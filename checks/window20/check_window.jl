# Independent check of a window certificate (Julia).
#
# The certificate file starts with "# m=<m> K=<K> band=<j1>,<j2>,..." and has one line per
# sublattice of 2^[m]: an integer k and the members as bit masks.  It certifies that every
# 2-colouring of the subsets of an m-element set has a red and a blue sublattice with at least
# K members in total, by the reduction of the paper: a mixed level outside the band settles
# the bound by the adjacent-set lemma; at a mixed band level k with an adjacent pair the two
# cubes beside the pair are coloured by size; every remaining pattern is settled by a listed
# sublattice (k = -1: moved to any position; k >= 0: placed around the pair at level k).
# Usage: julia check_window.jl certfile

function fail(msg)
    println("FAIL: ", msg)
    exit(1)
end

Pbound(j) = j < 0 ? 0 : (j >= 11 ? j + 2 : j + 1)

function subset_max!(T::Vector{Int16}, bits::Int)
    for i in 0:bits-1
        b = UInt64(1) << i
        for x in UInt64(0):UInt64(length(T) - 1)
            if x & b != 0
                v = T[(x ⊻ b) + 1]
                if v > T[x + 1]
                    T[x + 1] = v
                end
            end
        end
    end
end

function main(path)
    lines = readlines(path)
    hdr = lines[1]
    mm = match(r"m=(\d+)", hdr); kk = match(r"K=(\d+)", hdr); bb = match(r"band=([\d,]*)", hdr)
    (mm === nothing || kk === nothing) && fail("bad header")
    m = parse(Int, mm[1]); K = parse(Int, kk[1])
    band = bb === nothing || isempty(bb[1]) ? Int[] : [parse(Int, s) for s in split(bb[1], ",") if !isempty(s)]
    NB = length(band)
    bidx = Dict(j => i for (i, j) in enumerate(band))
    L = m + 1; NM = 1 << L
    for k in 1:m-1
        if !haskey(bidx, k) && Pbound(k - 1) + Pbound(m - k - 1) + 2 < K
            fail("level $k outside the band is not settled")
        end
    end
    for k in band
        (k + 1) + (m - k) + 2 < K && fail("cube reduction at level $k")
    end
    res = [zeros(Int16, NM) for _ in 0:NB]
    piv = Dict{Tuple{Int,Int},Vector{Int16}}()
    full = (UInt64(1) << m) - 1
    ncert = 0
    for ln in lines[2:end]
        (isempty(strip(ln)) || startswith(ln, "#")) && continue
        parts = split(ln)
        k = parse(Int, parts[1])
        X = [parse(UInt64, s) for s in parts[2:end]]
        ncert += 1
        S = Set(X)
        length(S) == length(X) || fail("repeated member")
        all(a -> a <= full, X) || fail("member out of range")
        for a in X, b in X
            ((a | b) in S && (a & b) in S) || fail("not a sublattice")
        end
        cnt = Int16(length(X))
        if k < 0
            top = UInt64(0); bot = full
            for a in X
                top |= a; bot &= a
            end
            t = count_ones(top & ~bot); base = count_ones(bot)
            rel = Dict{Int,Int}()
            for a in X
                r = count_ones(a) - base
                rel[r] = get(rel, r, 0) + 1
            end
            relmask = UInt64(0)
            for r in keys(rel)
                relmask |= UInt64(1) << r
            end
            for d in 0:m-t
                lm = relmask << d
                res[1][lm + 1] = max(res[1][lm + 1], cnt)
                for (i, j) in enumerate(band)
                    if get(rel, j - d, 0) == 1
                        key = lm & ~(UInt64(1) << j)
                        res[1 + i][key + 1] = max(res[1 + i][key + 1], cnt)
                    end
                end
            end
        else
            haskey(bidx, k) || fail("pivot outside the band")
            Sk = (UInt64(1) << k) - 1; lo = (UInt64(1) << (k - 1)) - 1; hi = (UInt64(1) << (k + 1)) - 1
            inside = Dict{Int,Bool}(); good = true
            for a in X
                j = count_ones(a)
                if j == k
                    a == Sk || (good = false)
                    continue
                end
                ins = j < k ? (a & ~lo) == 0 : (a & hi) == hi
                inside[j] = get(inside, j, true) && ins
            end
            good || continue
            strict = UInt64(0); flex = UInt64(0)
            for (j, ins) in inside
                if ins && haskey(bidx, j)
                    flex |= UInt64(1) << j
                else
                    strict |= UInt64(1) << j
                end
            end
            ki = bidx[k]
            for Mb in 0:(1 << NB)-1
                (Mb >> (ki - 1)) & 1 == 1 || continue
                Mm = UInt64(0)
                for i in 1:NB
                    (Mb >> (i - 1)) & 1 == 1 && (Mm |= UInt64(1) << band[i])
                end
                strict & Mm == 0 || continue
                T = get!(() -> zeros(Int16, NM), piv, (ki, Mb))
                key = strict | flex
                T[key + 1] = max(T[key + 1], cnt)
            end
        end
    end
    for T in res
        subset_max!(T, L)
    end
    for T in values(piv)
        subset_max!(T, L)
    end
    bandmask = UInt64(0)
    for j in band
        bandmask |= UInt64(1) << j
    end
    rest = [l for l in 0:L-1 if (bandmask >> l) & 1 == 0]
    nr = length(rest)
    configs = 0; via = 0; words = 0; least = typemax(Int)
    for st in 0:3^NB-1
        z = st; Radd = UInt64(0); Badd = UInt64(0); Mi = Int[]; Mb = 0
        for i in 1:NB
            s = z % 3; z ÷= 3
            if s == 0
                Radd |= UInt64(1) << band[i]
            elseif s == 1
                Badd |= UInt64(1) << band[i]
            else
                push!(Mi, i); Mb |= 1 << (i - 1)
            end
        end
        nm = length(Mi)
        for r in 0:(1 << nr)-1
            Rp = Radd; Bp = Badd
            for (i, l) in enumerate(rest)
                if (r >> (i - 1)) & 1 == 1
                    Rp |= UInt64(1) << l
                else
                    Bp |= UInt64(1) << l
                end
            end
            configs += 1
            bR = max(count_ones(Rp) + (nm > 0), Int(res[1][Rp + 1]))
            bB = max(count_ones(Bp) + (nm > 0), Int(res[1][Bp + 1]))
            for i in Mi
                bR = max(bR, Int(res[1 + i][Rp + 1])); bB = max(bB, Int(res[1 + i][Bp + 1]))
            end
            if bR + bB >= K
                least = min(least, bR + bB)
                continue
            end
            nm == 0 && fail("size colouring with pair $(bR + bB)")
            via += 1
            vr = Vector{Vector{Int}}(); vb = Vector{Vector{Int}}()
            for a in 1:nm
                i = Mi[a]
                oth = [band[Mi[b]] for b in 1:nm if b != a]
                T = get(piv, (i, Mb), nothing)
                xr = Int[]; xb = Int[]
                for e in 0:(1 << length(oth))-1
                    er = UInt64(0); eb = UInt64(0)
                    for (q, j) in enumerate(oth)
                        if (e >> (q - 1)) & 1 == 1
                            er |= UInt64(1) << j
                        else
                            eb |= UInt64(1) << j
                        end
                    end
                    push!(xr, T === nothing ? 0 : Int(T[(Rp | er) + 1]))
                    push!(xb, T === nothing ? 0 : Int(T[(Bp | eb) + 1]))
                end
                push!(vr, xr); push!(vb, xb)
            end
            for c in Iterators.product((1:length(v) for v in vr)...)
                R = bR; B = bB
                for a in 1:nm
                    R = max(R, vr[a][c[a]]); B = max(B, vb[a][c[a]])
                end
                words += 1
                R + B < K && fail("pattern with pair $(R + B)")
                least = min(least, R + B)
            end
        end
    end
    println("m=$m K=$K band=$(join(band, ",")): $ncert certificates, $configs patterns, $via settled by pivots, $words word choices, least pair $least")
    println("PASS: every 2-colouring of 2^[$m] has a red and a blue sublattice with at least $K members in total")
end

length(ARGS) == 1 || (println("usage: julia check_window.jl certfile"); exit(2))
main(ARGS[1])
