import Erdos1183.LatticeCerts

/-!
# Definitions for the size colourings of `2^{[19]}`

A colouring of the subsets of `[19]` that depends only on the size is a word
`g 0, g 1, …, g 19`. A *gadget* is a sublattice of a cube `2^{[t]}`, written as a list of bit
masks; placed on the levels `d, …, d + t` above an initial segment and completed by a chain on
the other levels of its colour, it beats the chain by the number of its members minus the number
of levels of its colour among `d, …, d + t` (`gain`). The kernel checks a binary tree of prefixes
of words whose leaves name one gadget for each colour with gains adding up to at least `2`.
-/

namespace Erdos1183.W20

/-- The number of the bits `0, …, 19` of `x` that are set. -/
def pc20 (x : ℕ) : ℕ := (List.range 20).countP fun i => x.testBit i

/-- A sublattice of `2^{[t]}`: `cnt` distinct masks, every member size `p` with bit `p` of `lm`
set. -/
structure Gadget where
  t : ℕ
  lm : ℕ
  cnt : ℕ
  masks : List ℕ

/-- The properties of a gadget checked by the kernel. -/
def Gadget.ok (G : Gadget) : Bool :=
  decide (G.t ≤ 19) && closedB G.masks && decide G.masks.Nodup && decide (G.cnt = G.masks.length) &&
    G.masks.all fun a => decide (a < 2 ^ G.t) && G.lm.testBit (pc20 a)

/-- Gadgets in a binary tree, looked up by the bits of the index, lowest bit first. -/
inductive GTree
  | nil
  | leaf (G : Gadget)
  | node (l r : GTree)

/-- Look up an index. -/
def GTree.get : GTree → ℕ → Option Gadget
  | .nil, _ => none
  | .leaf G, _ => some G
  | .node l r, i => if i % 2 = 0 then l.get (i / 2) else r.get (i / 2)

/-- Every gadget of the tree is `ok`. -/
def GTree.allOk : GTree → Bool
  | .nil => true
  | .leaf G => G.ok
  | .node l r => l.allOk && r.allOk

/-- The levels `v < L` of colour `c` in the prefix `w` of length `L` (bit `v` of `w` is `g v`). -/
def cmask (w L : ℕ) (c : Bool) : ℕ := if c then w else w ^^^ (2 ^ L - 1)

/-- The gain of the gadget `G` on the levels `d, …, d + t` in colour `c`, or `0` if it does not
fit into the prefix or one of its levels has the other colour. -/
def gain (G : Gadget) (d w L : ℕ) (c : Bool) : ℕ :=
  if d + G.t + 1 ≤ L ∧ (G.lm <<< d) &&& cmask w L c = G.lm <<< d then
    G.cnt - pc20 ((cmask w L c >>> d) &&& (2 ^ (G.t + 1) - 1))
  else 0

/-- The gain of the gadget with index `j` (none for `j = 0`). -/
def resGain (T : GTree) (j d w L : ℕ) (c : Bool) : ℕ :=
  if j = 0 then 0 else
    match T.get j with
    | some G => gain G d w L c
    | none => 0

/-- A leaf code names a red gadget and its position and a blue gadget and its position. -/
def leafOK (T : GTree) (x w L : ℕ) : Bool :=
  decide (2 ≤ resGain T (x % 1024) ((x >>> 10) % 32) w L true +
    resGain T ((x >>> 15) % 1024) ((x >>> 25) % 32) w L false)

/-- Read a preorder description of a tree of prefixes, starting at the prefix `w` of length `L`;
return the rest of the list. -/
def walk (T : GTree) : ℕ → ℕ → ℕ → List ℕ → Option (List ℕ)
  | 0, _, _, _ => none
  | _ + 1, _, _, [] => none
  | f + 1, w, L, x :: xs =>
    if x = 0 then
      if L < 20 then
        match walk T f w (L + 1) xs with
        | none => none
        | some r => walk T f (w + 2 ^ L) (L + 1) r
      else none
    else if leafOK T (x - 1) w L then some xs else none

end Erdos1183.W20
