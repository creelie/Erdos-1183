#!/bin/sh
# usage: build.sh name  (compiles name.tex via the standalone wrapper and renders name.png)
set -e
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error -jobname="$1" "\def\figfile{$1.tex}\input{standalone-wrap.tex}" > "/tmp/claude-0/-home-claude-erdos-1183/631a8b93-4210-5f02-9119-87f75df17812/scratchpad/$1.log" 2>&1 || { tail -30 "/tmp/claude-0/-home-claude-erdos-1183/631a8b93-4210-5f02-9119-87f75df17812/scratchpad/$1.log"; exit 1; }
python3 -c "
import pymupdf,sys
d=pymupdf.open('$1.pdf'); p=d[0]
p.get_pixmap(dpi=300).save('$1.png')
print('$1', p.rect)
"
rm -f "$1.aux" "$1.log"
