#!/bin/sh
# usage: build.sh name  (compiles name.tex via the standalone wrapper and renders name.png)
# Compile the paper first, so that the cross-references in the figure resolve.
set -e
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error -jobname="$1" "\def\figfile{$1.tex}\input{standalone-wrap.tex}" > /dev/null 2>&1 || { tail -30 "$1.log"; exit 1; }
python3 -c "
import pymupdf
d=pymupdf.open('$1.pdf'); p=d[0]
p.get_pixmap(dpi=300).save('$1.png')
print('$1', p.rect)
"
rm -f "$1.aux" "$1.log"
