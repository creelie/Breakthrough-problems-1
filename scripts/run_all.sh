#!/usr/bin/env bash
# run_all.sh -- every check outside Lean; outputs go to build/.
#   C:      regtour.c lists the regular tournaments on d = 3, 5, 7, 9 vertices with N+(0) = {1..m} and
#           must reproduce data/classes*.txt (one line per characteristic polynomial of S)
#   Python: wormald_hessian.py computes H from Wormald's definition in exact arithmetic and compares it
#           with Theorem 1.1; spectral_bounds.py checks Theorem 1.5 and the circulant remark;
#           check_paper.py recomputes every number printed in preprint/main.tex (needs mpmath, numpy)
#   GP:     wormald.gp is an independent PARI/GP check of Theorem 1.1 and of the closed form for R_d
#   Figures: gen_figures.py must reproduce preprint/figures/*.tex exactly
# Needs a C compiler, Python 3 with numpy and mpmath, and PARI/GP.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
B="$ROOT/build"
PY="$ROOT/verification/python"
mkdir -p "$B"
cd "$ROOT"
CLASSES="data/classes3.txt data/classes5.txt data/classes7.txt data/classes9.txt"

echo "== C: regular tournaments on at most 9 vertices"
cc -O2 -Wall -Wextra -Werror -o "$B/regtour" verification/c/regtour.c
for d in 3 5 7 9; do
  "$B/regtour" "$d" > "$B/classes$d.txt"
  cmp "$B/classes$d.txt" "data/classes$d.txt"
  head -1 "$B/classes$d.txt"
done

echo "== Python: H from Wormald's definition against Theorem 1.1"
python3 -I "$PY/wormald_hessian.py" $CLASSES | tee "$B/wormald_hessian.txt"

echo "== Python: full Hessian matrix and exact nondegeneracy bounds"
python3 "$PY/hessian_matrix_bounds.py" | tee "$B/hessian_matrix_bounds.txt"

echo "== Python: Theorem 1.5 and the circulant remark"
python3 -I "$PY/spectral_bounds.py" $CLASSES | tee "$B/spectral_bounds.txt"

echo "== Python: every number in the paper"
python3 -I "$PY/check_paper.py" preprint/main.tex data | tee "$B/check_paper.txt"

echo "== PARI/GP: independent check"
gp -q verification/gp/wormald.gp | tee "$B/wormald_gp.txt"
grep -q '^failures 0$' "$B/wormald_gp.txt"

echo "== the figure sources are the generator's output"
mkdir -p "$B/figures"
cp preprint/figures/blowup.tex preprint/figures/convergence.tex "$B/figures/"
python3 -I scripts/gen_figures.py
cmp preprint/figures/blowup.tex "$B/figures/blowup.tex"
cmp preprint/figures/convergence.tex "$B/figures/convergence.tex"
echo "all checks passed"
