#!/bin/bash
# clean4.sh: clean build + axiom check + three-kernel Comparator of the cleaned q-colorability-palomar package.
set -uo pipefail
export PATH=$HOME/.elan/bin:$PATH
P=~/th/scratch/CLEAN4/pkg; L=~/th/scratch/CLEAN4/logs; mkdir -p $L; cd $P
S=$L/summary.txt; : > $S
echo "start $(date -u +%FT%TZ)" >> $S
echo "project objects before: $(find . -name '*.olean' -not -path './.lake/packages/*' | wc -l)" >> $S
echo "toolchain: $(cat lean-toolchain); lean: $(lean --version)" >> $S
( time lake exe cache get ) > $L/cache-get.log 2>&1; echo "cache-get exit $?" >> $S
( time lake --no-cache build ) > $L/build.log 2>&1; rc=$?; echo "build exit $rc" >> $S
grep -E "^(real|Build completed)|error" $L/build.log | tail -5 >> $S
echo "project modules compiled: $(find .lake/build/lib/lean -name '*.olean' | wc -l)" >> $S
printf 'import Solution\n#print axioms ThresholdChallenge.main\n' > $L/Axioms.lean
lake env lean $L/Axioms.lean > $L/axioms.log 2>&1; echo "axioms exit $?: $(tr '\n' ' ' < $L/axioms.log)" >> $S
python3 scripts/run_comparator.py --package . --report verification --label comparator > $L/comparator-run.log 2>&1; echo "comparator exit $?" >> $S
grep -E "kernel accepts|Your solution is okay|VERDICT" $L/comparator-run.log >> $S
echo "DONE $(date -u +%FT%TZ)" >> $S
