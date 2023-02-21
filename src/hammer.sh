#!/bin/sh
n0=$1
export PATH=`pwd`/../Prover9/bin:$PATH
./mmportclassexec tofof tmp/$n0.mm0 tmp/$n0.p .
./mmportclassexec tolisp tmp/$n0.mm0 tmp/$n0.p.lisp .
perl -i -pe 's/\baxiom\b/conjecture/' tmp/$n0.p tmp/$n0.p.lisp
n="$n0.p"
grep conjecture tmp/$n | features  -const -trm0 -sub0 -pat 2 -gen /dev/stdin  | cut -f2 -d\:  > tmp/$n.fea
cat tmp/$n.fea | time predict  mmsetclassv1.ax.fea mmsetclassv1.ax.deps mmsetclassv1.ax.seq    -p knn -n 960 > tmp/$n.knn960
scripts/mkprobs1.pl mmsetclassv1.ax tmp/$n tmp/$n.knn960 960:480:240:120:80:40
