#!/bin/sh
n0=$1
build/mmportclassexec tofof tmp/$n0.mm0 tmp/$n0.p .
build/mmportclassexec tolisp tmp/$n0.mm0 tmp/$n0.p.lisp .
perl -i -pe 's/\baxiom\b/conjecture/' tmp/$n0.p tmp/$n0.p.lisp
n="$n0.p"
grep conjecture tmp/$n | bin/features  -const -trm0 -sub0 -pat 2 -gen /dev/stdin \
  | cut -f2 -d\:  > tmp/$n.fea
time bin/predict \
  build/mmsetclassv1.ax.fea build/mmsetclassv1.ax.deps build/mmsetclassv1.ax.seq \
  -p knn -n 960 < tmp/$n.fea > tmp/$n.knn960
src/mkprobs1.pl build/mmsetclassv1.ax tmp/$n tmp/$n.knn960 960:480:240:120:80:40
