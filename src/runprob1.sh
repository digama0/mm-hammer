#!/bin/bash
TL=$1
n=$2;
m=`echo -n $n | perl -pe 's/\.prem\d+$//'`
export PATH=`pwd`/../Prover9/bin:$PATH
vampire_z3_rel_static_HEAD_6295 --mode portfolio -sched ltb_default_2017 -t $TL --sine_selection axioms --proof tptp --output_axiom_names on $n > $n.vout
if grep -q Theorem $n.vout; then
  scripts/extract_v_core.pl $n > $n.small;
  tptp_to_ladr < $n.small > $n.small.p9
  prover9 -t 60 -f $n.small.p9 > $n.small.p9.out
  if grep -q PROOF $n.small.p9.out; then
    prooftrans ivy < $n.small.p9.out  > $n.ivy
    scripts/mklisp1.pl mmsetclassv2lisp.ax $m.lisp $n.small
  else echo "Vampire succeeded but Prover9 failed on $n, not reconstructing"
  fi
else echo "Vampire failed on $n, not reconstructing"
fi