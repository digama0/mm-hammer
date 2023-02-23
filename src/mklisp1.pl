#!/usr/bin/perl
# create lisp spec from problems
# mklisp1.pl build/set.mm.ax.lisp tmp/_0dif.p.lisp tmp/_0dif.p.prem240.small tmp/_0dif.p.prem480.small ...
my $axfile=shift;
my $conjfile=shift;


#    (axiom "ax_mp" (! "Xph" (! "Xps" (=> (p "Xph") (=> (p ("cwi" "Xph" "Xps")) (p "Xps"))))))
my %h=();
open(F,$axfile) or die "axfile not found";
while(<F>) {m/^.axiom *"([^," ]+)" */ or die; $h{'a' . $1 . '_thm'}=$_}
close F;

my $conj="";
my $cn="";
open(F,$conjfile) or die "conjfile not found";
$_=<F>;
m/^.conjecture *"([^," ]+)" */ or die;
$conj=$_; $cn= 'a' . $1 . '_thm';
close F;

while(my $pfile=shift)
{
    open(F,$pfile) or die "problem file not found";
    open(G,">$pfile.lisp") or die "$pfile.lisp not writable";
    while(<F>)
    {
        m/^fof.([^, ]+) *, *(axiom|conjecture) *,/ or die;
        # print $_;
        if("axiom" eq $2) { die "axiom not found $1 at $pfile" unless exists $h{$1}; print G $h{$1} }
        elsif("conjecture" eq $2) { die unless ($1 eq $cn); print G $conj }
        else {die $_}
    }
    close F;
    close G;
}
