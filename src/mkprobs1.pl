#!/usr/bin/perl
# create problems from refs
# mkprobs1.pl build/setmm.ax tmp/_0dif.p tmp/_0dif.p.knn960 "960:480:240:120:80:40"
my $axfile=$ARGV[0];
my $conjfile=$ARGV[1];
my $reffile=$ARGV[2];
my $slices=$ARGV[3];

sub min { my ($x,$y) = @_; ($x <= $y)? $x : $y }
sub max { my ($x,$y) = @_; ($x <= $y)? $y : $x }

my %h=();
open(F,$axfile) or die "axfile not found";
while(<F>) {m/^fof.([^,]+) *,/ or die; $h{$1}=$_}
close F;

my $conj = "";
open(F,$conjfile) or die "conjfile not found";
while(<F>)
{   # m/^fof.([^,]+) *, *conjecture *,/ or die;
    $conj = $conj . $_
}
close F;

open(G,$reffile) or die "no reffile found";
my $r=<G>;
my @r=split(/ +/,$r);
close G;
my $maxr=$#r;


$slices=~m/^\d+(:\d+)*$/ or die "slices should be e.g., 960:480:240:120:80:40";
@slices=split(/:/,$slices);
for my $s (@slices)
{
    open(H,">$conjfile.prem$s") or die;
    for my $i (@r[0 .. min($s-1,$maxr)])
    {
        die "nonexistent premise $i" unless exists $h{$i};
        print H $h{$i};
    }
    print H $conj;
    close H;
}
