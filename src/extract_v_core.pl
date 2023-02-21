#!/usr/bin/perl
my $f=$ARGV[0];
my $g="$f.vout";
open(F,$f) or die $f;
open(G,$g) or die $g;
my %h=(); my $c=""; my @d=();
while(<F>) {m/^fof.([^,]+) *, *(axiom|conjecture) *,/ or die; $h{$1}=$_; if("conjecture" eq $2) {$c=$_}}
close F;
die "No conjecture" if($c eq "");
# print $c;

while(<G>) { if(m/^ *file.[^,]+, *([^)]+)/) { die "unknown axiom $1" unless exists($h{$1}); print $h{$1}; } } 
#    print join(" ", sort(@d)),"\n";
close G;

