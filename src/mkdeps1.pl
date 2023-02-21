#!/usr/bin/perl
# create deps for all files on input
while($_=shift)
{
    chomp;
    my $n=$_;
    open(G,$n) or die "File not found $n";
    my $c="";
    my %h=();
    while(<G>)
    {
        if (m/^fof.([ac]([^,]+)_(thm|conj)),conjecture,.*/) {$c= 'a' . $2 . '_thm';}
        elsif (m/^fof.(a[^,]*_(thm|ax)),axiom,.*/) { $h{$1}=(); }
    }
    die "no conjecture in $n" if($c eq "");
    print $c,':', join(" ", sort keys %h),"\n";
    close G;
}
