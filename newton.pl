#!/usr/bin/perl

use warnings;
use strict;

my $a = -($ARGV[0] + $ARGV[1]);
my $b = $ARGV[0] * $ARGV[1];

my ($u,$v) = ($ARGV[2], $ARGV[3]);
print "$u\t$v\n";

for(1..20) {
    my $u_ = $u + ($b + $u**2 + $u*$a) / ($v-$u);
    my $v_ = $v - ($b + $v**2 + $v*$a) / ($v-$u);
    ($u,$v) = ($u_,$v_);
    print "$u\t$v\n";
}
