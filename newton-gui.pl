#!/usr/bin/perl

use warnings;
use strict;

use Tk;

my $M = 250;
my $L = 2;
sub tk2math { ($_[0] - $M, $M - $_[1]) }
sub math2tk { ($_[0] + $M, $M - $_[1]) }

my $top = MainWindow->new();

my $c   = $top->Canvas(-width => 2*$M, -height => 2*$M);
my $a   = $top->Entry();
my $b   = $top->Entry();
$a->insert("0", "-50");
$b->insert("0", "150");
d($a->get, $b->get);
d($b->get, $a->get);

my $b1 = $top->Button(-text => "x", -command => sub {
    $c->delete("p");
    d($a->get, $b->get);
    d($b->get, $a->get);
});

my $b2 = $top->Button(-text => "y", -command => sub {
    $c->delete("p");
    d($a->get, $b->get);
    d($b->get, $a->get);
    for(my $x = -$M; $x <= $M; $x += 10) {
        for(my $y = -$M; $y <= $M; $y += 10) {
            eval { cb(undef,math2tk($x,$y)) };
        }
    }
});

$c->createGrid(math2tk(0,0), math2tk(20,-20));
$c->createLine(math2tk(-$M,0), math2tk($M,0));
$c->createLine(math2tk(0,-$M), math2tk(0,$M));
$c->createLine(math2tk(-$M,-$M), math2tk($M,$M));
$c->Tk::bind("<Button-1>", [ \&cb, Ev("x"), Ev("y") ]);

$c->grid(-column => 0, -row => 0, -columnspan => 2);
$a->grid(-column => 0, -row => 1);
$b->grid(-column => 1, -row => 1);
$b1->grid(-column => 0, -row => 2);
$b2->grid(-column => 1, -row => 2);

MainLoop();

sub cb {
    my ($x0,$y0) = @_[1,2];

    my @ps = newton($a->get,$b->get, tk2math($x0,$y0));
    $c->createLine(map { math2tk(@$_) } @ps);
    d(@$_) for @ps;

    my ($x,$y) = @{ $ps[-1] };
    my $n1 = sqrt(($x-$a->get)**2 + ($y-$b->get)**2);
    my $n2 = sqrt(($y-$a->get)**2 + ($x-$b->get)**2);

    d(@{ $ps[0] }, -fill => $n1 > $n2 ? "red" : "yellow");
}

sub d {
    my ($x,$y,@args) = @_;
    $c->createOval(math2tk($x-$L,$y-$L), math2tk($x+$L,$y+$L), -tags => ["p"], @args);
}

sub newton {
    my ($u0,$v0,$u,$v) = @_;
    my $a = -($u0 + $v0);
    my $b = $u0 * $v0;

    my @ps;
    push @ps, [$u,$v];

    for(1..20) {
        my $u_ = $u + ($b + $u**2 + $u*$a) / ($v-$u);
        my $v_ = $v - ($b + $v**2 + $v*$a) / ($v-$u);
        ($u,$v) = ($u_,$v_);
        push @ps, [$u,$v];
    }

    return @ps;
}
