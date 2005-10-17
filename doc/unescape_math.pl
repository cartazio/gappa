#!/usr/bin/perl
use strict;
$^W=1; # turn warning on

my $line;
my $textmp = "./tmp.tex";
my $inmath = 0;
my $begin;

sub usage
{
    die <<"EndUsage";
usage: unescape_math.pl texfile

unescape_math.pl -- A program for unescaping TeX math in a TeX file
                    produced by openjade, which must be named on the
                    command line.

EndUsage
}

if (@ARGV == 0) { &usage; }
my $doc = $ARGV[0];

open (MAN, "<$doc") || die "Can't read $doc";
open (TMP, ">$textmp") || die "Can't write to $textmp";

sub unescape {
    $line =~ s/\\char92{}/\\/g;
    $line =~ s/\\char94{}/^/g;
    $line =~ s/\\char95{}/_/g;
    $line =~ s/\\{/{/g;
    $line =~ s/\\}/}/g;
    $line =~ s/\\&/&/g;
    $line =~ s/\\\$/\$/g;
}

while ($line = <MAN>) {
    $begin = 0;
    if ($line =~ /{}BEGINTEXLITERAL/) {
	$line =~ s/BEGINTEXLITERAL//;
        $inmath = 1;
	$begin = 1;
    }
    if ($inmath || $begin) {
	unescape();
    }
    if ($line =~ /ENDTEXLITERAL/) {
        if ($inmath) {
	    $line =~ s/ENDTEXLITERAL//;
	    $inmath = 0;
	}
    }    
    print TMP "$line";
}

close (MAN);
close (TMP);
system("cp $textmp $doc");
system("rm -f $textmp");
