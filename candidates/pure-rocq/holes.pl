#!/usr/bin/env perl
# Hole search for Rocq build files (used by pure-rocq/check.sh and
# wasmcert-coq/decoder/check.sh).  Usage: perl holes.pl FILE.v...
# Prints each finding as FILE:LINE: text and exits 1 if there is any.
# This is a second line of defence: the semantic guards (Print Assumptions,
# rocqchk's context summary) are the first.  It rejects, anywhere in the file
# (comments included, so it errs on the side of a false alarm):
#   - words that leave a hole or declare an assumption: Admitted, admit,
#     admitted, Axiom(s), Parameter(s), Conjecture(s), Abort, Primitive,
#     bypass_check, Admit Obligations, Typing Flags, Declare ML Module, Load;
#   - any Unset other than the two harmless ones used here
#     (Unset Strict Implicit, Unset Printing Implicit Defensive), so
#     Unset Guard/Positivity/Universe Checking, with or without Local/Global/
#     #[...] and split across lines, is rejected;
# and, in the code with comments removed, Hypothesis/Hypotheses/Variable/
# Variables/Context outside every Section (at top level, or inside a Module
# only, they are axioms; inside a Section they become premises, which the
# statement checks see).
use strict; use warnings;
my $bad = 0;
sub report { my ($f, $txt, $pos, $what) = @_;
  my $line = 1 + (substr($txt, 0, $pos) =~ tr/\n//);
  print "$f:$line: $what\n"; $bad = 1; }
for my $f (@ARGV) {
  open(my $h, '<', $f) or die "cannot read $f\n"; local $/; my $raw = <$h>; close $h;
  while ($raw =~ /\b(Admitted|admit|admitted|Axioms?|Parameters?|Conjectures?|Abort|Primitive|bypass_check)\b/g) {
    report($f, $raw, $-[0], "forbidden word '$1'"); }
  while ($raw =~ /\b(Admit\s+Obligations|Typing\s+Flags|Declare\s+ML\s+Module|Load)\b/g) {
    report($f, $raw, $-[0], "forbidden command '$1'"); }
  while ($raw =~ /\bUnset\b(\s+[A-Za-z]+){0,3}/g) {
    my ($p, $s) = ($-[0], $&); my $n = $s; $n =~ s/\s+/ /g;
    next if $n =~ /^Unset (Strict Implicit|Printing Implicit Defensive)$/;
    report($f, $raw, $p, "forbidden '$n'"); }
  # remove (nested) comments, keeping newlines so line numbers stay right
  my $code = ''; my $depth = 0; my $i = 0; my $L = length $raw;
  while ($i < $L) {
    my $two = substr($raw, $i, 2);
    if ($two eq '(*') { $depth++; $code .= '  '; $i += 2; next; }
    if ($two eq '*)' && $depth > 0) { $depth--; $code .= '  '; $i += 2; next; }
    my $c = substr($raw, $i, 1);
    $code .= ($depth > 0 && $c ne "\n") ? ' ' : $c; $i++;
  }
  my @stack;   # 'S name' for a Section, 'M name' for a Module / Module Type
  while ($code =~ /(?<![\w'.])(Section|Module(?:\s+Type)?|End|Hypothes[ie]s|Hypothesis|Variables?|Context)\b(?:\s+(?:Import\s+|Export\s+)?([A-Za-z_][\w']*))?([^.]*\.)?/g) {
    my ($kw, $name, $rest, $p) = ($1, $2 // '', $3 // '', $-[0]);
    if ($kw eq 'Section') { push @stack, "S $name"; }
    elsif ($kw =~ /^Module/) { push @stack, "M $name" unless $rest =~ /:=/; }
    elsif ($kw eq 'End') {
      my $k = -1; for my $j (reverse 0..$#stack) { if ((split ' ', $stack[$j])[1] eq $name) { $k = $j; last; } }
      splice(@stack, $k) if $k >= 0; }
    else { report($f, $code, $p, "'$kw' outside any Section (an axiom)") unless grep { /^S / } @stack; }
  }
}
exit $bad;
