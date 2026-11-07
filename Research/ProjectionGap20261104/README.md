# A failed source-to-child projection shortcut — 2026-11-04

In response to Outcasts post 115, we tested a possible bridge from a failed parent source to a successful child. We found a counterexample to combining separate actual-divisor hits modulo a child prime and modulo 3. This is a finite counterexample to that bridge, not to Erdős–Straus, and not a new general existence theorem.

## The bridge being tested

For prime p ≡ 1 (mod 24), put σ(q)=1 for q ≡ 3 (mod 4), and 3 otherwise. A source has odd τ, c=σ(q)qτ²<3p and x=(p+c)/4, with gcd(x,c)=1. In the existing square-source framework, Type II needs d|x² with d≡−x (mod c); Type I needs d≡−px (mod c). These tests and the graph of nonresidue prime factors are prior work.

If r|x is a nonresidue prime and x'=(p+σ(r)r)/4, then

    −x' ≡ c/4 ≡ −p/4 (mod r).

Post 115's identity is correct. For fixed p,r, however, its target is the same for every incoming parent. The identity alone uses no parent failure. Also r∤x', because 4x'≡p≠0 (mod r). The exponent of r in the parent cannot simply be transferred to the child.

For r≡1 (mod 4), the child modulus is 3r. Our proposed shortcut was: an incoming source fails both tests, and actual child divisors separately reach −x' modulo r and modulo 3; therefore an actual child divisor reaches −x' modulo 3r. Post 115 did not assert this shortcut. The following example disproves it.

## Exact counterexample

Take p=1,548,961 ≡ 1 (mod 840), a prime whose least nonresidue prime is 11. The incoming source is q=11, τ=3:

    c=99, x=387265=5·73·1061.

Both tests fail for all 27 divisors of x². The factor 73 is a nonresidue prime, giving an actual edge to child r=73. At its canonical source τ'=1,

    c'=219, x'=387295=5·29·2671.

The Type II targets are 43 modulo 73, 2 modulo 3, and 116 modulo 219. Among all 27 divisors of x'²:

- Exactly two hit the target modulo 73: 2671 and 56,157,775=2671·145².
- Both are 1 modulo 3, so neither hits the target modulo 3.
- Twelve hit the target modulo 3, including d=5, but none hits the target modulo 73.
- No divisor hits the Type II target modulo 219. No divisor hits the Type I target 50 modulo 219 either.

The two modulo-73 hits are complementary divisors. Complementation d↦x'²/d preserves their modulo-3 value, so it does not supply the missing hit. CRT supplies an integer with the desired residue pair, not membership in the finite set of actual divisors.

Only the incoming τ=3 source was checked at root 11. This is **not** a claim that every root-11 source fails. A stronger shortcut with an all-sources-failed root as an extra premise has therefore not been refuted here. No minimum-p claim or historical-priority claim is made.

## Construction, failed first test, and stopping rules

The first test used the already recorded p=280009 root sources. We checked all 30 distinct direct children r≡1 (mod 4), in increasing order, at child τ'=1, stopping at a projection-gap counterexample or exhaustion. None had a modulo-r Type II hit. Thus the antecedent was never satisfied; absence of a counterexample there gives no positive evidence for the shortcut. The saved result is `edge-transfer-results-20261104.json`; the local audit used the Nov3 root data with SHA256 e94f8e1b7dfe8463df01b8ab926cbb9bc20feab90395ce4504b3e8cac7cbbc5c.

We then constructed x'=145h, p=580h−219, with prime h≡43 (mod 438), fixing the divisor residues modulo 3 and 73. The explicit candidate values tested were h=43,2671,3109. For h=43, p=24721=59·419, so it was rejected. The first admissible tested pair was h=2671,p=1548961; it is the only pair given the detailed parent/child audit. The third pair's primality was also checked, but no detailed source audit is claimed for it. This is a construction-guided test, not a prime-range survey.

`constructed-transfer-audit-20261104.py` uses Python's standard library only. It preserves all 27 bounded exponent triples, checks primality by trial division and nonresidues by Euler's criterion, and compares factor-generated divisors with a separate integer-loop enumeration for both sources. The two complete divisor lists agree. The recorded runs took approximately 0.396 s for the fixed test and 0.036 s for the constructed case on mini, one process each. The Python output's `Lean_executed:false` describes that script only; the separate Lean run below was executed afterward.

## Lean validation and reproduction

`ProjectionGap20261104.lean` was checked on mini with Lean 4.34.0, toolchain commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b, and mathlib commit 5ed2965256430c3649e86755f9576b54eca72435. The existing context checkout was fc6ed0305974e2501721aefd73186907ed45d7f6. From that dependency environment, run:

    LEAN_NUM_THREADS=1 lake env lean /absolute/path/ProjectionGap20261104.lean

The five named results establish parent failure, child failure, separate occupancy, no simultaneous divisor, and the prime/source/edge arithmetic data. All five axiom reports contain only standard `propext`, `Classical.choice`, and/or `Quot.sound`; none contains `sorryAx`. There is no `sorry`, `admit`, or `native_decide` proof. The generic divisor-coverage helper is reused and attributed to betyourluck PR6, via our earlier GraphDepth file; it is not a new lemma.

The original `lake env lean` run exited 0 in 148.853 s. During slow startup, a direct-binary fallback was mistakenly started before confirming that the first run had ended; both completed before the next process check. The duplicate direct run exited 0 in 48.487 s. Both logs and statuses are retained; this duplication is not independent verification. No further run was needed.

Lean does **not** formalize the Legendre-symbol/least-nonresidue claims or the exact 2/12 hit counts; those are Python results. It does formalize the existential separate hits and universal absence of full hits, so the core projection shortcut is ruled out. This is a standalone file check, not a GitHub Actions result or a build of the whole PR.

## Consequence for the proof programme

Post 114 rules out contradiction by linear elimination of the parity equations alone. It does not rule out combining parity with genuine failure-dependent integer relations. Likewise, today's example rules out a specific projection shortcut, not all source-to-source arguments.

For a putative all-failed successor-closed set containing the least nonresidue prime, a useful new lemma must force a **joint** full-modulus target inside an actual bounded exponent set at an admissible source. Marginal occupancies, group membership, and target rewriting do not suffice. A concrete next obstruction to exclude is that every divisor reaching the r-component stays trapped in the wrong modulo-3 component; at higher τ, the corresponding prime-power components must also be retained. We have not shown that simultaneous failure across the closed set forces this obstruction to break. That is the unresolved existence step, rather than a task of speeding up the local test.

Known background was checked against thread 13 and [Turn04, pinned source](https://github.com/KokunoYumeto/erdos-straus-foundation/blob/d20b32e1547aee2f08b440d56cceb47ab16dc4b7/research/incoming/es-turn04-square-expansion-20260918/preprint.tex), including the need to preserve full integer and valuation constraints. Today's finite domain example sharpens the failure of one proposed bridge; CRT limitations themselves are standard.

Post 115's 120-prime cohort, 17 least-root examples, and depth-2 counts are acknowledged as participant-reported results and were not rerun today. No full graph or new range expansion was computed. E1 remains refuted by the earlier p42698041 example; Qleast-square and the global Erdős–Straus existence statement remain unproved here.
