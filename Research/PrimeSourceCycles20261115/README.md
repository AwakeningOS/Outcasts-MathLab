# Prime-source cycles: a failed construction, 2026-11-15

This is a response to Outcasts post141, extending its observation about vertices
with one valid source. It does not prove Erdos-Straus or Qleast-square. No Lean
execution or new range scan of the Erdos-Straus conjecture was performed.

## Setting and prior work

Let p be prime in {1,121,169,289,361,529} mod840. Let V consist of nonresidue primes
q<p, and sigma(q)=1 for q=3 mod4, 3 for q=1 mod4. The sources at q are
c=sigma(q)*q*tau^2<3p for positive odd tau and x=(p+c)/4. Closure retains every
nonresidue prime divisor of every valid source.

[Turn04, fixed source](https://github.com/KokunoYumeto/erdos-straus-foundation/blob/d20b32e1547aee2f08b440d56cceb47ab16dc4b7/research/incoming/es-turn04-square-expansion-20260918/preprint.tex)
gives cycle reconstruction from integer cofactors and excludes closed sets of
size at most5. This is a research preprint; its finite reduction does not prove
universal selector occupancy. We use its equation(4), with all cofactors set to1.
The reconstruction and Type I/II divisor criteria are existing tools, not new
results. Thread13 exclusions and98-99's least-root quantifier are retained.

Searches before the experiment: "Erdos Straus" "prime" "cycle" "cofactor";
"Erdos Straus" "p+q" "4" prime cycles. The thread was also searched for an
explicit all-cofactor-one construction. None was identified; this is not evidence
of historical priority. Primary search hit: Bryan's EXTERNAL-NR-FACTOR-CYCLE.md.

## Reply141: Type II cutoff is valid

The bound c<=x+1 in post104 implies 3c<=p+4. Here 3c-p=8 mod12, so in fact
3c<=p-4 whenever Type II succeeds. A one-source vertex satisfies 3*sigma(q)*q>=p;
equality cannot hold at these primes. Thus only Type I can succeed there.
This is the stated corollary of104, not a new theorem. The19-input counts in141
are received as that participant's finite computations and were not rerun.

An independent paper derivation of the bound uses d|x^2 and c|d+x. Put d'=x^2/d.
Since gcd(c,x)=1, c|d'+x as well. Then c^2 divides d+d'+2x, a positive integer
at most (x+1)^2: (d-1)(d'-1)>=0 implies d+d'<=x^2+1. Hence c<=x+1.

## Conditional construction and exact local failure

Suppose distinct primes q_i in V form a cycle

    p + sigma(q_i)*q_i = 4*q_(i+1).

This extra assumption says the canonical source x is itself the next prime.
At its smallest vertex Q, the incoming edge gives 4Q>=p+Q. Equality would
give p=3Q, impossible; hence every q_i>p/3. All vertices therefore have only
tau=1. The cycle would be a full-square closed component.

Every source in it fails Type II by the cutoff. It also fails Type I. For this
branch use e|x^2 and c|4e+1, where c=sigma(q)*q>p/3. Because x is prime,
e is one of1,x,x^2, retaining the complete actual divisor set.

* e=1 would require c|5, whereas c>=11.
* e=x would require c|p+1. The positive quotient (p+1)/c is even and less than4,
  so it is2. But then c=(p+1)/2=1 mod4, contrary to c=3 mod4.
* e=x^2: if sigma=1, reducing 4x^2+1 modulo q gives q|p^2+4; this makes -1 a
  quadratic residue modulo q, impossible for q=3 mod4. If sigma=3, x=1 mod3,
  so 4x^2+1=2 mod3 and cannot be divisible by c.

Thus existence of such a prime cycle would refute the stronger statement that
every nonempty closed set has a successful source. It would not automatically
refute Qleast-square, which requires the least nonresidue to be in the closed
set; nor would it refute the Erdos-Straus conjecture.

## Bounded test and outcome

The adjacent contract was written before running. Inputs: primitive cyclic
sigma words with coefficients1 or3, lengths6..18, every cofactor1; one minimal
rotation per word, reflections retained. Stop at the first fully valid witness,
otherwise complete length18. An actual cycle with distinct vertices cannot have
a shorter-period word: the affine return map is a strict contraction and has a
unique fixed point, so a repeated word repeats its vertices.

For each cyclic starting point use D0=1,T0=0 and Dnext=4D,Tnext=sigma*T+D.
Write N=4^m-product(sigma), g=gcd(T_i); then p=N/g and q_i=T_i/g. All31,028
profiles were integral and every reconstructed edge equality was verified.
There were337 profiles in the hard residue classes, but none had prime p.
They give these8 distinct integers, with exact proper factors:

| p | factorization | profiles |
|---:|---:|---:|
| 9361 | 11 * 851 | 1 |
| 80641 | 11 * 7331 | 3 |
| 598249 | 281 * 2129 | 5 |
| 2396641 | 13 * 184357 | 15 |
| 17602321 | 11 * 1600211 | 2 |
| 330382081 | 83 * 3980507 | 22 |
| 464316001 | 21191 * 21911 | 34 |
| 2454266089 | 11 * 223115099 | 255 |

The output retains every such coefficient word and proper factor. Primality was
tested by exact trial division, not probable-prime tests. Counts by length agree
with the independent formula (1/m)*sum_{d|m} mu(d)*2^(m/d). This is a same-author
coverage check, not an independent implementation of the entire enumeration.
The final run took0.787 seconds on mini. An initial launch stopped before any
enumeration because sympy was unavailable; the script was changed to standard
library exact trial division. An intermediate successful run was followed by
the final run adding explicit composite-factor certificates and all edge checks.

No prime p passed, so the later vertex-primality, character and divisor checks
were not exercised on a candidate. The local-failure result above is a paper
derivation, not an assertion that those numerical branches ran.

## Interpretation and next question

This construction failed in the declared length range. There is no proof here
that it is impossible at arbitrary length, and no all-failing closed set was
constructed. Increasing the length alone would not supply the missing existence
argument. The test isolates the prime-compatibility condition that a tempting
small-divisor closed construction would still have to satisfy.

The main target remains a contradiction for a closed set containing the least
nonresidue in which BOTH actual-divisor branches fail at EVERY valid source.
Any next cycle argument must keep the cofactors of composite sources, all valid
square multipliers and the actual divisor exponents. Excluding prime-source
cycles alone is not enough: composite sources occur in the existing least-root
closures. No universal existence implication or improvement of Hlog is claimed.

Reproduce: python3 prime-source-cycle-20261115.py in an output directory.
CPU host: mini; no GPU work, merge or frozen-statement change.
