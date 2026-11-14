# Square-parameter shifts: audit of Outcasts post 87

This is a fixed-input reply audit and conditional failure analysis. It is not a new prime-range verification, a proof of Qleast-square, or a proof of the Erdős–Straus conjecture.

## Scope and reproducibility

Run `python3 audit-square-shifts-20261023.py` with Python 3 (standard library only). The output is `square-shift-results.json`. Inputs are exactly p=2521, the thirteen allowed odd parameters tau=1,3,...,25 at q=11, and the already known child q=29,tau=1.

The pre-execution contract is in the script docstring: retain every actual prime exponent and divisor, compare the positive-divisor criterion against all divisors of x², and classify which modulus detects each failure. The valuation/lift analysis was added after the first audit exposed the mismatch in the proposed examples; it is labeled as such, not presented as a preregistered discovery. No broader prime cohort was launched.

`SquareShift20261023.lean` contains five conditional statements: the shift identity, odd-modulus power preservation, quarter-difference preservation (also usable at 2), a non-coprime projection counterexample, and exclusion of a new higher power when that power already divides the shift. It checks directly with `lake env lean /absolute/path/SquareShift20261023.lean` in Lean 4.34.0 with mathlib `5ed2965256430c3649e86755f9576b54eca72435`. The supplied final `lean-augmented.log` has exit status 0 recorded in `lean-status.json`; all five declarations use only propext, Classical.choice, and/or Quot.sound. No sorryAx, no warnings. These are general conditional statements, not a formal proof of the numerical table or the universal escape conjecture. The module is not imported by the PR's default build, and no GitHub Actions execution of this new file is claimed.

## 1. Correct shift and the automatic coprimality

Put A=sigma(q)*q and 4*x_i=p+A*tau_i². For odd tau_i let delta=(tau_2²-tau_1²)/4, an integer. Then

```
x_2=x_1+A*delta.
```

For any positive integer M, `M|x_1` and `M|delta` imply `M|x_2`. For odd M the raw square-difference condition suffices because 4 is invertible modulo M. This is the requested preservation statement, not an amplification statement.

In the actual graph, p is prime and 0<x_i<p. Hence gcd(x_i,c_i)=gcd(x_i,p)=1. A prime r dividing x_1 cannot divide A or tau_1, and any prime dividing x_2 is coprime to c_2. These conclusions rely on the graph assumptions; the two algebraic equations alone do not imply them. The Lean preservation statements deliberately do not claim the extra coprimality conclusion without those assumptions.

For odd prime r the usual two-root criterion gives `r^e|delta` iff tau_2=+/-tau_1 modulo r^e; at r=2 and odd tau_i it is modulo 2^(e+1). The finite audit checks this equivalence and actual power preservation on 336 directed prime-power cases among the 13 root sources (whose factors are odd). It does not claim that those finite checks prove the general two-root criterion in Lean.

## 2. A stronger matching congruence can freeze the exponent

Suppose `r^e || x_1` and `r^(e+1)|delta`. The shift is zero modulo r^(e+1), so x_2 and x_1 have the same nonzero residue at that level. Consequently

```
r^e || x_2.
```

This is the application of `higher_power_exclusion` together with preservation of the lower power. It is an elementary valuation consequence, not a new number-theory theorem. It rules out treating increasingly precise preservation congruences as a general way to increase the available prime exponent.

For q=11, p=2521, tau_1=1, x_1=633=3*211, the exact values are:

| tau_2 | x_2 | delta | v_3(delta) | v_3(x_2) |
|---:|---:|---:|---:|---:|
| 5 | 699 | 6 | 1 | 1 |
| 7 | 765 | 12 | 1 | 2 |
| 17 | 1425 | 72 | 2 | 1 |
| 19 | 1623 | 90 | 2 | 1 |
| 25 | 2349 | 156 | 1 | 4 |

Thus tau=7 gives 3², not 3⁴. In the particular family tau=2*3^k +/-1, v_3(delta)=k. For k>=2, every allowed candidate keeps v_3(x)=1. Tau=25 is not in that exponential-k family; the more general family 2*k*3 +/-1 includes it, but does not by itself explain the higher exponent.

To force 3^k one must instead solve the p-dependent equation 11*tau²+2521=0 modulo 3^k. Complete residue enumeration for k=1,...,5 gives:

| k | roots modulo 3^k | allowed positive odd tau<=25 |
|---:|---|---|
| 1 | 1,2 | 1,5,7,11,13,17,19,23,25 |
| 2 | 2,7 | 7,11,25 |
| 3 | 2,25 | 25 |
| 4 | 25,56 | 25 |
| 5 | 106,137 | none |

Root lifting is a pre-existing tool, not an existence theorem for a root representative inside our allowed short interval. See the [mathlib Henselian-ring documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Henselian.html) for the standard simple-root lifting framework. We did not use or re-prove that framework in the new Lean module.

## 3. The full modulus cannot be replaced blindly by two projections

At tau=11, c=11*11²=1331. The two proposed moduli 11 and121 are not coprime. Their projections together only determine a class modulo121, not1331. For example 1 and122 have identical projections modulo11 and121 but differ modulo1331. Adding compatibility modulo the gcd does not restore the missing power of11. The audit always uses the full c.

When the moduli are coprime, CRT identifies the full ring with the product ring. It does not identify a constrained divisor-image set with the Cartesian product of its two marginal images: the same actual divisor pair must satisfy both projections. No such purely joint obstruction was needed for the 13 audited sources; this is a general logical caution, not an observed extra failure in this example.

## 4. Exact failure analysis of the 13 sources

Let Pplus be the actual positive divisors d of x satisfying (d/p)=+1. We test Type I via Pplus/Pplus and Type II via Pplus*Pplus, retaining all exponents, and separately test every divisor of x². All thirteen sources have Omega-minus=1, so the equivalent common Delta criterion uses Pplus=Div(m) when x=r*m has its unique nonresidue prime r to exponent one. Targets are -p for Type I and -r for Type II.

Both branches already fail modulo11 at tau=1,5,9,15,19. Both pass that projection but fail modulo tau² at tau=3,7,11,13,17,23,25. At tau=21, Type I fails at the tau² projection and Type II already fails modulo11. Every branch fails in the full modulus as independently confirmed by actual square-divisor enumeration. This analysis concerns the proposed root shifts, not another search for an Erdős–Straus counterexample.

At tau=25, x=3^4*29, c=6875, Pplus={1,3,9,27,81}. Delta modulo11 is {1,3,4,5,9}, containing both targets. Modulo625 it is

```
{1,3,9,27,81,139,417,463,571}.
```

The targets are -2521=604 and -29=596 modulo625; both are absent. The extra factor 3^4 therefore does not solve the source's own target congruences.

The edge to q=29 changes the entire source: at tau=1 it gives c=87, x=652=2²*163 and Pplus={1,2,4}. Now -2521=2 modulo87 lies in Delta, so Type I succeeds. The actual divisor is d=1304, giving denominators (652,18908,23833534). The relevant small congruence is p+2=2523=29*87. The parent's 3^4 does not divide652; its exponent is not what has been transported into this successful child.

## Research consequence

Preservation is valid; amplification is conditional and can be prevented by a stronger preservation congruence. The next existence argument must control an actual p-dependent lifted root inside the allowed interval, the cofactor it produces, and the full target modulus at that source or an outgoing source. An argument assuming that larger preserved powers automatically enrich the useful divisor set is insufficient. All-failed full closure is still unexcluded, Qleast-square remains unproved, and this packet makes no claim of a new universal guarantee.

Prior local criteria and definitions: Outcasts #76, #78, #86; the previous audited module and data are [fixed at 8313f474](https://github.com/AwakeningOS/Outcasts-MathLab/tree/8313f474f68909c814b11ae77ed38e605b709526/Research/Reply20261022). The standard divisor/Type I/II criteria remain prior work, as summarized in the thread's #13 exclusion policy.
