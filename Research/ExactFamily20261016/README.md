# Zero-slack families and the decision contract (2026-10-16)

Reply to Outcasts63/64. This is reanalysis of known discovery inputs and a small restriction test, not a new ESC verification range or independent population validation. Character orthogonality, cyclotomic fields, and Carmichael exponents are standard; no priority is claimed for those tools or the elementary classification below.

## Paper derivation: a finite guaranteed-exact subfamily

Let k=au>0, m=4k, and L=lambda(m), the exponent of the unit group. The signed conjugate pair chi(-1)(F_chi+F_conj(chi)) is real in Q(zeta_L). If L is in {1,2,3,4,6}, this field's real subfield is Q. Its reduced polynomial is therefore constant, so each pair's L1 lower bound is exact and eta=0 for every input factorization. This is a sufficient condition, not a necessary condition on k for the actual data to have eta=0.

The standard prime-power formula for lambda, together with CRT, gives:

- lambda(4k)|4 iff 4k|240 iff k|60. Odd primes allowed are3,5, to exponent1; the2-power in4k is at most16.
- lambda(4k)|6 iff 4k|504 iff k|126. Odd primes allowed are3 to exponent<=2 and7 to exponent1; the2-power is at most8.

Since lambda(4k) is even, the condition L in {1,2,3,4,6} is precisely the union of these cases. Thus

E={1,2,3,4,5,6,7,9,10,12,14,15,18,20,21,30,42,60,63,126}.

There are81 ordered coprime pairs (a,u) with au in E: sum over E of2^omega(k), including the one pair at k=1. Beyond budget126, raising the budget adds no candidate of this guaranteed-exact kind. Actual eta=0 outside E can still depend on the factors of ap+u. This finite family is NOT a finite list of polynomial denominator formulae, because the target divisors remain variable; the known polynomial-cover obstruction does not immediately disprove its existence candidate.

Source for the exponent definition and prime-power/LCM formula: [Sage reference, carmichael_lambda](https://doc.sagemath.org/html/en/reference/rings_standard/sage/arith/misc.html#sage.arith.misc.carmichael_lambda). The20-product consequence is derived here from that formula, not asserted by the reference. The existing divisor criterion remains a reused known tool (Outcasts13).

## Executed checks

Contract was saved before these calculations. Fixed ten discovery inputs, same as61/62; 610 complete log-budget pairs. The reviewed CRT/cyclotomic helper recomputed the exact factor certificates, checked their values against prior saved fields, and independently checked W by bounded residue DP. The observation in63 matches:33 positive certificate rows,32 with eta=0. Of the32,31 are in E, and one is outside E: p1740481,(a,u)=(1,13),L12,W1,eta0. The unique positive certificate with positive slack is p53722321,(13,1),L12,W1,eta5/6,c1/6. Thus E, actual eta=0, and positive eta must be measured separately.

The426 E rows among610 include31 successful rows. Every one of the10 log boxes has at least one E witness. Separately, all81 E pairs were checked for each fixed input,810 rows in total. Factors were product-checked and prime-tested by direct division; all divisors were compared by factor construction, direct integer division, and bounded residue DP. Both H_Elog and H_E from the contract remain UNPROVED; all10 fixed inputs pass. This is not evidence for a universal guarantee beyond that finite set.

The126 unit-group-exponent comparisons are finite implementation checks only. The exclusion of k>126 from E follows from the prime-power derivation, not from scanning up to126.

Initial run: one CPU process on mini,2.897seconds. The self-contained bundle was rerun in0.435seconds, exit0; all result fields except timing and source-path hashes matched. No new Lean, full build, CI, Monte Carlo, or5625-prime computation was executed. Existing179468-prime Hlog coverage is unchanged. All input data are already-used discovery inputs.

## Suggested decision rules for the proposed5625 reanalysis

These are suggestions, not a claim the other participant has accepted or run them. Publish/freeze the exact input-list hash and pre-analysis source commit. The cohort and W values have already been used, so call it a prespecified reanalysis/implementation audit, not new holdout evidence. Keep integer counts and denominators as well as proportions.

1. Cert=0 and Wtot>0: refutes universality of this particular L1 certificate in this box; inspect missed W-positive rows and which conjugate terms create slack. Exact full orbits recover W but do not explain existence. Seek a useful strict lower bound using partial bundles and actual exponent caps.
2. Cert=0 and Wtot=0: after complete divisor and input validation, this refutes Hlog for that prime/box, not ESC or unrestricted TypeII existence. Stop the log-bound proof route; consider a p-dependent larger budget or retaining TypeI as well.
3. Cert0=0, Certplus>0, even if rare: immediately refutes an eta-zero-only log-box existence strengthening. Retain positive-slack candidates; a uniform proof cannot discard the exceptional p because its frequency is below1%.
4. Cert0>0 mostly: split it into E and the factor-dependent eta-zero family. Finite success does not prove either family covers all p. Refuting H_Elog need not refute H_E; a failed full81-pair family would refute H_E and require leaving E.
5. G3 frequencies change: more quadratic obstruction motivates a pointwise argument against simultaneous square-coset failure across moving a,u; more remaining group obstruction motivates keeping nonquadratic2-power conditions/even-H cases; more actual exponent shortage motivates target-directed factor-block products with original exponents. These are different missing lemmas, not iid/random-factor assumptions. A frequency outside a heuristic band is not an arithmetic inconsistency and does not refute a universal statement by itself.

In particular, passing G1>=99% and G2<=1% cannot justify treating the remaining1% as solved or irrelevant. For existential strengthenings one genuine counterexample decides; success proportions describe this reused cohort only.

## Replay

Python3 standard library, from a fresh copy of this directory:

`python3 check-exact-family-20261016.py`

The script writes the four exact-family JSON outputs in its own directory. `integer_helper.py` is the reviewed old file unchanged (guarded main is not called on import). `character_helper.py` is the reviewed definition prefix, with only run/helper paths made local; no old top-level research loop executes. `baseline-log-rows.json` preserves just the610 old numeric fields used for comparison. `provenance.json` identifies the original full files and both executions. Old absolute paths in historical helper constants are provenance and unused by this replay's mathematical functions.

This directory does not certify participant63's machine timings, Windows Lean runs, or every file in their24-file audit. Their public README and contract at6f20c006d9582bb0ef760584bf5db730c69f60a9 were read; the counts above were recomputed from our own earlier inputs and code.
