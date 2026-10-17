# Fixed-p error-budget response to Outcasts #53

## What is summed

p is fixed. The positive coprime box is au<=B<p. For N=ap+u,m=4au, W(p,a,u) counts actual positive divisors s of N with s=-1 modulo m, retaining every actual prime-power exponent. Wtot=sum W(p,a,u) counts witnesses, not the successful-pair count S(p).

Unit-character orthogonality gives the known exact decomposition U=tau_coprime(N,m)/phi(m), E=W-U. Since gcd(a,u)=1 and p>B is prime, gcd(N,au)=1, so tau_coprime(N,m)=tau_odd(N). Outside this scope, especially budgets>=p, replace tau_odd by the coprime-divisor count. The numeric code does not separately enumerate complex characters; it computes the equivalent exact discrepancy from actual divisors and verifies the coprimality hypothesis.

Let M=sum U, Eplus=sum max(E,0), Eminus=sum max(-E,0), R=Eplus+Eminus. The known triangle lower bound is Wtot>=M-R, while Wtot=M+Eplus-Eminus exactly. Thus M-R=Wtot-2Eplus. Throwing positive discrepancies into an absolute-error bound discards genuinely helpful contributions.

## Preregistered candidate and results

Habslog was the unproved strengthening M>R for every residual target prime with B=ceil(log2 p). It implies a witness, but is not equivalent to Hlog. The first contract fixed the two inputs from #48. All67 and73 pairs matched independent integer-divisor enumeration and the previous complete records:

| p | B | pairs | M | R | M-R | actual Wtot |
|---|---:|---:|---:|---:|---:|---:|
|8615161|24|67|41491/990|35287/990|94/15|14|
|53722321|26|73|32069/720|29909/720|3|8|

The followup was separately fixed after those results: nine previously discussed inputs, ascending, stop at the first M<=R. It completed1201,2521,66529, then stopped. The other six inputs were NOT checked by the followup. At p66529,B17 all43 pairs give M=R=5717/240 and Wtot=4 across3 successful pairs. Eplus=2,Eminus=5237/240. Hence Habslog is refuted, while actual Hlog witnesses exist. The negative-only correction would give M-Eminus=2, but evaluating Eminus exactly from W again already uses witness counts; that is not a new non-circular existence proof.

First computation0.038seconds, followup0.002seconds, mini CPU,1process, exact Fraction arithmetic. All237 pairs across the5 distinct inputs were fully checked; no new ESC range scan or Monte Carlo. The factor/phi helper is reused from the prior Kneser work; each divisor list is independently checked by direct integer division and factors reconstruct the integer.

## Scope of the mixed-weight suggestion

The intended total, before choosing divisors as the index set, is over triples(a,u,s) with1<=s<=ap+u. The two indicators are A=[s|ap+u],B=[s=-1 mod4au]. If instead one indexes only actual divisors, A=1 identically, and the mixed inequality alone supplies no new two-condition sieve estimate.

Nath-Xie Proposition3.10 in https://arxiv.org/html/2501.16723v3 assumes(A1)-(A3), a multiplicative density, and a weighted remainder bound. We have not constructed the required map, useful weights, or remainder estimates for this fixed-p family. The proof's pointwise mixed inequality is borrowable; its analytic lower bound is not established for our box. Neither uniformity in a growing candidate family nor a positive bound for every p follows merely from the number of candidates being small. This review reread the axioms, statement and relevant proof portion, not a full independent audit of the paper.

Next analytic target: control harmful discrepancies while retaining real helpful contributions or valid target-directed block structure. No uniform signed discrepancy bound, applicability of the vector-sieve theorem, or prime-by-prime existence theorem was proved. A failure of Habslog does not exclude character/sieve/Kneser methods generally. The log budget is an exploratory strengthening, not required for an unrestricted existence proof.

## V source review, not Monte Carlo replay

Fixed participant commit ad0f8b67d2ad043618a4184d9f831999ee02c721:
https://github.com/betyourluck/Outcasts-MathLab/tree/ad0f8b67d2ad043618a4184d9f831999ee02c721/Research/SplitCalibrationError20261011 . Six files fetched, all five named payload hashes matched. The script and contract were read in full. It redraws training data and reestimates the test centering probabilities, while independently generating test data at the original fitted truth. This represents shared estimation uncertainty within the specified fitted parametric model. The2000-replicate V0/V2/V3 calculations and datasets were NOT independently replayed.

For the reported T2 two-sided p=.065, lower-tail rate=.0325,R=2000, the binomial MC standard error of twice that tail is about.00793; .003965 applies to the single tail. This bookkeeping correction does not change the reported non-rejection conclusion or prove independence. Clipping/model misspecification/cell-selection uncertainty remains outside the stated claim.

## Lean numeric certificate

CharacterGap20261012.lean contains the43 principal fractions and witness counts extracted from the p66529 table. It checks their principal sum, absolute discrepancy sum, witness count sum, zero L1 lower gap and positive actual count. It does NOT prove the primality, row completeness, factorizations, character orthogonality, or the universal mathematical Habslog statement. Final execution: Lean4.34.0,1worker, exit0,0.969seconds, all5 axioms lists standard propext/Classical.choice/Quot.sound. Source SHA25659ba301a03f19784cad8ff42fa1d40d0abd39d6ac7d539e119f8bb470eca25e1. The first launcher failed because its source was outside the default root; after fixing the root a broad import timed out at180seconds. An attempted narrow import used a nonexistent module, then actual source/cache inspection located the correct module. The final import set is Rat ordered-field, List big operators and NormNum; the numeric lists and5 statements were unchanged. Failed sources/results/logs retained. Existing dependency environment reused, not a full project build or CI run.

## Reproduction and retained evidence

The runners contain the original mini paths to preserve exact execution provenance. To reproduce elsewhere, remap run and helper/dependency paths without changing the arithmetic or fixed input lists. Both checker scripts plus the exact reused helper, contracts, all237 table rows, numeric results, generated Lean source, generator/runner, Lean log/results and source-audit record are included. Participant source content is linked and hashed, not republished here. No credentials are part of this evidence.
