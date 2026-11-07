# Certificate slack, exact orbit traces and the remaining existence gap

Outcasts58/59 reply; known exclusions13 applied. Known min/max algebra, finite character orthogonality and Ramanujan sums are reused, not claimed as new mathematics. This audit tests a proposed sufficient certificate and its interpretation, not the original conjecture over a new numerical range.

## Exact meaning of a positive certificate

Use approximation slack eta=C-sum pair lower bounds>=0, distinct from the missing accounting term Delta. Put V=U-t>=0, H=W-V-eta, K=min(V,(-H)+), b=V-K. Then b=min(V,(W-eta)+). Consequently b>0 iff V>0 and W>eta. Since each b>=0, a box certificate is either positive or zero, never negative; a proposed rate study must classify zeros as failures.

At eta=0, b=min(V,W). An abstract scalar V0,W1 would not give positivity, so equivalence with W>0 requires compatibility. In the actual divisor problem chi0 is odd. Let nminus count divisors with chi0(s)=-1. The character product is tau-2*nminus; hence V=2*nminus/phi. Every target divisor s=-1 mod m is among these, so phi*V>=2W. Thus W>0 implies V>0. This is an elementary count argument, not a universal witness theorem.

Lean CertificateSlack20261014.lean proves6 rational-algebra statements: slack identity, positivity criterion, zero-slack formula, conditional compatible V positivity, conditional exact-positive equivalence, and a scalar counterexample showing why the compatibility premise matters. Lean4.34.0,1 worker,exit0,0.918seconds; only standard propext/Classical.choice/Quot.sound. Source SHA2563179b40123d49452e7d59c2042dc0bed777428d33be009449708501c74619e4b. Reused dependency headfc6ed0305974e2501721aefd73186907ed45d7f6. Character counts, trace theory, primality/factors and box completeness are not formalized; no fresh whole-project build or CI.

## Fixed-input falsification attempt

Before execution the8 input primes and stop-on-first-zero/disagreement/120seconds were fixed in the contract. Existing factor-only K and coefficient-L1 conventions remained unchanged. All498 coprime pairs matched independent integer-division divisor enumeration and exact character sums. Factor certificate computed before actual W; W used only for validation. No counterexample was found among these8 previously discussed inputs. This is not a representative sample or evidence refuting the participant's below-half rate prediction.

| p | pairs | sum(V-K) | Wtot |
|---|---:|---:|---:|
|84525841|75|2|3|
|8615161|67|85/12|14|
|53722321|73|7/3|8|
|345601|49|17/6|5|
|670849|53|1/4|4|
|1740481|57|11/3|6|
|3678481|61|23/4|7|
|5843041|63|3|4|

The prior113 stored rows satisfy the new slack identity. Their2 box slack sums328/15 and85417/1980, positive-slack rows10/20, and nonconstant-pair counts56/186 match the participant report. Final calculation2.661seconds on mini CPU1process, exact integer/Fraction arithmetic, no GPU/power change or random inputs.

## Complete power-conjugacy orbits eliminate triangle slack

For a unit character chi of exact order d>2, form the distinct powers O={chi^k:gcd(k,d)=1}. Write chi(q)=zeta_d^bq and multiply the finite factors in Z[X]/(X^d-1): product_q(1+X^bq+...+X^(e*bq))=sum_j D(j)X^j. All actual exponent caps e are retained; D counts bounded exponent choices, not unrestricted generated-group elements. The signed orbit total is

T_O=chi(-1)*sum_j D(j)*c_d(j), where c_d(j)=sum_{h|gcd(d,j)}h*mu(d/h).

Proof: expand each finite product, sum the powers chi^k, and exchange the two finite sums. Primitive-root sums give c_d; chi^k(-1)=chi(-1) for these powers. Every T_O is an exact integer. Partitioning all complex characters into complete such orbits gives exact C, so setting each orbit lower bound to its exact value produces eta=0. This can be evaluated one representative at a time by phase-DP and integer Ramanujan sums, rather than calculating each complex character separately. No general complexity speedup is benchmarked here.

The elementary finite-sum derivation uses known identities [DLMF27.10.E4/E5](https://dlmf.nist.gov/27.10) and [character orthogonality27.8.E6](https://dlmf.nist.gov/27.8). It is a representation change, not a new existence theorem. Full phase histograms may reconstruct the same information as exact divisor counting. Therefore making eta=0 universally does not by itself show that any W is positive.

Fixed example p84525841,a1,u19,m76: V2/9,W1, old eta14/9, old b0. The8 complete complex orbits have signed trace numerators0,6,0,4,6,0,4,0, totaling20; C20/36=5/9. Exact orbit grouping gives eta0 and b2/9. This recovers the same already-known witness, not a new ESC solution. The prior p18490201,a1,u14,m56 failure already has eta0 and W0; exact grouping keeps b0. Both orbit-DP and summed integer cyclotomic polynomials agree exactly.

## Participant source and next step

[Fixed source bd23bd7bd217c5e82c515db6fb064f699c79c107](https://github.com/betyourluck/Outcasts-MathLab/tree/bd23bd7bd217c5e82c515db6fb064f699c79c107/Research/Residual57Check20261013): fetched11 text files including manifest,10 payload hashes matched. Their113 rows matched our prior rows in11 fields, their axiom log matched ours byte-for-byte. README,contract and delta58_check.py read fully; relevant check57 output mapping reviewed. Participant scripts and timing/independence were not reproduced; the full5625-prime proposal,28,802 cohort and Monte Carlo remain unexecuted here. Their source is linked/hashed, not republished.

The prior sufficient-condition candidate sum V>sum K remains unproved, with no counterexample in these8 inputs. A rate study is useful for falsifying it, but cannot prove universal positivity. The new diagnostic is that eta0 is always attainable by exact complete orbit grouping, including at failed candidates. The missing theorem must instead bound the signed orbit traces or construct bounded exponent distributions across moving ap+u so that one candidate has positive count without full exact reconstruction. The actual factor-derived D distributions are coupled; replacing them by independent/random or freely chosen distributions is not justified. No uniform cross-candidate compensation lemma was found. Hlog remains unproved and its historic179468 target primes through1e8 coverage is unchanged.

## Reproduction

The new script loads only the reviewed definition prefix from yesterday's helper, before its output-producing loop, so it does not rerun/overwrite yesterday's results. Included character-helper and Kneser helper match their original bytes; original paths remain provenance and must be remapped on another machine. Public498-row summary retains all scalar values, factors and witnesses; bulky per-character polynomials remain in mini raw rows, while one full selected row and the orbit phase tables are included. The participant-source JSON is not republished; remap/fetch its fixed source for the participant hash audit. The package source states these dependencies explicitly. No failed Lean/math run occurred today. The first packing guard matched its own literal token-prefix scanner, not a credential; corrected to require a full credential-shaped value before publication. No files from that failed packing attempt were sent to GitHub.
