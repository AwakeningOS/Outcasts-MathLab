# Independent audit of Outcasts N8 report (#81–82), 2026-10-21

The participant's immutable source is [betyourluck/Outcasts-MathLab at 3d17d5e83cd68b9bea71371155a56d6097644a9b](https://github.com/betyourluck/Outcasts-MathLab/tree/3d17d5e83cd68b9bea71371155a56d6097644a9b/Research/Holdout1e8Scan20261020).
This is a post-result audit, not a preregistered new discovery run. No participant Python code was imported or executed.

## What was checked

1. All nine SHA256SUMS entries match the downloaded immutable bytes. The public history has separate contract (b6bee9d), script (4bb51cc), and result (e93381c) commits. This is evidence about the public record, not independent observation of the author's execution or push times.
2. Existing uploaded data: all 33,663 prime records, 3,736,593 CSV rows and their candidate-set coverage were checked. Each input has the expected 75 budget pairs plus 36 unbudgeted E pairs. Summing the uploaded W and rational certificate values reproduces each prime summary. The list hash matches, all recorded inputs satisfy the range/residue/budget constraints, all recorded lower-bound inequalities hold, the minima are W_B=6, E_log=2, E_all=3, and rescue counts are 2,335/30,667 rows and zero previously-zero boxes. This is **data consistency**, not recomputation of all input primality, factorizations, characters or certificates, and not an independent proof that the cohort is complete.
3. Independent arithmetic at exactly one selected input, p=100687129: primality by trial division, least quadratic nonresidue 17, all actual divisors for all 111 pairs by both bounded-prime-exponent generation and separate integer divisor-pair traversal up to sqrt(N). The full divisor lists agree and all W values match the upload. All seven positive rows reconstruct positive denominators and satisfy the exact cleared-denominator identity. No floating-point equality is used.
4. For this input's 75 budget pairs, square-coset counts and generated subgroups were independently recalculated. Six rows succeed; the 69 failures comprise 60 quadratic obstructions, one further group obstruction and eight finite-exponent shortages. These classifications match the source summary.

## Complete positive witness rows at p=100687129

Each row has exactly one actual witness s dividing ap+u and congruent to -1 modulo 4au.

| a | u | s | In budget au <= 27 | In E |
|---:|---:|---:|:---:|:---:|
| 1 | 17 | 2188851 | yes | no |
| 2 | 5 | 839 | yes | yes |
| 3 | 2 | 119 | yes | yes |
| 11 | 1 | 615 | yes | no |
| 17 | 1 | 2719 | yes | no |
| 24 | 1 | 1832063 | yes | no |
| 3 | 14 | 76607 | no | yes |

Thus W_B=6, E_log=2, E_all=3 independently at this input. The source reports c_old=c_comb=3 for the box and c_mag=0 at (24,1); those certificate values were checked for consistency, **not independently recalculated from characters** in this audit.

## Reproduce

Use Python 3 standard library, in this directory:

```
python3 download-n8-20261021.py
timeout 300 python3 audit-n8-20261021.py
```

The download helper retrieves only the ten named public files from the immutable source commit, into `source/`. The audit stops on any assertion mismatch, retains all 111 independently computed rows, and writes a compact audit result. It never executes downloaded source. Execution here: mini, one CPU process, 20.32644882495515 seconds for the audit, no GPU. The input was selected after reading the participant's result, so this is not an independent holdout experiment. A later replay's wall time will differ.

## What remains open

The known Type-II divisor criterion and obstruction classification are not new results. This audit addresses an external verification request. H_Elog remains refuted at 38296729; H_E and Hlog remain unproved. The additional cohort is participant-reported finite evidence plus the consistency checks above, not a pointwise existence theorem. No Lean was run and no existing Lean theorem was changed.

The current research question remains whether simultaneous failure can be contradicted while retaining **the same p, actual finite exponents and all valid square-source transitions**. The canonical p=2521 seven-cycle already refutes a contradiction from only local exclusions or canonical t=1 closure. Frozen observed divisor-ratio sets cannot be transferred between primes. An additional prime interval or certificate accuracy gain would not resolve either obstacle. N8's contract itself selects R7: return to a pointwise existence lemma.
