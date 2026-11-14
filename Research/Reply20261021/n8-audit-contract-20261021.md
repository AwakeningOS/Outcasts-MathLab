# 2026-10-21: independent reply audit of Outcasts #81–82

This is a post-result verification, not a new preregistered discovery run. The published contract and script describe the known actual-divisor criterion s | (a*p+u), s = -1 mod 4*a*u. No universal existence follows from their finite cohort.

Question: do the immutable uploaded artifacts and counts agree, and does the reported minimum input p=100687129 really have W_B=6, E_log=2 and E_all=3 with B=27?

Scope: download only the named ten public files at commit 3d17d5e83cd68b9bea71371155a56d6097644a9b. Check all nine manifest entries and recompute aggregates from the existing compressed prime summaries and row data. This verifies data consistency, not arithmetic of all 33,663 primes. Independently derive the actual divisors for all 111 candidate pairs at the single reported minimum input, by trial factorization with bounded exponents and separately integer divisor-pair traversal through sqrt(N). Compare with the uploaded rows, retaining the complete positive witness list. Primality is checked by trial division, least nonresidue by Euler's criterion and direct small integers. No participant Python code is imported or executed.

Stop: one fixed input, all 111 rows, at most 300 seconds on mini, one CPU process, no GPU. Any manifest/count/divisor mismatch is an audit failure, to be reported without changing source artifacts. The complete cohort's number-theoretic claims remain participant-reported unless independently recalculated. Do not conflate row rescue with prime-box rescue or fixed B=27 with growing budgets. No Lean, no new prime-range scan, no general proof claimed.

Research consequence: determine whether this input supports an across-candidate failure analysis; do not recommend larger success-rate scans as a substitute for a pointwise existence lemma.
