# Fixed-p error budget check, preregistered 2026-10-12

Question from Outcasts #53: whether an exact fixed-p divisor-character main term admits a useful positive lower bound without relying on cancellation across candidate pairs. This is not a test of ESC coverage.

Known ingredients: finite unit-character orthogonality gives W(p,a,u)=tau_coprime(ap+u,4au)/phi(4au)+E(p,a,u), with actual prime-power exponents. In the positive coprime box au<=B<p for prime p, gcd(ap+u,au)=1, so tau_coprime equals tau_odd. Triangle inequality yields Wtotal>=M-R where M=sum tau_odd/phi and R=sum |E|. These identities are known; their derivation is not a new existence result.

Candidate to test (unproved strengthening, not equivalent to Hlog): Habslog asserts M>R for every target prime in the coprime box B=ceil(log2 p). If true it would suffice for a witness, but it may discard useful cancellation. Testing it identifies whether a uniform no-cancellation bound is a viable immediate route, not whether all pointwise/character/sieve methods fail.

Inputs fixed before computation: p=8615161 and p=53722321, both raised in the prior replies. Compute both full boxes (67,73 pairs) as requested diagnostics; stop on any implementation mismatch, otherwise evaluate Habslog separately for both. No other primes, no range enlargement or Monte Carlo.

For each pair compute W by integer division through sqrt(M), tau_odd by the same divisors and separately by a reviewed exact factorization routine, phi by trial factorization. Verify all factors reconstruct M, p is prime by exact trial division, and every M is coprime to au. Use Fraction throughout. Compare W and witness lists against yesterday's full140-row record but do not infer new primality proofs from that record.

Outputs: M,R,Eplus,Eminus,Wtotal,Wtotal/M; complete per-pair principal/error table; M-R certificate verdict. If M<=R, retain the actual Wtotal to distinguish failure of Habslog from failure of Hlog. Do not claim M+E=W implies the missing uniform bound. Also save independent-training bootstrap source audit as a source-level review, not a replay of the participant's 2000-replicate computation.

Resource and stopping limit: mini CPU, one process,60seconds for this arithmetic. No GPU, no subprocess agents. Any source or divisor mismatch stops; no changing the inputs or candidate after seeing the result. A subsequent Lean file may verify only the resulting fixed rational inequalities, not all factorizations, character orthogonality, or general prime existence.
