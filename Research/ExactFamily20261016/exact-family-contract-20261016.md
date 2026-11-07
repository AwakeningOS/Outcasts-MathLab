# Contract: consequence of the zero-slack restriction (2026-10-16)

Question from Outcasts63/64: distinguish an implementation audit of known inputs from a new existence guarantee, and specify how a failed certificate changes the proof route.

Known: pairwise L1 certificate c=(W-eta)+; actual eta=0 gives c=W. Character orthogonality and Carmichael prime-power exponents are standard tools. This run does not claim a new character formula or a new ESC verification range.

New pointwise candidates to test (our strengthenings, not claims by63):
- H_Elog: every residual prime has an actual divisor witness at coprime positive a,u with au<=ceil(log2 p), and lambda(4au) in {1,2,3,4,6}.
- H_E: remove the log restriction from H_Elog but retain that exponent restriction.

Paper derivation before calculation: lambda(4k)|4 iff 4k|240 iff k|60; lambda(4k)|6 iff 4k|504 iff k|126. Thus the guaranteed-rational family E consists of exactly the20 divisors of60 or126. These implications use the standard prime-power exponent formula, not a bounded numerical search. They do NOT say eta=0 only in E: factors can make individual nonreal pairs rational outside E.

Inputs fixed before running: the ten previously used discovery inputs, sorted [66529,345601,670849,1740481,3678481,5843041,8615161,18490201,53722321,84525841]. This is reanalysis, not a held-out sample. No new primes, no5625 cohort, no MC.

Part1: independently recompute the pair certificates for all610 existing log-box rows using the previously reviewed exact CRT/cyclotomic implementation; compare W against saved actual-divisor rows and the bounded residue DP, compare all old numeric fields. Split zero eta into forced E and data-dependent outside E, including successful rows. Verify the33 positive/32 zero-slack observations, but stop on any mismatch, never force an expected value.

Part2: for each fixed prime, evaluate ALL coprime pairs with product in E, including products above log budget. Verify factors by product and prime tests; actual divisors by factor construction, direct integer division and bounded residue counts. Record every target divisor. H_Elog or H_E is refuted by one fixed prime with no successes in its full prescribed family. If none, mark only finite corroboration; do not expand input range to obtain a desired conclusion.

Stop on arithmetic or prior-data disagreement or90seconds elapsed. One CPU process on mini; no GPU, no Lean of known lemmas, no full build/CI. Preserve any failure. Report standard algebra as derived, finite checks as finite checks, and existence as unresolved unless counterexamples specifically refute one strengthening.
