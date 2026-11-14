# PR6 review contract, 2026-10-06

Input fixed before execution: PR6 head fc6ed0305974e2501721aefd73186907ed45d7f6; p=345601,670849; all 53 pairs of its explicit box per p. No new prime interval. This is an independent response to new Outcasts #29, not novel existence research.

Known from literature: Dahan v1 Thm3.9(ii), Lem4.2, finite-exponent limitation; Elsholtz–Tao v6 Prop1.6. Unknown to this reviewer: whether submitted Lean statements/specs agree, build under fixed dependencies, and finite negative certificate factors agree with independent full divisor enumeration. Statistical atlas percentages/correlations cannot be reproduced from this PR's certificate generator alone; those claims need source/row data/model definitions.

Methods: exact deterministic integer trial factorization, full exponent expansion, independent integer divisor traversal through sqrt(M), compare both sorted full divisor sets and committed Lean factor certificates for EVERY106 rows. Separately compute finite unit subgroup H and H*G² solely to classify failures, never as divisor existence. This retains all prime multiplicities.

Success: all certificates/factors/divisor sets match, all106 negatives hold, Lean build/all declared theorem axioms pass and agree with specs. Failure: stop on any mismatch, unallowed axiom, compilation error; retain failure logs. Arithmetic deadline180s, build900s, axiom check180s. One process on mini HDD, 8 CPU affinity for Lean, no GPU, no randomness. No statistical independence or pointwise existence claim follows.
