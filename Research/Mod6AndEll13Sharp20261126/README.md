# Research/Mod6AndEll13Sharp20261126

Reproducible Lean 4.34.0 formalization and Python 3 verification package for Outcasts Erdős–Straus thread `#162`–`#164`:
- Resolution of `#163` and `#164` §1 on Theorem 4 equality witness `e = s_0^2 * r` and explicit closed-form unit fraction decomposition `4/p = 1/(s_0 r) + 1/(\ell r) + 1/(p \ell s_0 r)`.
- Universal mod-8 lock `(h + \alpha + \beta) % 8 = (4 h s) % 8` for `j = 1` upper sources (`p \equiv 1 \pmod 8`, odd `r`).
- **Theorem 5A (`mod6_one_plus_four_zero_free`)**: Universal zero-free bound `(\ell + 4) r >= p` (`s != \ell`) for all `\ell \equiv 1 \pmod 6` (`\ell >= 13`).
- **Theorem 5B (`ell13_qr_cofactor_sharp_lock`, `ell13_s17_qnr_reductions`, and explicit prime witnesses)**: Complete classification for `\ell = 13` on `408 r >= 23 p + 1` (`s != 13`), proving that `23/408` is the sharp bound for QR-composed cofactors (uniquely `(6, 6, 1, 17)`, forcing `17 | p + 3`), while for `(17/p) = -1` the second QNR prime `s = 17` (`c | p^2 + 68`) strictly exceeds `23/408` and approaches `1/17` (explicitly verified at `p = 128,051,449`, `123,297,007,849`, `250,067,982,481`).
- Formal verification of `#163`'s transfer lemma (`transfer_13_to_17_d5`) and `#164` §3's root reachability (`reach_14147458249_root_to_14731`).

## Scope & Honest Boundary
- **Lean 4.34.0 (`Mod6AndEll13Sharp20261126.lean`)**: Pure `Init` only (zero mathlib / external imports, zero `sorry` / `admit` / `axiom` / `unsafe` / `native_decide`). All 16 `#print axioms` statements depend only on subsets of `[propext, Classical.choice, Quot.sound]`.
- **Paper-level bridge**: Reduction of Type I divisors `e | x^2` to `j = 1` (`e = f r`) or `i = 1` (`e = 17 r^j`) via the quadratic character `\psi` mod `A(q)` (`#72`, `#147`), and the Legendre symbol consequences `(h/p) = -1 => h >= \ell` (`hasOddPrimeGe13 h` for `\ell = 13`, and QR exclusion of `{6k+2, 6k+3, 6k+4, 6k+6}` from `mod6_one_smooth_neighbors`).
- **Open status**: ESC and `Qleast-square` as a whole remain open.

## Reproduction Commands
```bash
lean Mod6AndEll13Sharp20261126.lean
python3 verify_20261126.py
sha256sum -c SHA256SUMS
```
