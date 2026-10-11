import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Tactic.NormNum.LegendreSymbol

/-!
# The quadratic-residue obstruction in Dahan's divisor normal form

This module formalizes a KNOWN obstruction; it is not a new result.
The obstruction goes back to Schinzel and Yamamoto (1965) and appears as
Elsholtz–Tao, arXiv:1107.1010, Proposition 1.6 (no Type I/II solutions for
odd squares). Here it is restated for the Type II criterion in the normal form
of Dahan, arXiv:2608.24035, Theorem 3.9(ii): a witness is a divisor `s` of
`a p + u` with `s ≡ -1 (mod 4 a u)`.

Main statements:
* `witness_jacobi_eq_neg_one`: every witness satisfies `J(p | s) = -1`.
* `no_witness_of_square`: a perfect square has no witness at all.
* `no_witness_of_mod_eq_one`: `p ≡ 1 (mod s)` rules out the divisor `s`.
* `finite_witnesses_miss_infinitely_many_primes`: no finite list of witnesses
  `(a, u, s)` covers all primes (via Dirichlet's theorem in Mathlib).

None of these is an existence statement for the Erdős–Straus equation.
-/

namespace OutcastsMathLab.Research.JacobiObstruction

/-- Dahan v1 Theorem 3.9(ii): `s ∣ a p + u` and `s ≡ -1 (mod 4 a u)`.
    Same shape as `DivisorWitness` in the witness-budget research modules. -/
def DivisorWitness (p a u s : ℕ) : Prop :=
  s ∣ a * p + u ∧ 4 * a * u ∣ s + 1

/-- If `s ≡ -1 (mod 4 a)` with `a > 0`, then `J(a | s) = 1`. -/
theorem jacobi_eq_one_of_dvd_succ :
    ∀ (a s : ℕ), 0 < a → 4 * a ∣ s + 1 → jacobiSym a s = 1 := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro s ha hs
    have h4 : 4 ∣ s + 1 := dvd_trans (Dvd.intro a rfl) hs
    have hs4 : s % 4 = 3 := by omega
    have hsodd : Odd s := Nat.odd_iff.mpr (by omega)
    rcases Nat.even_or_odd a with ⟨b, rfl⟩ | hodd
    · have hb : 0 < b := by omega
      have h8 : 8 ∣ s + 1 := dvd_trans ⟨b, by ring⟩ hs
 …2466 tokens truncated…ℤ) := by push_cast; rfl
  rw [hr] at h
  have hlt : p % 11 < 11 := Nat.mod_lt _ (by norm_num)
  generalize p % 11 = r at h hlt ⊢
  interval_cases r <;> first | omega | (norm_num at h)

/-- Non-vacuity: `p = 1009` (hard class `169 mod 840`, `1009 ≡ 8 mod 11`) has the witness
`s = 11` at `(a, u) = (1, 3)`. -/
theorem witness_1009_eleven : DivisorWitness 1009 1 3 11 := by
  unfold DivisorWitness
  norm_num

#print axioms jacobi_eq_one_of_dvd_succ
#print axioms witness_jacobi_eq_neg_one
#print axioms no_witness_of_square
#print axioms no_witness_of_mod_eq_one
#print axioms finite_witnesses_miss_infinitely_many_primes
#print axioms witness_409
#print axioms exists_prime_dvd_jacobiSym_eq_neg_one
#print axioms witness_has_nonresidue_prime_factor
#print axioms no_smooth_witness
#print axioms witness_prime_factor_nonsquare
#print axioms witness_eleven_nonresidue
#print axioms witness_1009_eleven

end OutcastsMathLab.Research.JacobiObstruction
