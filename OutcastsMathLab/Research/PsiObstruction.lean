import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.Nat.Factorization.Induction

/-!
# The ψ-type obstruction forces `u` to be a residue

For a Dahan pair `(a, u)` at the prime `p`, let `ψ(q) = J(-(a u) | q)`.
The finite failure atlas (Outcasts P1) classified most failures as
"every odd prime factor `q` of `a p + u` lies in `ker ψ`". This module proves
the elementary consequence that was predicted and checked numerically (H2'):
if `p ≡ 1 (mod 8)` and the ψ-type obstruction holds, then `J(u | p) = 1`.
Contrapositively, a shift `u` with `J(u | p) = -1` can never fail by the
ψ-type obstruction.

This is a consequence of quadratic reciprocity, not a new theorem about the
Erdős–Straus equation; in particular it does NOT assert that a witness exists
when `J(u | p) = -1` (other characters, and exponent obstructions, remain).
-/

namespace OutcastsMathLab.Research.PsiObstruction

/-- If `J(p | q) = 1` for every odd prime factor `q` of `n ≠ 0`, then
    `J(p | m) = 1` for every odd divisor `m` of `n`. -/
theorem jacobi_eq_one_of_prime_factors (p n : ℕ) (hn : n ≠ 0)
    (h : ∀ q, q.Prime → q ∣ n → Odd q → jacobiSym p q = 1) :
    ∀ m, m ∣ n → Odd m → jacobiSym p m = 1 := by
  intro m
  induction m using Nat.recOnMul with
  | zero => intro h0 _; exact absurd (zero_dvd_iff.mp h0) hn
  | one => intro _ _; exact jacobiSym.one_right _
  | prime q hq => intro hqn hodd; exact h q hq hqn hodd
  | mul x y ihx ihy =>
    intro hxy hodd
    obtain ⟨hxo, hyo⟩ := Nat.odd_mul.mp hodd
    have hx0 : x ≠ 0 := by rintro rfl; simp at hxo
    have hy0 : y ≠ 0 := by rintro rfl; simp at hyo
    rw [jacobiSym.mul_right' _ hx0 hy0, ihx (dvd_trans (Dvd.intro y rfl) hxy) hxo,
      ihy (dvd_trans (Dvd.intro_left x rfl) hxy) hyo, one_mul]

/-- L2: if `p ≡ 1 (mod 8)` and every odd prime factor `q` of `a p + u` has
    `J(p | q) = 1`, then `J(u | p) = 1`. -/
theorem psi_obstruction_forces_residue {p a u : ℕ} (hp8 : p % 8 = 1) (hu : 0 < u)
    (h : ∀ q, q.Prime → q ∣ a * p + u → Odd q → jacobiSym p q = 1) :
    jacobiSym u p = 1 := by
  have hM : a * p + u ≠ 0 := by omega
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hM
  have hmdvd : m ∣ a * p + u := ⟨2 ^ k, by rw [hkm]; ring⟩
  have hJm := jacobi_eq_one_of_prime_factors p _ hM h m hmdvd hm
  have hp4 : p % 4 = 1 := by omega
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.quadratic_reciprocity_one_mod_four hp4 hm] at hJm
  have hmod : ((a * p + u : ℕ) : ℤ) % (p : ℤ) = (u : ℤ) % (p : ℤ) := by
    push_cast
    exact Int.modEq_iff_dvd.mpr ⟨-(a : ℤ), by ring⟩
  rw [← jacobiSym.mod_left' hmod, hkm]
  push_cast
  rw [jacobiSym.mul_left, jacobiSym.pow_left, jacobiSym.at_two hpodd, hJm,
    ZMod.χ₈_nat_eq_if_mod_eight]
  simp [hp8, show p % 2 = 1 by omega]

/-- For a prime `q ∣ a p + u` with `gcd(a, u) = 1`: `ψ(q) = J(-(a u) | q) = J(p | q)`. -/
theorem psi_eq_jacobi {p a u q : ℕ} (hq : q.Prime) (hcop : Nat.Coprime a u)
    (hdvd : q ∣ a * p + u) : jacobiSym (-((a : ℤ) * u)) q = jacobiSym p q := by
  have hqa : ¬ q ∣ a := by
    intro hqa
    have hqu : q ∣ u := (Nat.dvd_add_right (dvd_mul_of_dvd_left hqa p)).mp hdvd
    have h1 : q ∣ 1 := hcop ▸ Nat.dvd_gcd hqa hqu
    exact hq.one_lt.ne' (Nat.dvd_one.mp h1)
  have hgcd : Int.gcd (a : ℤ) q = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqa))
  have hmod : (-((a : ℤ) * u)) % (q : ℤ) = ((a : ℤ) ^ 2 * p) % (q : ℤ) := by
    have hd : (q : ℤ) ∣ (a : ℤ) * p + u := by exact_mod_cast hdvd
    exact Int.modEq_iff_dvd.mpr (by
      rw [show (a : ℤ) ^ 2 * p - -((a : ℤ) * u) = (a : ℤ) * ((a : ℤ) * p + u) by ring]
      exact Dvd.dvd.mul_left hd _)
  rw [jacobiSym.mod_left' hmod, jacobiSym.mul_left, jacobiSym.sq_one' hgcd, one_mul]

/-- L2 in ψ form: if `p ≡ 1 (mod 8)`, `gcd(a, u) = 1`, and every odd prime factor of
    `a p + u` lies in `ker ψ`, then `J(u | p) = 1`. -/
theorem psi_kernel_forces_residue {p a u : ℕ} (hp8 : p % 8 = 1) (hu : 0 < u)
    (hcop : Nat.Coprime a u)
    (h : ∀ q, q.Prime → q ∣ a * p + u → Odd q → jacobiSym (-((a : ℤ) * u)) q = 1) :
    jacobiSym u p = 1 :=
  psi_obstruction_forces_residue hp8 hu fun q hq hd ho => by
    rw [← psi_eq_jacobi hq hcop hd]
    exact h q hq hd ho

/-- Contrapositive: a non-residue shift `u` always has an odd prime factor `q` of
    `a p + u` outside `ker ψ`. (This is necessary, not sufficient, for a witness.) -/
theorem nonresidue_shift_escapes_psi {p a u : ℕ} (hp8 : p % 8 = 1) (hu : 0 < u)
    (hcop : Nat.Coprime a u) (hJ : jacobiSym u p = -1) :
    ∃ q, q.Prime ∧ q ∣ a * p + u ∧ Odd q ∧ jacobiSym (-((a : ℤ) * u)) q ≠ 1 := by
  by_contra hne
  push Not at hne
  have := psi_kernel_forces_residue hp8 hu hcop hne
  rw [hJ] at this
  norm_num at this

#print axioms jacobi_eq_one_of_prime_factors
#print axioms psi_obstruction_forces_residue
#print axioms psi_eq_jacobi
#print axioms psi_kernel_forces_residue
#print axioms nonresidue_shift_escapes_psi

end OutcastsMathLab.Research.PsiObstruction
