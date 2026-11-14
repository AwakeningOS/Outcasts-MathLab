import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/- Conditional arithmetic requested in Outcasts #87.
No existence of an allowed shifted source or successful divisor is asserted. -/
namespace OutcastsMathLab.Research.SquareShift20261023

theorem square_shift_identity {p A t₁ t₂ x₁ x₂ : ℤ}
    (h₁ : 4*x₁=p+A*t₁^2) (h₂ : 4*x₂=p+A*t₂^2) :
    4*(x₂-x₁)=A*(t₂^2-t₁^2) := by linear_combination h₂-h₁

theorem preserve_power_odd_modulus {p A t₁ t₂ x₁ x₂ M : ℤ}
    (h₁ : 4*x₁=p+A*t₁^2) (h₂ : 4*x₂=p+A*t₂^2)
    (hcop : IsCoprime M 4) (hx : M ∣ x₁) (ht : M ∣ t₂^2-t₁^2) :
    M ∣ x₂ := by
  obtain ⟨k,hk⟩ := hx
  obtain ⟨j,hj⟩ := ht
  have hmul : M ∣ 4*x₂ := by
    refine ⟨4*k+A*j, ?_⟩
    linear_combination h₂-h₁+4*hk+A*hj
  exact hcop.dvd_of_dvd_mul_left hmul

theorem preserve_power_quarter_difference {p A t₁ t₂ x₁ x₂ M delta : ℤ}
    (h₁ : 4*x₁=p+A*t₁^2) (h₂ : 4*x₂=p+A*t₂^2)
    (hdelta : t₂^2-t₁^2=4*delta) (hx : M ∣ x₁) (hd : M ∣ delta) :
    M ∣ x₂ := by
  obtain ⟨k,hk⟩ := hx
  obtain ⟨j,hj⟩ := hd
  refine ⟨k+A*j, ?_⟩
  have hfour : 4*x₂=4*(M*(k+A*j)) := by
    linear_combination h₂-h₁+4*hk+A*hdelta+4*A*hj
  linarith

theorem noncoprime_projections_lose_information :
    (122:ℕ)%11=1%11 ∧ (122:ℕ)%121=1%121 ∧ (122:ℕ)%1331≠1%1331 := by
  norm_num

theorem higher_power_exclusion {p A t₁ t₂ x₁ x₂ M delta : ℤ}
    (h₁ : 4*x₁=p+A*t₁^2) (h₂ : 4*x₂=p+A*t₂^2)
    (hdelta : t₂^2-t₁^2=4*delta) (hd : M ∣ delta)
    (hx : ¬ M ∣ x₁) : ¬ M ∣ x₂ := by
  intro hx₂
  have hreverse : t₁^2-t₂^2=4*(-delta) := by linarith
  exact hx (preserve_power_quarter_difference h₂ h₁ hreverse hx₂ (dvd_neg.mpr hd))

#print axioms square_shift_identity
#print axioms preserve_power_odd_modulus
#print axioms preserve_power_quarter_difference
#print axioms noncoprime_projections_lose_information
#print axioms higher_power_exclusion
end OutcastsMathLab.Research.SquareShift20261023
