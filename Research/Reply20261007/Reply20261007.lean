import OutcastsMathLab.Research.DeterministicFailure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.LegendreSymbol

namespace OutcastsMathLab.Research.Reply20261007

open OutcastsMathLab.Research.DeterministicFailure

theorem prime_form_forces_a_dvd_u_add_one {p a u s : ℕ}
    (ha : 0 < a) (hu : 0 < u) (hp : Nat.Prime (a*p+u))
    (hw : DivisorWitness p a u s) : a ∣ u+1 := by
  rcases hw with ⟨hs, hm⟩
  rcases (Nat.dvd_prime hp).mp hs with h1 | hM
  · subst s
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hm
    nlinarith
  · subst s
    have had : a ∣ a*p+u+1 := dvd_trans (by exact ⟨4*u, by ring⟩ : a ∣ 4*a*u) hm
    have hap : a ∣ a*p := dvd_mul_right a p
    have heq : a*p+u+1 = a*p+(u+1) := by omega
    rw [heq] at had
    exact (Nat.dvd_add_iff_right hap).mpr had

theorem rough_inputs_valid :
    Nat.Prime 2521 ∧ 2521 % 840 = 1 ∧
    2^11 < 2521 ∧ 2521 ≤ 2^12 ∧
    12*2521+1 = 30253 ∧ Nat.Prime 30253 ∧ Nat.gcd 30253 210 = 1 ∧
    10*2521+1 = 17*1483 ∧ Nat.gcd 25211 210 = 1 := by
  norm_num

theorem rough_prime_failure (s : ℕ) : ¬ DivisorWitness 2521 12 1 s := by
  intro hw
  have ha := prime_form_forces_a_dvd_u_add_one (by decide) (by decide)
    (by norm_num : Nat.Prime (12*2521+1)) hw
  norm_num at ha

theorem rough_semiprime_failure (s : ℕ) : ¬ DivisorWitness 2521 10 1 s := by
  apply no_divisorWitness_of_cert (L := [(17,1),(1483,1)])
  · norm_num
  · norm_num [prodPow]
  · decide

theorem gemmy_witnesses :
    Nat.Prime 345601 ∧ Nat.Prime 670849 ∧
    DivisorWitness 345601 1 9 107 ∧ DivisorWitness 670849 1 8 7711 ∧
    9 ≤ 19 ∧ 8 ≤ 20 ∧
    jacobiSym (9 : ℤ) 345601 = 1 ∧ jacobiSym (8 : ℤ) 670849 = 1 ∧
    7711 = 11*701 ∧ Nat.Prime 11 ∧ Nat.Prime 701 := by
  norm_num [DivisorWitness]

theorem gemmy_reconstructions :
    (4*87210*9331227*3348873690 : ℕ) =
       345601*(87210*9331227 + 87210*3348873690 + 9331227*3348873690) ∧
    (4*167736*1293396872*14065690983 : ℕ) =
       670849*(167736*1293396872 + 167736*14065690983 + 1293396872*14065690983) := by
  norm_num

theorem square_divisor_residues_345601 (t : ℕ) (ht : t ∣ 86402^2) :
    t%7 = 1 ∨ t%7 = 2 ∨ t%7 = 4 := by
  have hfac : prodPow [(2,2),(43201,2)] = 86402^2 := by norm_num [prodPow]
  have hpr : ∀ qe ∈ ([(2,2),(43201,2)] : List (ℕ × ℕ)), Nat.Prime qe.1 := by norm_num
  have hm := mem_subProducts_of_dvd [(2,2),(43201,2)] hpr t (by rw [hfac]; exact ht)
  have hc : ∀ d ∈ subProducts [(2,2),(43201,2)], d%7=1 ∨ d%7=2 ∨ d%7=4 := by decide
  exact hc t hm

theorem square_divisor_residues_670849 (t : ℕ) (ht : t ∣ 167714^2) :
    t%7 = 1 ∨ t%7 = 2 ∨ t%7 = 4 := by
  have hfac : prodPow [(2,2),(83857,2)] = 167714^2 := by norm_num [prodPow]
  have hpr : ∀ qe ∈ ([(2,2),(83857,2)] : List (ℕ × ℕ)), Nat.Prime qe.1 := by norm_num
  have hm := mem_subProducts_of_dvd [(2,2),(83857,2)] hpr t (by rw [hfac]; exact ht)
  have hc : ∀ d ∈ subProducts [(2,2),(83857,2)], d%7=1 ∨ d%7=2 ∨ d%7=4 := by decide
  exact hc t hm

theorem fixed_c7_both_branches_fail :
    (∀ t : ℕ, t ∣ 86402^2 → ¬ 7 ∣ t+345601*86402 ∧ ¬ 7 ∣ t+86402) ∧
    (∀ t : ℕ, t ∣ 167714^2 → ¬ 7 ∣ t+670849*167714 ∧ ¬ 7 ∣ t+167714) := by
  constructor
  · intro t ht
    have hr := square_divisor_residues_345601 t ht
    omega
  · intro t ht
    have hr := square_divisor_residues_670849 t ht
    omega

#print axioms prime_form_forces_a_dvd_u_add_one
#print axioms rough_inputs_valid
#print axioms rough_prime_failure
#print axioms rough_semiprime_failure
#print axioms gemmy_witnesses
#print axioms gemmy_reconstructions
#print axioms square_divisor_residues_345601
#print axioms square_divisor_residues_670849
#print axioms fixed_c7_both_branches_fail

end OutcastsMathLab.Research.Reply20261007
