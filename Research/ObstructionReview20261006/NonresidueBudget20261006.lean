import OutcastsMathLab.Research.HardPrimes20261005
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

namespace OutcastsMathLab.Research.NonresidueBudget20261006

open OutcastsMathLab.Research.DeterministicFailure

theorem inputs_valid :
    Nat.Prime 345601 ∧ Nat.Prime 670849 ∧
    345601 % 840 = 361 ∧ 670849 % 840 = 529 ∧
    2^18 < 345601 ∧ 345601 ≤ 2^19 ∧
    2^19 < 670849 ∧ 670849 ≤ 2^20 := by
  norm_num

theorem only_nonresidue_345601 {u : ℕ} (hu : 0 < u) (hub : u ≤ 19)
    (hj : jacobiSym (u : ℤ) 345601 = -1) : u = 19 := by
  interval_cases u <;> norm_num at *

theorem only_nonresidue_670849 {u : ℕ} (hu : 0 < u) (hub : u ≤ 20)
    (hj : jacobiSym (u : ℤ) 670849 = -1) : u = 17 := by
  interval_cases u <;> norm_num at *

theorem nonresidues_are_real :
    jacobiSym (19 : ℤ) 345601 = -1 ∧ jacobiSym (17 : ℤ) 670849 = -1 := by
  norm_num

theorem no_nonresidue_budget_345601 (a u s : ℕ) (ha : 0 < a) (hu : 0 < u)
    (hbudget : a * u ≤ 19) (hj : jacobiSym (u : ℤ) 345601 = -1) :
    ¬ DivisorWitness 345601 a u s := by
  have hule : u ≤ 19 := by nlinarith
  have hueq := only_nonresidue_345601 hu hule hj
  subst u
  have hae : a = 1 := by omega
  subst a
  exact OutcastsMathLab.Research.HardPrimes20261005.p345601_a1_u19 s

theorem no_nonresidue_budget_670849 (a u s : ℕ) (ha : 0 < a) (hu : 0 < u)
    (hbudget : a * u ≤ 20) (hj : jacobiSym (u : ℤ) 670849 = -1) :
    ¬ DivisorWitness 670849 a u s := by
  have hule : u ≤ 20 := by nlinarith
  have hueq := only_nonresidue_670849 hu hule hj
  subst u
  have hae : a = 1 := by omega
  subst a
  exact OutcastsMathLab.Research.HardPrimes20261005.p670849_a1_u17 s

theorem group_power_escape_345601 :
    345601 + 19 = 4 * 5 * 11 * 1571 ∧
    Nat.Prime 1571 ∧ 1571 % 76 = 51 ∧
    (51 ^ 9 : ℕ) % 76 = 75 := by
  norm_num

#print axioms inputs_valid
#print axioms only_nonresidue_345601
#print axioms only_nonresidue_670849
#print axioms nonresidues_are_real
#print axioms no_nonresidue_budget_345601
#print axioms no_nonresidue_budget_670849
#print axioms group_power_escape_345601

end OutcastsMathLab.Research.NonresidueBudget20261006
