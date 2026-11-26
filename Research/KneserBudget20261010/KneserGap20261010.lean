import Mathlib.Data.Finset.Prod

namespace OutcastsMathLab.Research.KneserGap20261010

/-- This is the actual bounded-exponent product set, not the generated group. -/
def D : Finset ℕ :=
  (({1, 5} : Finset ℕ).product
    (({1, 3} : Finset ℕ).product ({1, 11} : Finset ℕ))).image
      (fun z => (z.1 * z.2.1 * z.2.2) % 16)

def G : Finset ℕ := {1, 3, 5, 7, 9, 11, 13, 15}

theorem actual_product_set : D = {1, 3, 5, 7, 11, 15} := by decide

theorem actual_target_and_gap :
    15 ∈ D ∧ D.card = 6 ∧ G.card = 8 ∧ ¬ (9 ∈ D) ∧ ¬ (13 ∈ D) := by decide

theorem residue_orders_four :
    ((5 : ℕ)^4 % 16 = 1 ∧ 5 % 16 ≠ 1 ∧ 5^2 % 16 ≠ 1 ∧ 5^3 % 16 ≠ 1) ∧
    ((3 : ℕ)^4 % 16 = 1 ∧ 3 % 16 ≠ 1 ∧ 3^2 % 16 ≠ 1 ∧ 3^3 % 16 ≠ 1) ∧
    ((11 : ℕ)^4 % 16 = 1 ∧ 11 % 16 ≠ 1 ∧ 11^2 % 16 ≠ 1 ∧ 11^3 % 16 ≠ 1) := by decide

theorem admissible_trivial_quotient_shortage :
    (1 + 1 + 1 : ℕ) < G.card - 1 := by decide

end OutcastsMathLab.Research.KneserGap20261010

#print axioms OutcastsMathLab.Research.KneserGap20261010.actual_product_set
#print axioms OutcastsMathLab.Research.KneserGap20261010.actual_target_and_gap
#print axioms OutcastsMathLab.Research.KneserGap20261010.residue_orders_four
#print axioms OutcastsMathLab.Research.KneserGap20261010.admissible_trivial_quotient_shortage
