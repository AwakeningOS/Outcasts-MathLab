import Mathlib

namespace OutcastsMathLab.Research.KneserGap20261010

/-- This is the actual bounded-exponent product set, not the generated group. -/
def D : Finset ℕ :=
  (({1, 5} : Finset ℕ).product
    (({1, 3} : Finset ℕ).product ({1, 11} : Finset ℕ))).image
      (fun z => (z.1 * z.2.1 * z.2.2) % 16)

def G : Finset ℕ := {1, 3, 5, 7, 9, 11, 13, 15}

theorem input_residual_and_budget :
    8615161 % 840 = 121 ∧ 2^23 < (8615161 : ℕ) ∧ 8615161 ≤ 2^24 := by norm_num

theorem linear_form_factorization :
    4 * (8615161 : ℕ) + 1 = 5 * 163 * 42283 := by norm_num

theorem factor_residues :
    5 % 16 = (5 : ℕ) ∧ 163 % 16 = (3 : ℕ) ∧ 42283 % 16 = (11 : ℕ) := by norm_num

theorem actual_product_set : D = {1, 3, 5, 7, 11, 15} := by decide

theorem actual_target_and_gap :
    15 ∈ D ∧ D.card = 6 ∧ G.card = 8 ∧ ¬ (9 ∈ D) ∧ ¬ (13 ∈ D) := by decide

theorem residue_orders_four :
    ((5 : ℕ)^4 % 16 = 1 ∧ 5 % 16 ≠ 1 ∧ 5^2 % 16 ≠ 1 ∧ 5^3 % 16 ≠ 1) ∧
    ((3 : ℕ)^4 % 16 = 1 ∧ 3 % 16 ≠ 1 ∧ 3^2 % 16 ≠ 1 ∧ 3^3 % 16 ≠ 1) ∧
    ((11 : ℕ)^4 % 16 = 1 ∧ 11 % 16 ≠ 1 ∧ 11^2 % 16 ≠ 1 ∧ 11^3 % 16 ≠ 1) := by norm_num

theorem admissible_trivial_quotient_shortage :
    (1 + 1 + 1 : ℕ) < G.card - 1 := by decide

theorem divisor_witness :
    815 ∣ 4 * (8615161 : ℕ) + 1 ∧ 4 * 4 * 1 ∣ (815 : ℕ) + 1 := by norm_num

theorem positive_unit_fraction_identity :
    (4 : ℚ) / 8615161 =
      1 / 2156433 + 1 / 1757492844 + 1 / 74312069922852 := by norm_num

end OutcastsMathLab.Research.KneserGap20261010

#print axioms OutcastsMathLab.Research.KneserGap20261010.input_residual_and_budget
#print axioms OutcastsMathLab.Research.KneserGap20261010.linear_form_factorization
#print axioms OutcastsMathLab.Research.KneserGap20261010.factor_residues
#print axioms OutcastsMathLab.Research.KneserGap20261010.actual_product_set
#print axioms OutcastsMathLab.Research.KneserGap20261010.actual_target_and_gap
#print axioms OutcastsMathLab.Research.KneserGap20261010.residue_orders_four
#print axioms OutcastsMathLab.Research.KneserGap20261010.admissible_trivial_quotient_shortage
#print axioms OutcastsMathLab.Research.KneserGap20261010.divisor_witness
#print axioms OutcastsMathLab.Research.KneserGap20261010.positive_unit_fraction_identity
