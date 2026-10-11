import OutcastsMathLab.Research.DeterministicFailure
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace OutcastsMathLab.Research.Reply20261008

open OutcastsMathLab.Research.DeterministicFailure

theorem continued_fraction_candidate_inputs :
    Nat.Prime 2521 ∧ Nat.Prime 631 ∧ 4*631 = 2521+3 ∧
    631 % 3 = 1 ∧ 2521 % 3 = 1 := by
  norm_num

#print axioms continued_fraction_candidate_inputs

theorem square_divisors_631_residue (d : ℕ) (hd : d ∣ 631^2) : d % 3 = 1 := by
  have hfac : prodPow [(631,2)] = 631^2 := by norm_num [prodPow]
  have hpr : ∀ qe ∈ ([(631,2)] : List (ℕ × ℕ)), Nat.Prime qe.1 := by norm_num
  have hm := mem_subProducts_of_dvd [(631,2)] hpr d (by rw [hfac]; exact hd)
  have hc : ∀ t ∈ subProducts [(631,2)], t % 3 = 1 := by decide
  exact hc d hm

#print axioms square_divisors_631_residue

theorem continued_fraction_candidate_both_branches_fail (d : ℕ) (hd : d ∣ 631^2) :
    ¬ 3 ∣ d+2521*631 ∧ ¬ 3 ∣ d+631 := by
  have hr := square_divisors_631_residue d hd
  omega

#print axioms continued_fraction_candidate_both_branches_fail

theorem c11_group_targets_reachable :
    633 = 3*211 ∧ Nat.Prime 211 ∧ 4*633 = 2521+11 ∧
    211^5 % 11 = 10 ∧ 211^7 % 11 = 7 := by
  norm_num

#print axioms c11_group_targets_reachable

theorem c11_bounded_exponents_both_branches_fail (d : ℕ) (hd : d ∣ 633^2) :
    ¬ 11 ∣ d+2521*633 ∧ ¬ 11 ∣ d+633 := by
  have hfac : prodPow [(3,2),(211,2)] = 633^2 := by norm_num [prodPow]
  have hpr : ∀ qe ∈ ([(3,2),(211,2)] : List (ℕ × ℕ)), Nat.Prime qe.1 := by norm_num
  have hm := mem_subProducts_of_dvd [(3,2),(211,2)] hpr d (by rw [hfac]; exact hd)
  have hc : ∀ t ∈ subProducts [(3,2),(211,2)],
      ¬ 11 ∣ t+2521*633 ∧ ¬ 11 ∣ t+633 := by decide
  exact hc d hm

#print axioms c11_bounded_exponents_both_branches_fail

def ExactSolution (p x y z : ℕ) : Prop :=
  0 < x ∧ x ≤ y ∧ y ≤ z ∧ 4*x*y*z = p*(x*y+x*z+y*z)

def TypeICertificate (p x y z : ℕ) : Prop :=
  ExactSolution p x y z ∧ ¬ p ∣ x ∧ ¬ p ∣ y ∧ p ∣ z

def TypeIICertificate (p x y z : ℕ) : Prop :=
  ExactSolution p x y z ∧ ¬ p ∣ x ∧ p ∣ y ∧ p ∣ z

theorem witness_2521 :
    TypeICertificate 2521 636 69748 131876031 ∧
    TypeIICertificate 2521 636 70588 5611746 := by
  norm_num [TypeICertificate, TypeIICertificate, ExactSolution]

#print axioms witness_2521

theorem witness_66529 :
    TypeICertificate 66529 16637 58254900 507708871715100 ∧
    TypeIICertificate 66529 16640 35925660 5978029824 := by
  norm_num [TypeICertificate, TypeIICertificate, ExactSolution]

#print axioms witness_66529

theorem witness_345601 :
    TypeICertificate 345601 86403 2714633026 976645263843789666 ∧
    TypeIICertificate 345601 86405 1573866954 1123884083970 := by
  norm_num [TypeICertificate, TypeIICertificate, ExactSolution]

#print axioms witness_345601

theorem witness_670849 :
    TypeICertificate 670849 167717 5922422704 50291789222224 ∧
    TypeIICertificate 670849 167722 2885321549 28466582402434 := by
  norm_num [TypeICertificate, TypeIICertificate, ExactSolution]

#print axioms witness_670849

theorem witness_5843041 :
    TypeICertificate 5843041 1460761 2845095471618 37187909228186680226106 ∧
    TypeIICertificate 5843041 1460761 2846367306658 6367323664993946 := by
  norm_num [TypeICertificate, TypeIICertificate, ExactSolution]

#print axioms witness_5843041

end OutcastsMathLab.Research.Reply20261008
