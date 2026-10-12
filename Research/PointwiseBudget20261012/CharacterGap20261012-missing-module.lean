import Mathlib.Data.Rat.Order
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.NormNum

/- Numeric certificate only. These lists were extracted from the independently
checked43-row table for p66529/B17. Primality, row completeness, factorization,
and general character orthogonality are NOT proved by this Lean file. -/
namespace CharacterGap20261012

def principals : List ℚ := [
  (2 : ℚ),
  (2 : ℚ),
  (1 : ℚ) / 2,
  (1 : ℚ) / 4,
  (1 : ℚ),
  (1 : ℚ),
  (1 : ℚ) / 6,
  (3 : ℚ) / 8,
  (2 : ℚ) / 3,
  (1 : ℚ) / 2,
  (2 : ℚ) / 5,
  (1 : ℚ) / 8,
  (1 : ℚ) / 3,
  (1 : ℚ) / 3,
  (1 : ℚ) / 8,
  (1 : ℚ) / 8,
  (3 : ℚ) / 16,
  (2 : ℚ),
  (1 : ℚ) / 2,
  (1 : ℚ) / 4,
  (1 : ℚ) / 2,
  (1 : ℚ),
  (3 : ℚ) / 4,
  (1 : ℚ) / 4,
  (1 : ℚ) / 4,
  (1 : ℚ) / 4,
  (3 : ℚ) / 8,
  (1 : ℚ) / 2,
  (1 : ℚ) / 4,
  (1 : ℚ) / 4,
  (3 : ℚ) / 2,
  (1 : ℚ) / 3,
  (1 : ℚ),
  (3 : ℚ) / 4,
  (1 : ℚ) / 3,
  (1 : ℚ) / 2,
  (2 : ℚ) / 5,
  (1 : ℚ) / 4,
  (1 : ℚ) / 3,
  (1 : ℚ) / 3,
  (1 : ℚ) / 4,
  (1 : ℚ) / 4,
  (3 : ℚ) / 8
]
def witnessCounts : List ℚ := [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def absoluteErrors : List ℚ :=
  List.zipWith (fun w u => |w-u|) witnessCounts principals

theorem principal_sum : principals.sum = (5717 : ℚ)/240 := by
  norm_num [principals]
theorem absolute_sum : absoluteErrors.sum = (5717 : ℚ)/240 := by
  norm_num [absoluteErrors, witnessCounts, principals, List.zipWith]
theorem actual_sum : witnessCounts.sum = 4 := by
  norm_num [witnessCounts]
theorem no_positive_L1_gap : ¬ (0 < principals.sum - absoluteErrors.sum) := by
  rw [principal_sum, absolute_sum]
  norm_num
theorem actual_count_positive : 0 < witnessCounts.sum := by
  rw [actual_sum]
  norm_num

#print axioms principal_sum
#print axioms absolute_sum
#print axioms actual_sum
#print axioms no_positive_L1_gap
#print axioms actual_count_positive
end CharacterGap20261012
