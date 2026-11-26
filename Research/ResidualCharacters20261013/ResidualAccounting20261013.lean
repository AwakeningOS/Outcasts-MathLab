import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ResidualAccounting20261013

def residual (u t w : ℚ) : ℚ :=
  max (u-w) 0 - min t (max (u-w) 0)

def leftover (u t w : ℚ) : ℚ :=
  t - min t (max (u-w) 0)

theorem residual_positive_part (u t w : ℚ) (ht : 0 ≤ t) :
    residual u t w = max (u-t-w) 0 := by
  unfold residual
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem leftover_nonnegative (u t w : ℚ) :
    0 ≤ leftover u t w := by
  unfold leftover
  exact sub_nonneg.mpr (min_le_left _ _)

theorem residual_bound (u t w : ℚ) (ht : 0 ≤ t) (htu : t ≤ u)
    (hw : 0 ≤ w) : 0 ≤ residual u t w ∧ residual u t w ≤ u-t := by
  rw [residual_positive_part u t w ht]
  constructor
  · exact le_max_right _ _
  · apply max_le
    · linarith
    · linarith

theorem corrected_identity (u t w : ℚ) :
    w = u-t-residual u t w + max (w-u) 0 + leftover u t w := by
  unfold residual leftover
  simp only [max_def]
  split_ifs <;> linarith

theorem valid_lower_bound (u t w : ℚ) :
    u-t-residual u t w + max (w-u) 0 ≤ w := by
  have he := corrected_identity u t w
  have hn := leftover_nonnegative u t w
  linarith

theorem certificate_upper (u t w j : ℚ) (ht : 0 ≤ t) (htu : t ≤ u)
    (hw : 0 ≤ w) (hj : u-t-j ≤ w) :
    residual u t w ≤ min (u-t) (max j 0) := by
  apply le_min
  · exact (residual_bound u t w ht htu hw).2
  · rw [residual_positive_part u t w ht]
    apply max_le
    · have hm : j ≤ max j 0 := le_max_left _ _
      linarith
    · exact le_max_right _ _

theorem sharp_scalar_bound : residual 1 0 0 = 1 := by norm_num [residual]

theorem fixed_box_missing_term :
    (3 : ℚ) = 12571/1320 - 3831/440 + 21/10 + 1/12 := by norm_num

theorem fixed_box_wrong_identity :
    (3 : ℚ) ≠ 12571/1320 - 3831/440 + 21/10 := by norm_num

theorem fixed_box_certificate_positive :
    (0 : ℚ) < 12571/1320 - 4007/440 := by norm_num

#print axioms residual_positive_part
#print axioms leftover_nonnegative
#print axioms residual_bound
#print axioms corrected_identity
#print axioms valid_lower_bound
#print axioms certificate_upper
#print axioms sharp_scalar_bound
#print axioms fixed_box_missing_term
#print axioms fixed_box_wrong_identity
#print axioms fixed_box_certificate_positive

end ResidualAccounting20261013
