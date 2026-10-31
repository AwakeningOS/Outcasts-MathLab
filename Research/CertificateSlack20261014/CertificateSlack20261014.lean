import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace CertificateSlack20261014

def gap (v w slack : ℚ) : ℚ :=
  v - min v (max (v + slack - w) 0)

theorem slack_identity (v w slack : ℚ) (hv : 0 ≤ v) :
    gap v w slack = min v (max (w - slack) 0) := by
  unfold gap
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem positive_criterion (v w slack : ℚ) (hv : 0 ≤ v) :
    0 < gap v w slack ↔ 0 < v ∧ slack < w := by
  rw [slack_identity v w slack hv]
  simp only [lt_min_iff, lt_max_iff, lt_self_iff_false, or_false, sub_pos]

theorem exact_gap (v w : ℚ) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    gap v w 0 = min v w := by
  rw [slack_identity v w 0 hv]
  simp only [sub_zero, max_eq_left hw]

theorem compatible_v_positive (v w phi : ℚ) (hphi : 0 < phi)
    (hw : 0 < w) (hc : 2*w ≤ phi*v) : 0 < v := by
  by_contra hn
  have hv : v ≤ 0 := le_of_not_gt hn
  have hm : phi*v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hphi) hv
  linarith

theorem exact_positive_iff (v w phi : ℚ) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hphi : 0 < phi) (hc : 2*w ≤ phi*v) :
    0 < gap v w 0 ↔ 0 < w := by
  rw [exact_gap v w hv hw, lt_min_iff]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨compatible_v_positive v w phi hphi h hc, h⟩

theorem scalar_compatibility_needed :
    gap 0 1 0 = 0 ∧ (0 : ℚ) < 1 := by
  norm_num [gap]

#print axioms slack_identity
#print axioms positive_criterion
#print axioms exact_gap
#print axioms compatible_v_positive
#print axioms exact_positive_iff
#print axioms scalar_compatibility_needed

end CertificateSlack20261014
