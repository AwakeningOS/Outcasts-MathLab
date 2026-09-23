import Std
import OutcastsMathLab.Problems.P001_ErdosStraus1201.Statement

namespace OutcastsMathLab.P001

theorem solution_yields_factor_pair : SolutionYieldsFactorPair := by
  intro c M y z hc hM hy hyz heq
  dsimp
  have hz : 0 < z := by omega

  have ha_pos : 0 < c * y - M := by
    by_cases ha : 0 < c * y - M
    · exact ha
    · have hle : c * y - M ≤ 0 := by omega
      have hz0 : 0 ≤ z := by omega
      have hle_prod : (c * y - M) * z ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg hle hz0
      have h_sub : (c * y - M) * z = M * y := by grind
      rw [h_sub] at hle_prod
      have hpos_prod : 0 < M * y := Int.mul_pos hM hy
      omega

  have ha_le_M : c * y - M ≤ M := by
    by_cases hle : c * y ≤ 2 * M
    · omega
    · have hgt : 2 * M < c * y := by omega
      have h_diff_pos : 0 < c * y - 2 * M := by omega
      have h_prod_pos : 0 < (c * y - 2 * M) * z := Int.mul_pos h_diff_pos hz
      have h_id : (c * y - 2 * M) * z = M * (y - z) := by grind
      have h_yz_nonpos : y - z ≤ 0 := by omega
      have hM_nonneg : 0 ≤ M := by omega
      have h_prod_nonpos : M * (y - z) ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos hM_nonneg h_yz_nonpos
      rw [h_id] at h_prod_pos
      omega

  have hab : (c * y - M) * (c * z - M) = M ^ 2 := by
    have hid : (c * y - M) * (c * z - M) - M ^ 2 = c * (c * y * z - M * (y + z)) := by grind
    rw [heq] at hid
    have : c * (M * (y + z) - M * (y + z)) = 0 := by grind
    rw [this] at hid
    omega

  have h_dvd_a : c ∣ (c * y - M) + M := by
    have : (c * y - M) + M = c * y := by omega
    rw [this]
    exact ⟨y, rfl⟩

  have h_dvd_b : c ∣ (c * z - M) + M := by
    have : (c * z - M) + M = c * z := by omega
    rw [this]
    exact ⟨z, rfl⟩

  exact ⟨ha_pos, ha_le_M, hab, h_dvd_a, h_dvd_b⟩

#print axioms solution_yields_factor_pair

end OutcastsMathLab.P001
