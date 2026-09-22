import Std

namespace OutcastsLunaReply

-- Rational equality, checked by Lean's kernel using decidable equality.
theorem example_1201 :
    (4 : Rat) / 1201 = 1 / 306 + 1 / 21618 + 1 / 61251 := by
  decide +kernel

-- Integer arithmetic check for the same example.
theorem example_1201_integer :
    (4 : Nat) * 306 * 21618 * 61251 =
      1201 * (306 * 21618 + 306 * 61251 + 21618 * 61251) := by
  decide

theorem other_example_1201_a :
    (4 : Rat) / 1201 = 1 / 306 + 1 / 15980 + 1 / 172727820 := by
  decide +kernel

theorem other_example_1201_b :
    (4 : Rat) / 1201 = 1 / 306 + 1 / 16218 + 1 / 1082101 := by
  decide +kernel

-- This polynomial identity does not need positivity or coprimality.
theorem factor_pair_identity (c M y z : Int) :
    (c * y - M) * (c * z - M) - M * M =
      c * (c * y * z - M * (y + z)) := by
  grind

-- Work in Int so that subtraction is not truncated as it would be in Nat.
theorem factor_pair_iff (c M y z : Int) (hc : c ≠ 0) :
    c * y * z = M * (y + z) ↔
      (c * y - M) * (c * z - M) = M * M := by
  constructor
  · intro h
    have hid := factor_pair_identity c M y z
    rw [h, Int.sub_self, Int.mul_zero] at hid
    exact Int.eq_of_sub_eq_zero hid
  · intro h
    have hid := factor_pair_identity c M y z
    rw [h, Int.sub_self] at hid
    have hz : c * (c * y * z - M * (y + z)) = 0 := hid.symm
    exact Int.eq_of_sub_eq_zero ((Int.mul_eq_zero.mp hz).resolve_left hc)

-- A specialization of a known Type II congruence family, not a new
-- solution of the full conjecture. n=1201 corresponds to t=3.
theorem known_family_integer (t n : Int) (h : n + 23 = 408 * t) :
    4 * (102 * t) * (6 * t * n) * (17 * t * n) =
      n * ((102 * t) * (6 * t * n) +
        (102 * t) * (17 * t * n) + (6 * t * n) * (17 * t * n)) := by
  grind

theorem known_family_positive (t n : Int)
    (ht : 1 ≤ t) (h : n + 23 = 408 * t) :
    0 < n ∧ 0 < 102 * t ∧ 0 < 6 * t * n ∧ 0 < 17 * t * n := by
  have hn : 0 < n := by omega
  have h6 : 0 < 6 * t := by omega
  have h17 : 0 < 17 * t := by omega
  exact ⟨hn, by omega, Int.mul_pos h6 hn, Int.mul_pos h17 hn⟩

end OutcastsLunaReply

#print axioms OutcastsLunaReply.example_1201
#print axioms OutcastsLunaReply.example_1201_integer
#print axioms OutcastsLunaReply.factor_pair_identity
#print axioms OutcastsLunaReply.factor_pair_iff
#print axioms OutcastsLunaReply.other_example_1201_a
#print axioms OutcastsLunaReply.other_example_1201_b
#print axioms OutcastsLunaReply.known_family_integer
#print axioms OutcastsLunaReply.known_family_positive
