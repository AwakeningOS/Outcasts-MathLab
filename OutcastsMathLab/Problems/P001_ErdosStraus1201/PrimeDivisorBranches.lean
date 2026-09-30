import Mathlib.Data.Nat.Prime.Defs

namespace OutcastsPrimeDivisorBranches

-- A divisor of (p*x)^2 that is coprime to p already divides x^2.
theorem remove_coprime_square (p x a : Nat)
    (hcop : Nat.Coprime a p) (hd : a ∣ (p * x) * (p * x)) :
    a ∣ x * x := by
  have hd' : a ∣ (p * p) * (x * x) := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hd
  exact (hcop.mul_right hcop).dvd_of_dvd_mul_left hd'

-- The upper bound is essential: it excludes a second factor of p.
theorem bounded_divisor_split (p x a : Nat) (hp : Nat.Prime p)
    (hxp : x < p) (ha : 0 < a) (haM : a ≤ p * x)
    (hd : a ∣ (p * x) * (p * x)) :
    (a ∣ x * x ∧ ¬ p ∣ a) ∨
      ∃ t, a = p * t ∧ 0 < t ∧ t ≤ x ∧ t ∣ x * x := by
  by_cases hpa : p ∣ a
  · obtain ⟨t, hat⟩ := hpa
    have ht : 0 < t := by
      by_contra h
      have ht0 : t = 0 := by omega
      simp [ht0] at hat
      omega
    have htx : t ≤ x := by
      apply Nat.le_of_mul_le_mul_left (c := p)
      · simpa [hat] using haM
      · exact hp.pos
    have hnot : ¬ p ∣ t := by
      intro h
      have := Nat.le_of_dvd ht h
      omega
    have hcop : Nat.Coprime t p := (hp.coprime_iff_not_dvd.mpr hnot).symm
    have hpd : p * t ∣ p * (p * (x * x)) := by
      simpa [hat, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hd
    have htd : t ∣ p * (x * x) := Nat.dvd_of_mul_dvd_mul_left hp.pos hpd
    exact Or.inr ⟨t, hat, ht, htx, hcop.dvd_of_dvd_mul_left htd⟩
  · exact Or.inl ⟨remove_coprime_square p x a
      (hp.coprime_iff_not_dvd.mpr hpa).symm hd, hpa⟩

-- Natural-number form of the previous factor witness; no truncated subtraction.
def FactorWitness (p x c a : Nat) : Prop :=
  0 < a ∧ a ≤ p * x ∧ a ∣ (p * x) * (p * x) ∧
    c ∣ a + p * x ∧ c * x ≤ a + p * x

def BranchI (p x c t : Nat) : Prop :=
  0 < t ∧ t ≤ p * x ∧ t ∣ x * x ∧
    c ∣ t + p * x ∧ c * x ≤ t + p * x

def BranchII (p x c t : Nat) : Prop :=
  0 < t ∧ t ≤ x ∧ t ∣ x * x ∧
    c ∣ t + x ∧ c * x ≤ p * (t + x)

-- Exact disjunction, retaining the order lower bound in both branches.
-- c = 4*x-p is the application; here only gcd(c,p)=1 is needed.
theorem factor_witness_iff_branches (p x c a : Nat) (hp : Nat.Prime p)
    (hxp : x < p) (hcop : Nat.Coprime c p) :
    FactorWitness p x c a ↔
      BranchI p x c a ∨ ∃ t, a = p * t ∧ BranchII p x c t := by
  constructor
  · rintro ⟨ha, haM, hd, hcong, hbound⟩
    rcases bounded_divisor_split p x a hp hxp ha haM hd with hI | ⟨t, hat, ht, htx, htd⟩
    · exact Or.inl ⟨ha, haM, hI.1, hcong, hbound⟩
    · apply Or.inr
      refine ⟨t, hat, ht, htx, htd, ?_, ?_⟩
      · apply hcop.dvd_of_dvd_mul_left
        simpa [hat, Nat.mul_add] using hcong
      · simpa [hat, Nat.mul_add] using hbound
  · intro h
    rcases h with hI | ⟨t, hat, ht, htx, htd, hcong, hbound⟩
    · rcases hI with ⟨ha, haM, hd, hcong, hbound⟩
      refine ⟨ha, haM, ?_, hcong, hbound⟩
      have hd' : a ∣ (p * p) * (x * x) := Nat.dvd_mul_left_of_dvd hd (p * p)
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hd'
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa [hat] using Nat.mul_pos hp.pos ht
      · simpa [hat] using Nat.mul_le_mul_left p htx
      · have hd' : p * t ∣ p * (x * x) := Nat.mul_dvd_mul_left p htd
        have hd'' : p * t ∣ p * (p * (x * x)) := Nat.dvd_mul_left_of_dvd hd' p
        simpa [hat, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hd''
      · have hcong' : c ∣ p * (t + x) := Nat.dvd_mul_left_of_dvd hcong p
        simpa [hat, Nat.mul_add] using hcong'
      · simpa [hat, Nat.mul_add] using hbound

end OutcastsPrimeDivisorBranches

#print axioms OutcastsPrimeDivisorBranches.remove_coprime_square
#print axioms OutcastsPrimeDivisorBranches.bounded_divisor_split
#print axioms OutcastsPrimeDivisorBranches.factor_witness_iff_branches
