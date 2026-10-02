import Mathlib

/- A finite counterexample to a NEW short-product budget hypothesis.
   Existing P000/P001 statements are untouched.
   No assumption about prime factor distributions is used. -/
namespace OutcastsMathLab.Research.ShortProduct20261002

set_option maxHeartbeats 4000000

/-- A prime or a product of two primes is an ACTUAL divisor witness.
    The two primes may coincide; divisibility then requires enough multiplicity. -/
def ShortWitness (p a u : ℕ) : Prop :=
  (∃ q : ℕ, Nat.Prime q ∧ q ∣ a*p+u ∧ (q+1) % (4*a*u) = 0) ∨
  (∃ q r : ℕ, Nat.Prime q ∧ Nat.Prime r ∧ q*r ∣ a*p+u ∧
      (q*r+1) % (4*a*u) = 0)

/-- Expanded prime factors, their product, and exhaustive one/two-factor misses. -/
def Certificate (p a u : ℕ) (fs : List ℕ) : Prop :=
  fs.prod = a*p+u ∧
  (∀ q ∈ fs, Nat.Prime q) ∧
  (∀ q ∈ fs, (q+1) % (4*a*u) ≠ 0) ∧
  (∀ q ∈ fs, ∀ r ∈ fs, (q*r+1) % (4*a*u) ≠ 0)

theorem prime_mem_factors {q : ℕ} (hq : Nat.Prime q) :
    ∀ fs : List ℕ, (∀ f ∈ fs, Nat.Prime f) → q ∣ fs.prod → q ∈ fs := by
  intro fs
  induction fs with
  | nil =>
      intro _ hd
      have h : q ∣ 1 := by simpa using hd
      exact (hq.not_dvd_one h).elim
  | cons f fs ih =>
      intro hfs hd
      have hdiv : q ∣ f * fs.prod := by simpa using hd
      rcases hq.dvd_mul.mp hdiv with hf | ht
      · have hfp : Nat.Prime f := hfs f (by simp)
        have he : q = f := (Nat.prime_dvd_prime_iff_eq hq hfp).mp hf
        simp [he]
      · have htail : ∀ x ∈ fs, Nat.Prime x := by
          intro x hx
          exact hfs x (by simp [hx])
        exact List.mem_cons_of_mem f (ih htail ht)

theorem certificate_excludes {p a u : ℕ} {fs : List ℕ}
    (hc : Certificate p a u fs) : ¬ ShortWitness p a u := by
  intro hw
  rcases hw with ⟨q, hq, hd, hm⟩ | ⟨q, r, hq, hr, hd, hm⟩
  · have hdf : q ∣ fs.prod := by rw [hc.1]; exact hd
    exact hc.2.2.1 q (prime_mem_factors hq fs hc.2.1 hdf) hm
  · have hqM : q ∣ a*p+u := dvd_trans (show q ∣ q*r from ⟨r, rfl⟩) hd
    have hrM : r ∣ a*p+u := dvd_trans
      (show r ∣ q*r from ⟨q, Nat.mul_comm q r⟩) hd
    have hqf : q ∣ fs.prod := by rw [hc.1]; exact hqM
    have hrf : r ∣ fs.prod := by rw [hc.1]; exact hrM
    exact hc.2.2.2 q (prime_mem_factors hq fs hc.2.1 hqf)
      r (prime_mem_factors hr fs hc.2.1 hrf) hm

/-- All coprime positive pairs of product at most 23, with expanded factors. -/
def certificates : List (ℕ × ℕ × List ℕ) := [
  (1, 1, [2, 181, 16141]),
  (1, 2, [3, 3, 3, 379, 571]),
  (2, 1, [3, 19, 205019]),
  (1, 3, [2, 2, 653, 2237]),
  (3, 1, [2, 2, 4382281]),
  (1, 4, [5, 13, 241, 373]),
  (4, 1, [5, 4674433]),
  (1, 5, [2, 3, 11, 223, 397]),
  (5, 1, [2, 3, 3, 31, 41, 1277]),
  (1, 6, [7, 834721]),
  (2, 3, [5, 2337217]),
  (3, 2, [5, 5, 5, 17, 73, 113]),
  (6, 1, [7, 1753, 2857]),
  (1, 7, [2, 2, 2, 383, 1907]),
  (7, 1, [2, 2, 2, 5112661]),
  (1, 8, [3, 1947683]),
  (8, 1, [3, 15581443]),
  (1, 9, [2, 5, 5, 137, 853]),
  (9, 1, [2, 5, 11, 478067]),
  (1, 10, [19, 307529]),
  (2, 5, [7, 1669441]),
  (5, 2, [7, 59, 127, 557]),
  (10, 1, [13, 17, 264391]),
  (1, 11, [2, 2, 3, 3, 101, 1607]),
  (11, 1, [2, 2, 3, 79, 151, 449]),
  (1, 12, [17, 343709]),
  (3, 4, [7, 11, 227651]),
  (4, 3, [7, 7, 13, 36691]),
  (12, 1, [70116493]),
  (1, 13, [2, 7, 7, 109, 547]),
  (13, 1, [2, 7, 863, 6287]),
  (1, 14, [3, 5, 43, 9059]),
  (2, 7, [3, 17, 229139]),
  (7, 2, [3, 11, 13, 67, 1423]),
  (14, 1, [3, 3, 3, 5, 5, 121189]),
  (1, 15, [2, 2, 2, 2, 107, 3413]),
  (3, 5, [2, 2, 2, 23, 95267]),
  (5, 3, [2, 2, 2, 11, 11, 30181]),
  (15, 1, [2, 2, 2, 2, 139, 39409]),
  (1, 16, [11, 647, 821]),
  (16, 1, [179, 522283]),
  (1, 17, [2, 3, 13, 23, 3257]),
  (17, 1, [2, 3, 71, 233173]),
  (1, 18, [421, 13879]),
  (2, 9, [11686091]),
  (9, 2, [103, 439, 1163]),
  (18, 1, [9007, 11677]),
  (1, 19, [2, 2, 5, 463, 631]),
  (19, 1, [2, 2, 5, 23, 241343]),
  (1, 20, [3, 3, 7, 163, 569]),
  (4, 5, [3, 7790723]),
  (5, 4, [3, 29, 335807]),
  (20, 1, [3, 7, 11, 521, 971]),
  (1, 21, [2, 2921531]),
  (3, 7, [2, 5, 1752913]),
  (7, 3, [2, 5, 4090129]),
  (21, 1, [2, 19, 3229049]),
  (1, 22, [5843063]),
  (2, 11, [23, 508091]),
  (11, 2, [64273453]),
  (22, 1, [128546903]),
  (1, 23, [2, 2, 2, 3, 243461]),
  (23, 1, [2, 2, 2, 3, 3, 13, 29, 4951])]

theorem certificates_valid :
    ∀ t ∈ certificates, Certificate 5843041 t.1 t.2.1 t.2.2 := by
  norm_num [certificates, Certificate]

theorem certificates_cover (a u : ℕ) (ha : 0 < a) (hu : 0 < u)
    (hb : a*u ≤ 23) (hg : Nat.Coprime a u) :
    ∃ fs, (a,u,fs) ∈ certificates := by
  have ha23 : a ≤ 23 := by nlinarith
  have hu23 : u ≤ 23 := by nlinarith
  interval_cases a <;> interval_cases u <;>
    norm_num [Nat.Coprime, certificates] at *

/-- The new pointwise short-product/log-budget proposal is false at this prime. -/
theorem no_short_witness_budget23 (a u : ℕ) (ha : 0 < a) (hu : 0 < u)
    (hb : a*u ≤ 23) (hg : Nat.Coprime a u) :
    ¬ ShortWitness 5843041 a u := by
  obtain ⟨fs, hfs⟩ := certificates_cover a u ha hu hb hg
  exact certificate_excludes (certificates_valid (a,u,fs) hfs)

theorem counterexample_prime : Nat.Prime 5843041 := by norm_num

theorem target_residue : 5843041 % 840 = 1 := by norm_num

theorem logarithmic_boundary : 2^22 < (5843041 : ℕ) ∧ 5843041 ≤ 2^23 := by
  norm_num

/-- The counterexample is NOT a failure of the original Type II witness. -/
theorem full_witness :
    (7359 : ℕ) = 3*11*223 ∧ 7359 ∣ 5843041+5 ∧
    (7359+1) % (4*1*5) = 0 ∧
    4 * (1460960 : ℕ) * 10751195440 * 1707289835872 =
      5843041 * (1460960*10751195440 + 1460960*1707289835872 +
        10751195440*1707289835872) := by
  norm_num

#print axioms no_short_witness_budget23
#print axioms counterexample_prime
#print axioms certificates_valid
#print axioms full_witness

end OutcastsMathLab.Research.ShortProduct20261002
