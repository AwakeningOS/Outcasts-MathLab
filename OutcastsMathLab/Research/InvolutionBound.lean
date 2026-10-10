import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.GCD.Basic

/-!
# Dahan's involution bound (Lemma 4.2 of arXiv:2608.24035)

This module formalizes a KNOWN lemma; it is not a new result.

Dahan, Lemma 4.2: let `m ≥ 1` and let `T ⊆ (ℤ/4m)ˣ` be the set of residues of the
prime factors of `M` coprime to `4m`. If `M` has no divisor `≡ -1 (mod 4m)`, then
`|T| ≤ φ(4m)/2`. The proof uses the involution `ι(x) = -x⁻¹`, which has no fixed
point because `-1` is not a square modulo `4m` (reduce modulo 4).

The lemma is a necessary condition for the FAILURE of the Type II divisor criterion
(Dahan Theorem 3.9(ii), `s ∣ a p + u`, `s ≡ -1 (mod 4 a u)`) at a pair `(a, u)`,
with `M = a p + u` and `m = a u`. It says nothing about existence.

Main statements:
* `neg_one_ne_sq`: `-1` is not a square in `ZMod (4 * m)`.
* `card_le_half_of_fixedPointFree_involution`: pure counting, for any fixed-point-free
  involution-like injection `ι` with `T ∩ ι(T) = ∅`.
* `card_le_half_totient_of_no_neg_one_divisor`: the bound for any finite set `T` of
  unit residues each represented by a prime factor of `M`.
* `dahan_involution_bound`: the bound for Dahan's `T` (`primeResidues M (4 * m)`).
-/

namespace OutcastsMathLab.Research.InvolutionBound

/-- `-1` is not a square modulo `4 m`: reduce modulo `4`, where the squares are `0, 1`. -/
theorem neg_one_ne_sq (m : ℕ) (x : ZMod (4 * m)) : x ^ 2 ≠ -1 := by
  intro h
  have h4 : (4 : ℕ) ∣ 4 * m := dvd_mul_right 4 m
  have := congrArg (ZMod.castHom h4 (ZMod 4)) h
  rw [map_pow, map_neg, map_one] at this
  revert this
  generalize (ZMod.castHom h4 (ZMod 4)) x = y
  revert y
  decide

/-- Pure counting: if `ι` is injective and `T` is disjoint from its image, then
    `2 |T| ≤ |α|`. -/
theorem card_le_half_of_fixedPointFree_involution {α : Type*} [Fintype α] [DecidableEq α]
    (ι : α → α) (hι : Function.Injective ι) (T : Finset α)
    (hdisj : ∀ x ∈ T, ι x ∉ T) : 2 * T.card ≤ Fintype.card α := by
  have hd : Disjoint T (T.image ι) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx'
    exact hdisj y hy hx
  have h1 := Finset.card_le_univ (T.disjUnion (T.image ι) hd)
  rw [Finset.card_disjUnion, Finset.card_image_of_injective _ hι] at h1
  omega

/-- The involution `ι x = -x⁻¹` on the units of `ZMod (4 m)`. -/
def iota (m : ℕ) (x : (ZMod (4 * m))ˣ) : (ZMod (4 * m))ˣ := -x⁻¹

theorem iota_injective (m : ℕ) : Function.Injective (iota m) := by
  intro x y h
  unfold iota at h
  exact inv_injective (neg_injective h)

/-- `ι` has no fixed point, because a fixed point would be a square root of `-1`. -/
theorem iota_ne_self (m : ℕ) (x : (ZMod (4 * m))ˣ) : iota m x ≠ x := by
  intro h
  unfold iota at h
  have hv := congrArg Units.val h
  rw [Units.val_neg] at hv
  -- hv : -(↑x⁻¹) = ↑x
  have hsq : ((x : ZMod (4 * m))) ^ 2 = -1 := by
    have hmul := congrArg (fun z => (x : ZMod (4 * m)) * z) hv
    simp only [mul_neg, Units.mul_inv] at hmul
    rw [sq]
    exact hmul.symm
  exact neg_one_ne_sq m _ hsq

/-- The bound for any finite set `T` of unit residues, each the residue of some prime
    factor of `M`, when `M` has no divisor `≡ -1 (mod 4 m)`. -/
theorem card_le_half_totient_of_no_neg_one_divisor {m M : ℕ} (hm : 0 < m)
    (T : Finset (ZMod (4 * m))ˣ)
    (hT : ∀ x ∈ T, ∃ q : ℕ, q.Prime ∧ q ∣ M ∧ ((q : ZMod (4 * m)) = (x : ZMod (4 * m))))
    (h : ∀ d, d ∣ M → ¬ 4 * m ∣ d + 1) :
    2 * T.card ≤ Nat.totient (4 * m) := by
  have : NeZero (4 * m) := ⟨by omega⟩
  rw [← ZMod.card_units_eq_totient (4 * m)]
  apply card_le_half_of_fixedPointFree_involution (iota m) (iota_injective m) T
  intro x hx hιx
  obtain ⟨q₁, hq₁, hq₁M, hq₁x⟩ := hT x hx
  obtain ⟨q₂, hq₂, hq₂M, hq₂x⟩ := hT _ hιx
  -- the two primes are distinct, since their residues differ
  have hne : q₁ ≠ q₂ := by
    rintro rfl
    exact iota_ne_self m x (Units.ext (hq₂x.symm.trans hq₁x))
  have hdvd : q₁ * q₂ ∣ M :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hq₁ hq₂).mpr hne) hq₁M hq₂M
  -- and their product is `≡ -1`
  have hprod : ((q₁ * q₂ + 1 : ℕ) : ZMod (4 * m)) = 0 := by
    push_cast
    rw [hq₁x, hq₂x]
    unfold iota
    rw [Units.val_neg, mul_neg, Units.mul_inv]
    ring
  exact h _ hdvd ((ZMod.natCast_eq_zero_iff _ _).mp hprod)

theorem coprime_of_mem_filter {M n q : ℕ}
    (hq : q ∈ M.primeFactors.filter (fun q => Nat.Coprime q n)) : Nat.Coprime q n := by
  have h := Finset.mem_filter.mp hq
  exact h.2

/-- Dahan's `T`: the residues modulo `n` of the prime factors of `M` coprime to `n`,
    as units of `ZMod n`. -/
def primeResidues (M n : ℕ) : Finset (ZMod n)ˣ :=
  ((M.primeFactors.filter (fun q => Nat.Coprime q n)).attach).image
    (fun q => ZMod.unitOfCoprime q.1 (coprime_of_mem_filter q.2))

/-- Dahan Lemma 4.2: if `M` has no divisor `≡ -1 (mod 4 m)`, then
    `2 |T| ≤ φ(4 m)` for `T = primeResidues M (4 m)`. -/
theorem dahan_involution_bound {m M : ℕ} (hm : 0 < m)
    (h : ∀ d, d ∣ M → ¬ 4 * m ∣ d + 1) :
    2 * (primeResidues M (4 * m)).card ≤ Nat.totient (4 * m) := by
  apply card_le_half_totient_of_no_neg_one_divisor hm _ _ h
  intro x hx
  unfold primeResidues at hx
  obtain ⟨⟨q, hq⟩, -, rfl⟩ := Finset.mem_image.mp hx
  have hq' := Finset.mem_filter.mp hq
  obtain ⟨hprime, hdvd, -⟩ := Nat.mem_primeFactors.mp hq'.1
  exact ⟨q, hprime, hdvd, ZMod.coe_unitOfCoprime q hq'.2⟩

/-- Specialisation to Dahan's divisor criterion: if the pair `(a, u)` has no witness
    for `p`, the prime residues of `a p + u` modulo `4 a u` fill at most half of the units. -/
theorem no_witness_bound {p a u : ℕ} (ha : 0 < a) (hu : 0 < u)
    (h : ∀ s, s ∣ a * p + u → ¬ 4 * (a * u) ∣ s + 1) :
    2 * (primeResidues (a * p + u) (4 * (a * u))).card ≤ Nat.totient (4 * (a * u)) :=
  dahan_involution_bound (Nat.mul_pos ha hu) h

#print axioms neg_one_ne_sq
#print axioms card_le_half_of_fixedPointFree_involution
#print axioms iota_ne_self
#print axioms card_le_half_totient_of_no_neg_one_divisor
#print axioms dahan_involution_bound
#print axioms no_witness_bound

end OutcastsMathLab.Research.InvolutionBound
