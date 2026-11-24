/-
  StructureAndSharpThreshold20261125.lean

  Formal verification of 27 core theorems for the Outcasts Erdős–Straus
  collaborative thread (#157–#161):
    Part 1 (Theorem 1A core): Symmetry interval error & odd-truncation Bonferroni bound
    Part 2 (Theorem 2A/2B core): Window size bounds, 4×4 reciprocity sign product,
            11 mod 12 dominance, disjoint closed-set exclusion, complete iff mod-12
            classification (3 maximal patterns, fixing #157 2B(3) per #161(a)),
            and universal M_11 lock for multiple disjoint closed sets in W_p
    Part 3 (Theorem 3 core): Complete 8/9 exclusion of e = ℓ^i R^j for upper sources
            with ℓ ∣ x, #156 corollaries for ℓ = 13 and ℓ = 11, and prime-R witnesses
    Part 4 (Theorem 4 core): Sharp threshold 4*ℓ*s0*r ≥ (ℓ + s0)*p + 1 sharpening
            #147's p/ℓ bound, plus exact checks of #147/#159/#161 examples

  Toolchain: Lean 4.34.0 (pure Init, zero external dependencies, zero sorry,
             no native_decide, standard axioms only).
-/

namespace StructureAndSharpThreshold20261125

/-! ## Part 1: Theorem 1A core — Symmetry interval error & odd-truncation Bonferroni bound -/

/-- Exact symmetry interval error bound (#70/#73, used in Theorem 1A Brun pure sieve):
    For a symmetric root pair `a < b = d - 1 - a` in `[0, d-1]` and remainder `0 ≤ s < d`,
    the count `delta` of roots in `[0, s-1]` satisfies `|d * delta - 2 * s| < d`. -/
theorem sym_pair_error_lt (d a s : Nat) (h1 : a + 1 + a < d) (hs : s < d) :
    let b := d - 1 - a
    let delta : Int := (if a < s then 1 else 0) + (if b < s then 1 else 0)
    (-(d : Int) < (d : Int) * delta - 2 * (s : Int)) ∧
      ((d : Int) * delta - 2 * (s : Int) < (d : Int)) := by
  dsimp only
  by_cases ha : a < s <;> by_cases hb : d - 1 - a < s <;> simp [ha, hb] <;> omega

/-- Binomial coefficient definition for self-contained Bonferroni identity. -/
def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

/-- Alternating sum of binomial coefficients up to `r`. -/
def altBinomSum (m : Nat) : Nat → Int
  | 0 => (binom m 0 : Int)
  | r + 1 =>
    altBinomSum m r +
      (if (r + 1) % 2 = 0 then (binom m (r + 1) : Int) else -(binom m (r + 1) : Int))

theorem altBinomSum_eq (m r : Nat) (hm : 1 ≤ m) :
    altBinomSum m r =
      (if r % 2 = 0 then (binom (m - 1) r : Int) else -(binom (m - 1) r : Int)) := by
  induction r with
  | zero =>
    simp [altBinomSum, binom]
  | succ r ih =>
    rw [altBinomSum, ih]
    cases m with
    | zero => omega
    | succ m' =>
      simp only [Nat.add_sub_cancel, binom]
      by_cases h : r % 2 = 0
      · have h1 : (r + 1) % 2 ≠ 0 := by omega
        simp [h, h1]
        omega
      · have h1 : (r + 1) % 2 = 0 := by omega
        simp [h, h1]
        omega

/-- Bonferroni lower bound at odd truncation `2*k + 1`:
    For any `m ≥ 1`, the alternating sum up to any odd index `2*k + 1` is `≤ 0`. -/
theorem bonferroni_odd_nonpos (m k : Nat) (hm : 1 ≤ m) :
    altBinomSum m (2 * k + 1) ≤ 0 := by
  rw [altBinomSum_eq m (2 * k + 1) hm]
  simp

/-! ## Part 2: Theorem 2A & 2B — Window bounds, 4×4 reciprocity, tournament, dominance, and M_11 lock -/

private theorem le_of_pow_three_le {x y : Nat} (h : x ^ 3 ≤ y ^ 3) : x ≤ y := by
  by_cases hle : x ≤ y
  · exact hle
  · have hlt : y < x := Nat.lt_of_not_le hle
    have h2 : y * y < x * x := Nat.mul_lt_mul'' hlt hlt
    have h3 : y * y * y < x * x * x := Nat.mul_lt_mul'' h2 hlt
    have hy3 : y ^ 3 = y * y * y := by
      simp [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_assoc]
    have hx3 : x ^ 3 = x * x * x := by
      simp [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_assoc]
    omega

/-- Size sufficiency for `W_p = {q : q^3 ≤ p}`:
    `q^3 ≤ p ∧ b^3 ≤ p ∧ 0 < q ∧ 3 ≤ b → 3 * q * (b - 2)^2 < 3 * p`. -/
theorem window_Wp_edge_bound (p q b : Nat)
    (hq : q ^ 3 ≤ p) (hb : b ^ 3 ≤ p) (hqpos : 0 < q) (hb3 : 3 ≤ b) :
    3 * q * (b - 2) ^ 2 < 3 * p := by
  have hbm : b - 2 < b := by omega
  have hsq : (b - 2) ^ 2 < b ^ 2 := by
    have : (b - 2) * (b - 2) < b * b := Nat.mul_lt_mul'' hbm hbm
    simpa [Nat.pow_two] using this
  have hqb : q * (b - 2) ^ 2 < q * b ^ 2 := Nat.mul_lt_mul_of_pos_left hsq hqpos
  have hcube : (q * b ^ 2) ^ 3 ≤ p ^ 3 := by
    have h1 : (q * b ^ 2) ^ 3 = q ^ 3 * (b ^ 3 * b ^ 3) := by
      simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
      ac_rfl
    have hb2 : b ^ 3 * b ^ 3 ≤ p * p := Nat.mul_le_mul hb hb
    have h2 : q ^ 3 * (b ^ 3 * b ^ 3) ≤ p * (p * p) := Nat.mul_le_mul hq hb2
    have h3 : p * (p * p) = p ^ 3 := by
      simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
      ac_rfl
    omega
  have hle : q * b ^ 2 ≤ p := le_of_pow_three_le hcube
  have h3lt : 3 * (q * (b - 2) ^ 2) < 3 * p := by omega
  have : 3 * q * (b - 2) ^ 2 = 3 * (q * (b - 2) ^ 2) := Nat.mul_assoc 3 q ((b - 2) ^ 2)
  omega

/-- Size sufficiency for `W_3 = {q : q ≡ 3 (mod 4), q^3 ≤ 3*p}`:
    `q^3 ≤ 3*p ∧ b^3 ≤ 3*p ∧ 0 < q ∧ 3 ≤ b → q * (b - 2)^2 < 3 * p`. -/
theorem window_W3_edge_bound (p q b : Nat)
    (hq : q ^ 3 ≤ 3 * p) (hb : b ^ 3 ≤ 3 * p) (hqpos : 0 < q) (hb3 : 3 ≤ b) :
    q * (b - 2) ^ 2 < 3 * p := by
  have hbm : b - 2 < b := by omega
  have hsq : (b - 2) ^ 2 < b ^ 2 := by
    have : (b - 2) * (b - 2) < b * b := Nat.mul_lt_mul'' hbm hbm
    simpa [Nat.pow_two] using this
  have hqb : q * (b - 2) ^ 2 < q * b ^ 2 := Nat.mul_lt_mul_of_pos_left hsq hqpos
  have hcube : (q * b ^ 2) ^ 3 ≤ (3 * p) ^ 3 := by
    have h1 : (q * b ^ 2) ^ 3 = q ^ 3 * (b ^ 3 * b ^ 3) := by
      simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
      ac_rfl
    have hb2 : b ^ 3 * b ^ 3 ≤ (3 * p) * (3 * p) := Nat.mul_le_mul hb hb
    have h2 : q ^ 3 * (b ^ 3 * b ^ 3) ≤ (3 * p) * ((3 * p) * (3 * p)) := Nat.mul_le_mul hq hb2
    have h3 : (3 * p) * ((3 * p) * (3 * p)) = (3 * p) ^ 3 := by
      simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
      ac_rfl
    omega
  have hle : q * b ^ 2 ≤ 3 * p := le_of_pow_three_le hcube
  omega

def chi3 (x : Nat) : Int :=
  if x % 3 = 1 then 1 else if x % 3 = 2 then -1 else 0

def edgeSign (leg : Nat → Nat → Int) (q b : Nat) : Int :=
  if q % 4 = 3 then leg b q else chi3 b * leg b q

/-- Reciprocity sign product `ε(q, b) = (b / A(q)) * (q / A(b))` from quadratic reciprocity. -/
theorem reciprocity_sign_product
    (leg : Nat → Nat → Int) (q b : Nat)
    (hq4 : q % 4 = 1 ∨ q % 4 = 3) (hb4 : b % 4 = 1 ∨ b % 4 = 3)
    (hrec : leg b q * leg q b = if q % 4 = 3 ∧ b % 4 = 3 then -1 else 1) :
    edgeSign leg q b * edgeSign leg b q =
      if q % 4 = 3 ∧ b % 4 = 3 then -1
      else if q % 4 = 3 ∧ b % 4 = 1 then chi3 q
      else if q % 4 = 1 ∧ b % 4 = 3 then chi3 b
      else chi3 b * chi3 q := by
  unfold edgeSign
  rcases hq4 with hq4 | hq4 <;> rcases hb4 with hb4 | hb4
  · simp only [hq4, hb4, show (1 : Nat) ≠ 3 by decide, ↓reduceIte, and_self, false_and, and_false]
      at hrec ⊢
    have : chi3 b * leg b q * (chi3 q * leg q b) = (chi3 b * chi3 q) * (leg b q * leg q b) := by
      ac_rfl
    rw [this, hrec, Int.mul_one]
  · simp only [hq4, hb4, show (1 : Nat) ≠ 3 by decide, ↓reduceIte, false_and, true_and] at hrec ⊢
    have : chi3 b * leg b q * leg q b = chi3 b * (leg b q * leg q b) := by ac_rfl
    rw [this, hrec, Int.mul_one]
  · simp only [hq4, hb4, show (1 : Nat) ≠ 3 by decide, ↓reduceIte, and_false, true_and] at hrec ⊢
    have : leg b q * (chi3 q * leg q b) = chi3 q * (leg b q * leg q b) := by ac_rfl
    rw [this, hrec, Int.mul_one]
  · simp only [hq4, hb4, ↓reduceIte, and_self] at hrec ⊢
    exact hrec

/-- Universal antisymmetry for `q ≡ 11 (mod 12)`: `ε(q, b) = -1` for every odd `b`. -/
theorem mod11_universal_antisymmetry
    (leg : Nat → Nat → Int) (q b : Nat)
    (hq12 : q % 12 = 11) (hb4 : b % 4 = 1 ∨ b % 4 = 3)
    (hrec : leg b q * leg q b = if q % 4 = 3 ∧ b % 4 = 3 then -1 else 1) :
    edgeSign leg q b * edgeSign leg b q = -1 := by
  have hq3 : q % 3 = 2 := by omega
  have hq4 : q % 4 = 3 := by omega
  rw [reciprocity_sign_product leg q b (Or.inr hq4) hb4 hrec]
  rcases hb4 with hb4 | hb4
  · simp [hq4, hb4, chi3, hq3]
  · simp [hq4, hb4]

/-- One-step absorption into a closed set `C` containing a universally comparable vertex `q0 ∈ W`. -/
theorem dominance_one_step_absorption
    {V : Type} (E : V → V → Prop) (W C : V → Prop) (q0 : V)
    (hClosed : ∀ u v, C u → E u v → C v)
    (hq0C : C q0)
    (hComp : ∀ b, W b → b ≠ q0 → E q0 b ∨ E b q0) :
    ∀ b, W b → ¬ C b → E b q0 := by
  intro b hbW hbNotC
  have hne : b ≠ q0 := fun heq => hbNotC (heq ▸ hq0C)
  rcases hComp b hbW hne with hfwd | hback
  · exact absurd (hClosed q0 b hq0C hfwd) hbNotC
  · exact hback

/-- No closed set `C'` disjoint from `C` can intersect `W`. -/
theorem dominance_disjoint_closed_empty
    {V : Type} (E : V → V → Prop) (W C C' : V → Prop) (q0 : V)
    (hClosedC : ∀ u v, C u → E u v → C v)
    (hClosedC' : ∀ u v, C' u → E u v → C' v)
    (hDisj : ∀ v, ¬ (C v ∧ C' v))
    (hq0C : C q0)
    (hComp : ∀ b, W b → b ≠ q0 → E q0 b ∨ E b q0) :
    ∀ b, W b → ¬ C' b := by
  intro b hbW hbC'
  have hbNotC : ¬ C b := fun hbC => hDisj b ⟨hbC, hbC'⟩
  have hEdge : E b q0 :=
    dominance_one_step_absorption E W C q0 hClosedC hq0C hComp b hbW hbNotC
  have hq0C' : C' q0 := hClosedC' b q0 hbC' hEdge
  exact hDisj q0 ⟨hq0C, hq0C'⟩

/-- Tournament exclusion on `W_3`: no two disjoint closed sets can both intersect a tournament `W3`. -/
theorem tournament_disjoint_closed_exclusion
    {V : Type} (E : V → V → Prop) (W3 C1 C2 : V → Prop)
    (hClosed1 : ∀ u v, C1 u → E u v → C1 v)
    (hClosed2 : ∀ u v, C2 u → E u v → C2 v)
    (hDisj : ∀ v, ¬ (C1 v ∧ C2 v))
    (hTourn : ∀ u v, W3 u → W3 v → u ≠ v → E u v ∨ E v u) :
    ¬ ((∃ u, W3 u ∧ C1 u) ∧ (∃ v, W3 v ∧ C2 v)) := by
  rintro ⟨⟨u, huW, hu1⟩, ⟨v, hvW, hv2⟩⟩
  have hne : u ≠ v := fun heq => hDisj u ⟨hu1, heq ▸ hv2⟩
  rcases hTourn u v huW hvW hne with huv | hvu
  · exact hDisj v ⟨hClosed1 u v hu1 huv, hv2⟩
  · exact hDisj u ⟨hu1, hClosed2 v u hv2 hvu⟩

inductive Mod12 : Type
  | r1 | r5 | r7 | r11
  deriving DecidableEq

def epsPlus : Mod12 → Mod12 → Bool
  | .r1,  .r1  => true
  | .r1,  .r7  => true
  | .r5,  .r5  => true
  | .r5,  .r7  => true
  | .r7,  .r1  => true
  | .r7,  .r5  => true
  | _,    _    => false

structure Sub12 where
  h1  : Bool
  h5  : Bool
  h7  : Bool
  h11 : Bool
  deriving DecidableEq

def Sub12.mem (S : Sub12) : Mod12 → Bool
  | .r1  => S.h1
  | .r5  => S.h5
  | .r7  => S.h7
  | .r11 => S.h11

def Sub12.nonempty (S : Sub12) : Bool :=
  S.h1 || S.h5 || S.h7 || S.h11

def Sub12.subset (S T : Sub12) : Bool :=
  (!S.h1 || T.h1) && (!S.h5 || T.h5) && (!S.h7 || T.h7) && (!S.h11 || T.h11)

def allPlus (A B : Sub12) : Bool :=
  ([Mod12.r1, .r5, .r7, .r11]).all fun a =>
    ([Mod12.r1, .r5, .r7, .r11]).all fun b =>
      !(A.mem a && B.mem b) || epsPlus a b

def s1  : Sub12 := ⟨true,  false, false, false⟩
def s5  : Sub12 := ⟨false, true,  false, false⟩
def s7  : Sub12 := ⟨false, false, true,  false⟩
def s17 : Sub12 := ⟨true,  false, true,  false⟩
def s57 : Sub12 := ⟨false, true,  true,  false⟩
def s15 : Sub12 := ⟨true,  true,  false, false⟩

def inThreeMaximal (A B : Sub12) : Bool :=
  (A.subset s1  && B.subset s17) || (A.subset s17 && B.subset s1) ||
  (A.subset s5  && B.subset s57) || (A.subset s57 && B.subset s5) ||
  (A.subset s7  && B.subset s15) || (A.subset s15 && B.subset s7)

def allSub12 : List Sub12 :=
  [false, true].flatMap fun b1 =>
  [false, true].flatMap fun b5 =>
  [false, true].flatMap fun b7 =>
  [false, true].map     fun b11 =>
    ⟨b1, b5, b7, b11⟩

/-- Complete kernel-checked iff classification over all 256 pairs `(A, B)` (fixing #157 2B(3) per #161(a)):
    Two nonempty mod-12 subsets have all cross-signs `+1` iff they lie in one of the
    three maximal patterns `{1} vs {1,7}`, `{5} vs {5,7}`, or `{7} vs {1,5}`. -/
theorem mod12_disjoint_three_maximal_iff :
    allSub12.all (fun A => allSub12.all (fun B =>
      !(A.nonempty && B.nonempty) || (allPlus A B == inThreeMaximal A B))) = true := by
  decide

/-- Universal `M_11` lock for multiple disjoint closed subsets `S1, S2 ⊆ W`:
    Any universally comparable `q0 ∈ W` lies outside `S1 ∪ S2` and has a direct edge `E q0 s`
    to every `s ∈ S1 ∪ S2`. -/
theorem multi_sink_mod11_lock
    {V : Type} (E : V → V → Prop) (W S1 S2 : V → Prop) (q0 : V)
    (hSub1 : ∀ v, S1 v → W v) (hSub2 : ∀ v, S2 v → W v)
    (hClosed1 : ∀ u v, S1 u → W v → E u v → S1 v)
    (hClosed2 : ∀ u v, S2 u → W v → E u v → S2 v)
    (hDisj : ∀ v, ¬ (S1 v ∧ S2 v))
    (hNE1 : ∃ u, S1 u) (hNE2 : ∃ v, S2 v)
    (hq0W : W q0)
    (hComp : ∀ b, W b → b ≠ q0 → E q0 b ∨ E b q0) :
    (¬ S1 q0 ∧ ¬ S2 q0) ∧ ∀ s, (S1 s ∨ S2 s) → E q0 s := by
  have hnot1 : ¬ S1 q0 := by
    intro hq1
    rcases hNE2 with ⟨v, hv2⟩
    have hne : v ≠ q0 := fun heq => hDisj q0 ⟨hq1, heq ▸ hv2⟩
    rcases hComp v (hSub2 v hv2) hne with hfwd | hback
    · exact hDisj v ⟨hClosed1 q0 v hq1 (hSub2 v hv2) hfwd, hv2⟩
    · exact hDisj q0 ⟨hq1, hClosed2 v q0 hv2 hq0W hback⟩
  have hnot2 : ¬ S2 q0 := by
    intro hq2
    rcases hNE1 with ⟨u, hu1⟩
    have hne : u ≠ q0 := fun heq => hDisj q0 ⟨heq ▸ hu1, hq2⟩
    rcases hComp u (hSub1 u hu1) hne with hfwd | hback
    · exact hDisj u ⟨hu1, hClosed2 q0 u hq2 (hSub1 u hu1) hfwd⟩
    · exact hDisj q0 ⟨hClosed1 u q0 hu1 hq0W hback, hq2⟩
  refine ⟨⟨hnot1, hnot2⟩, ?_⟩
  intro s hs
  rcases hs with hs1 | hs2
  · have hne : s ≠ q0 := fun heq => hnot1 (heq ▸ hs1)
    rcases hComp s (hSub1 s hs1) hne with hfwd | hback
    · exact hfwd
    · exact absurd (hClosed1 s q0 hs1 hq0W hback) hnot1
  · have hne : s ≠ q0 := fun heq => hnot2 (heq ▸ hs2)
    rcases hComp s (hSub2 s hs2) hne with hfwd | hback
    · exact hfwd
    · exact absurd (hClosed2 s q0 hs2 hq0W hback) hnot2

/-! ## Part 3: Theorem 3 — Complete 8/9 exclusion of `e = ℓ^i R^j` for upper sources with `ℓ ∣ x` -/

theorem upper_ell_div_x_i0_j0 (p c : Nat) (hp : 1009 ≤ p) (hup : p < 3 * c) :
    ¬ (c ∣ 5) := by
  intro hd
  have hle : c ≤ 5 := Nat.le_of_dvd (by decide) hd
  omega

theorem upper_ell_div_x_i1_j0 (p c ell : Nat)
    (hp : 1009 ≤ p) (hup : p < 3 * c) (hell : ell ^ 2 < p) :
    ¬ (c ∣ 4 * ell + 1) := by
  intro hd
  have hle : c ≤ 4 * ell + 1 := Nat.le_of_dvd (by omega) hd
  by_cases h83 : ell ≤ 83
  · omega
  · have h84 : 84 ≤ ell := by omega
    have hsq : 84 * ell ≤ ell ^ 2 := by
      have : 84 * ell ≤ ell * ell := Nat.mul_le_mul_right ell h84
      simpa [Nat.pow_two] using this
    omega

theorem upper_ell_div_x_i0_j1 (p c ell R : Nat)
    (hp : 1009 ≤ p) (hup : p < 3 * c) (hell11 : 11 ≤ ell) (hell : ell ^ 2 < p)
    (hx : 4 * ell * R = p + c) :
    ¬ (c ∣ 4 * R + 1) := by
  rintro ⟨k, hk⟩
  have hkpos : 1 ≤ k := by
    by_cases h0 : k = 0
    · subst h0; simp at hk
    · omega
  have hmul : 4 * ell * R + ell = k * ell * c := by
    have h1 : ell * (4 * R + 1) = ell * (c * k) := congrArg (ell * ·) hk
    have hL : ell * (4 * R + 1) = 4 * ell * R + ell := by
      rw [Nat.mul_add, Nat.mul_one]
      have : ell * (4 * R) = 4 * ell * R := by ac_rfl
      omega
    have hR : ell * (c * k) = k * ell * c := by ac_rfl
    omega
  have hsub : (k * ell - 1) * c = p + ell := by
    have h1 : 1 ≤ k * ell := Nat.mul_le_mul hkpos (show 1 ≤ ell by omega)
    have h2 : k * ell * c = (k * ell - 1) * c + c := by
      calc k * ell * c = (k * ell - 1 + 1) * c := by rw [Nat.sub_add_cancel h1]
        _ = (k * ell - 1) * c + c := by rw [Nat.add_mul, Nat.one_mul]
    omega
  have hke10 : 10 ≤ k * ell - 1 := by
    have : 11 ≤ k * ell := by
      calc 11 = 1 * 11 := by decide
        _ ≤ k * ell := Nat.mul_le_mul hkpos hell11
    omega
  have h10c : 10 * c ≤ p + ell := by
    calc 10 * c ≤ (k * ell - 1) * c := Nat.mul_le_mul_right c hke10
      _ = p + ell := hsub
  have hell_lt_p : ell < p := by
    have : ell ≤ ell ^ 2 := by
      have : ell * 1 ≤ ell * ell := Nat.mul_le_mul_left ell (by omega)
      simpa [Nat.pow_two] using this
    omega
  omega

theorem upper_ell_div_x_i1_j1 (p c x : Nat)
    (hp24 : p % 24 = 1) (hc4 : c % 4 = 3) (hup : p < 3 * c)
    (hx : 4 * x = p + c) :
    ¬ (c ∣ 4 * x + 1) := by
  rintro ⟨k, hk⟩
  have hk2 : 2 ≤ k := by
    by_cases h0 : k = 0
    · subst h0; simp at hk
    · by_cases h1 : k = 1
      · subst h1; simp at hk; omega
      · omega
  have hsub : (k - 1) * c = p + 1 := by
    have h1 : k * c = (k - 1) * c + c := by
      calc k * c = (k - 1 + 1) * c := by rw [Nat.sub_add_cancel (by omega)]
        _ = (k - 1) * c + c := by rw [Nat.add_mul, Nat.one_mul]
    have hk' : 4 * x + 1 = k * c := by rw [Nat.mul_comm c k] at hk; exact hk
    omega
  have hkm : k - 1 = 1 ∨ k - 1 = 2 ∨ k - 1 = 3 := by
    by_cases hlt4 : k - 1 < 4
    · omega
    · have h4 : 4 ≤ k - 1 := by omega
      have : 4 * c ≤ p + 1 := by
        calc 4 * c ≤ (k - 1) * c := Nat.mul_le_mul_right c h4
          _ = p + 1 := hsub
      omega
  rcases hkm with h1 | h2 | h3
  · rw [h1, Nat.one_mul] at hsub; omega
  · rw [h2] at hsub; omega
  · rw [h3] at hsub; omega

def chiNeg1 (n : Nat) : Int := if n % 4 = 1 then 1 else -1
def chi2 (n : Nat) : Int := if n % 8 = 1 ∨ n % 8 = 7 then 1 else -1

theorem upper_ell_div_x_i2_j1_mod8_lock
    (p c ell R k a hp' : Nat)
    (hp8 : p % 8 = 1) (hc4 : c % 4 = 3) (hup : p < 3 * c)
    (hell_odd : ell % 2 = 1) (hodd : hp' % 2 = 1) (hge : ell ≤ hp')
    (hx : 4 * ell * R = p + c)
    (hwit : 4 * ell ^ 2 * R + 1 = k * c)
    (hfac : k - ell = 2 ^ a * hp') :
    a = 1 ∧ ell % 4 = 1 ∧ chiNeg1 hp' = -chi2 ell := by
  have hk_eq : ell * (p + c) + 1 = k * c := by
    have h1 : 4 * ell ^ 2 * R = ell * (4 * ell * R) := by
      simp only [Nat.pow_two]; ac_rfl
    rw [h1, hx] at hwit
    exact hwit
  have hkle : ell < k := by
    by_cases hgt : ell < k
    · exact hgt
    · have hkc : k * c ≤ ell * c := Nat.mul_le_mul_right c (by omega)
      have hdist : ell * (p + c) = ell * p + ell * c := Nat.mul_add ell p c
      omega
  have hhc : (k - ell) * c = ell * p + 1 := by
    have h1 : k * c = (k - ell) * c + ell * c := by
      calc k * c = (k - ell + ell) * c := by rw [Nat.sub_add_cancel (by omega)]
        _ = (k - ell) * c + ell * c := by rw [Nat.add_mul]
    have h2 : ell * (p + c) = ell * p + ell * c := Nat.mul_add ell p c
    omega
  have hh_le : k - ell ≤ 3 * ell := by
    by_cases hle : k - ell ≤ 3 * ell
    · exact hle
    · have h1 : 3 * ell + 1 ≤ k - ell := by omega
      have h2 : (3 * ell + 1) * c ≤ ell * p + 1 := by
        calc (3 * ell + 1) * c ≤ (k - ell) * c := Nat.mul_le_mul_right c h1
          _ = ell * p + 1 := hhc
      have h3 : (3 * ell + 1) * c = ell * (3 * c) + c := by
        rw [Nat.add_mul, Nat.one_mul]; ac_rfl
      have h4 : ell * p + ell ≤ ell * (3 * c) := by
        have : p + 1 ≤ 3 * c := by omega
        have := Nat.mul_le_mul_left ell this
        rw [Nat.mul_add, Nat.mul_one] at this
        exact this
      omega
  have ha1 : 1 ≤ a := by
    by_cases ha0 : a = 0
    · rw [ha0, Nat.pow_zero, Nat.one_mul] at hfac
      rw [hfac] at hhc
      have hL : (hp' * c) % 2 = 1 := by
        rw [Nat.mul_mod, hodd, show c % 2 = 1 by omega]
      have hR : (ell * p + 1) % 2 = 0 := by
        rw [Nat.add_mod, Nat.mul_mod, hell_odd, show p % 2 = 1 by omega]
      omega
    · omega
  have ha_eq : a = 1 := by
    by_cases ha_is1 : a = 1
    · exact ha_is1
    · have ha2 : 2 ≤ a := by omega
      have hpow : 4 ≤ 2 ^ a := by
        calc 4 = 2 ^ 2 := by decide
          _ ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) ha2
      have h4ell : 4 * ell ≤ k - ell := by
        rw [hfac]
        exact Nat.mul_le_mul hpow hge
      omega
  rw [ha_eq, Nat.pow_one] at hfac
  have h2hpc : 2 * hp' * c = ell * p + 1 := by rw [← hfac]; exact hhc
  have hmod8 : (2 * hp' * c) % 8 = (ell * p + 1) % 8 := congrArg (· % 8) h2hpc
  have hp_mod : (ell * p + 1) % 8 = (ell + 1) % 8 := by
    have hpdiv : p = 8 * (p / 8) + 1 := by omega
    have h1 : ell * p + 1 = 8 * (ell * (p / 8)) + (ell + 1) := by
      calc ell * p + 1 = ell * (8 * (p / 8) + 1) + 1 := by rw [← hpdiv]
        _ = ell * (8 * (p / 8)) + ell * 1 + 1 := by rw [Nat.mul_add]
        _ = 8 * (ell * (p / 8)) + (ell + 1) := by
          rw [Nat.mul_one, Nat.add_assoc]
          have : ell * (8 * (p / 8)) = 8 * (ell * (p / 8)) := by ac_rfl
          omega
    omega
  have hc_mod : (2 * hp' * c) % 8 = (6 * (hp' % 4)) % 8 := by
    have hcdiv : c = 4 * (c / 4) + 3 := by omega
    have hhpdiv : hp' = 4 * (hp' / 4) + hp' % 4 := by omega
    have h1 : 2 * hp' * c = 8 * (hp' * (c / 4) + 3 * (hp' / 4)) + 6 * (hp' % 4) := by
      have hm1 : 2 * hp' * c = 2 * hp' * (4 * (c / 4)) + 2 * hp' * 3 := by
        calc 2 * hp' * c = 2 * hp' * (4 * (c / 4) + 3) := by rw [← hcdiv]
          _ = 2 * hp' * (4 * (c / 4)) + 2 * hp' * 3 := by rw [Nat.mul_add]
      have hm2 : 2 * hp' * (4 * (c / 4)) = 8 * (hp' * (c / 4)) := by
        have : 2 * hp' * (4 * (c / 4)) = (2 * 4) * (hp' * (c / 4)) := by ac_rfl
        simpa using this
      have hm3 : 2 * hp' * 3 = 6 * hp' := by omega
      have hm4 : 6 * hp' = 8 * (3 * (hp' / 4)) + 6 * (hp' % 4) := by
        calc 6 * hp' = 6 * (4 * (hp' / 4) + hp' % 4) := by rw [← hhpdiv]
          _ = 6 * (4 * (hp' / 4)) + 6 * (hp' % 4) := by rw [Nat.mul_add]
          _ = 8 * (3 * (hp' / 4)) + 6 * (hp' % 4) := by omega
      omega
    omega
  have hlock : (6 * (hp' % 4)) % 8 = (ell + 1) % 8 := by omega
  refine ⟨ha_eq, ?_, ?_⟩
  · omega
  · unfold chiNeg1 chi2
    have hcase : (ell % 8 = 1 ∧ hp' % 4 = 3) ∨ (ell % 8 = 5 ∧ hp' % 4 = 1) := by omega
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

theorem upper_ell_div_x_i2_j1_contradiction
    (ell hp' : Nat)
    (hlock : chiNeg1 hp' = -chi2 ell)
    (hrec_conseq : chiNeg1 hp' = chi2 ell) : False := by
  unfold chi2 at hlock hrec_conseq
  split at hlock <;> simp_all

theorem upper_ell_div_x_j2_reductions (p c ell R : Nat) (hx : 4 * ell * R = p + c) :
    (c ∣ 4 * R ^ 2 + 1 → c ∣ p ^ 2 + 4 * ell ^ 2) ∧
    (c ∣ 4 * (ell * R) ^ 2 + 1 → c ∣ p ^ 2 + 4) ∧
    (c ∣ 4 * ell * R ^ 2 + 1 → c ∣ p ^ 2 + 4 * ell) := by
  have hsq : (p + c) ^ 2 = p ^ 2 + c * (2 * p + c) := by
    simp only [Nat.pow_two]
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    have : p * c + (c * p + c * c) = c * (2 * p + c) := by
      rw [Nat.mul_add, Nat.mul_comm p c]
      have : c * (2 * p) = c * p + c * p := by
        rw [show 2 * p = p + p by omega, Nat.mul_add]
      omega
    omega
  have h16 : 16 * ell ^ 2 * R ^ 2 = (p + c) ^ 2 := by
    have h0 : (4 * ell * R) ^ 2 = (p + c) ^ 2 := congrArg (· ^ 2) hx
    have hL : (4 * ell * R) ^ 2 = 16 * ell ^ 2 * R ^ 2 := by
      simp only [Nat.pow_two]
      have : 4 * ell * R * (4 * ell * R) = (4 * 4) * (ell * ell) * (R * R) := by ac_rfl
      simpa using this
    omega
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨k, hk⟩
    have hmul : 4 * ell ^ 2 * (4 * R ^ 2 + 1) = (p + c) ^ 2 + 4 * ell ^ 2 := by
      rw [Nat.mul_add, Nat.mul_one]
      have h1 : 4 * ell ^ 2 * (4 * R ^ 2) = 16 * ell ^ 2 * R ^ 2 := by
        have : 4 * ell ^ 2 * (4 * R ^ 2) = (4 * 4) * ell ^ 2 * R ^ 2 := by ac_rfl
        simpa using this
      rw [h1, h16]
    have hd : c ∣ (p + c) ^ 2 + 4 * ell ^ 2 := by
      refine ⟨4 * ell ^ 2 * k, ?_⟩
      rw [← hmul, hk]; ac_rfl
    rw [hsq] at hd
    have hc_part : c ∣ c * (2 * p + c) := ⟨2 * p + c, rfl⟩
    have hrew : p ^ 2 + c * (2 * p + c) + 4 * ell ^ 2 =
        (p ^ 2 + 4 * ell ^ 2) + c * (2 * p + c) := by omega
    rw [hrew] at hd
    exact (Nat.dvd_add_left hc_part).mp hd
  · rintro ⟨k, hk⟩
    have hmul : 4 * (4 * (ell * R) ^ 2 + 1) = (p + c) ^ 2 + 4 := by
      rw [Nat.mul_add, Nat.mul_one]
      have h1 : 4 * (4 * (ell * R) ^ 2) = 16 * ell ^ 2 * R ^ 2 := by
        have : 4 * (4 * (ell * R) ^ 2) = (4 * 4) * ell ^ 2 * R ^ 2 := by
          simp only [Nat.pow_two]; ac_rfl
        simpa using this
      rw [h1, h16]
    have hd : c ∣ (p + c) ^ 2 + 4 := by
      refine ⟨4 * k, ?_⟩
      rw [← hmul, hk]; ac_rfl
    rw [hsq] at hd
    have hc_part : c ∣ c * (2 * p + c) := ⟨2 * p + c, rfl⟩
    have hrew : p ^ 2 + c * (2 * p + c) + 4 = (p ^ 2 + 4) + c * (2 * p + c) := by omega
    rw [hrew] at hd
    exact (Nat.dvd_add_left hc_part).mp hd
  · rintro ⟨k, hk⟩
    have hmul : 4 * ell * (4 * ell * R ^ 2 + 1) = (p + c) ^ 2 + 4 * ell := by
      rw [Nat.mul_add, Nat.mul_one]
      have h1 : 4 * ell * (4 * ell * R ^ 2) = 16 * ell ^ 2 * R ^ 2 := by
        have : 4 * ell * (4 * ell * R ^ 2) = (4 * 4) * ell ^ 2 * R ^ 2 := by
          simp only [Nat.pow_two]; ac_rfl
        simpa using this
      rw [h1, h16]
    have hd : c ∣ (p + c) ^ 2 + 4 * ell := by
      refine ⟨4 * ell * k, ?_⟩
      rw [← hmul, hk]; ac_rfl
    rw [hsq] at hd
    have hc_part : c ∣ c * (2 * p + c) := ⟨2 * p + c, rfl⟩
    have hrew : p ^ 2 + c * (2 * p + c) + 4 * ell =
        (p ^ 2 + 4 * ell) + c * (2 * p + c) := by omega
    rw [hrew] at hd
    exact (Nat.dvd_add_left hc_part).mp hd

theorem cor_156_ell13_general (p q : Nat) (h1 : q ∣ p + 39) (h2 : q ∣ p ^ 2 + 52) :
    q ∣ 1573 := by
  have hz1 : (q : Int) ∣ (p : Int) + 39 := Int.ofNat_dvd.mpr h1
  have hz2 : (q : Int) ∣ (p : Int) ^ 2 + 52 := Int.ofNat_dvd.mpr h2
  have hmul : (q : Int) ∣ ((p : Int) + 39) * ((p : Int) - 39) := Int.dvd_mul_of_dvd_left hz1
  have hdiff : (q : Int) ∣ ((p : Int) ^ 2 + 52) - ((p : Int) + 39) * ((p : Int) - 39) :=
    Int.dvd_sub hz2 hmul
  have hid : ((p : Int) ^ 2 + 52) - ((p : Int) + 39) * ((p : Int) - 39) = (1573 : Nat) := by
    have : ((p : Int) + 39) * ((p : Int) - 39) = (p : Int) * (p : Int) - 1521 := by
      rw [Int.add_mul, Int.mul_sub, Int.mul_sub]
      omega
    have hp2 : (p : Int) ^ 2 = (p : Int) * (p : Int) := by simp [Int.pow_succ]
    omega
  rw [hid] at hdiff
  exact Int.ofNat_dvd.mp hdiff

theorem cor_156_ell11_general (p q : Nat) (h1 : q ∣ p + 11) (h2 : q ∣ p ^ 2 + 44) :
    q ∣ 165 := by
  have hz1 : (q : Int) ∣ (p : Int) + 11 := Int.ofNat_dvd.mpr h1
  have hz2 : (q : Int) ∣ (p : Int) ^ 2 + 44 := Int.ofNat_dvd.mpr h2
  have hmul : (q : Int) ∣ ((p : Int) + 11) * ((p : Int) - 11) := Int.dvd_mul_of_dvd_left hz1
  have hdiff : (q : Int) ∣ ((p : Int) ^ 2 + 44) - ((p : Int) + 11) * ((p : Int) - 11) :=
    Int.dvd_sub hz2 hmul
  have hid : ((p : Int) ^ 2 + 44) - ((p : Int) + 11) * ((p : Int) - 11) = (165 : Nat) := by
    have : ((p : Int) + 11) * ((p : Int) - 11) = (p : Int) * (p : Int) - 121 := by
      rw [Int.add_mul, Int.mul_sub, Int.mul_sub]
      omega
    have hp2 : (p : Int) ^ 2 = (p : Int) * (p : Int) := by simp [Int.pow_succ]
    omega
  rw [hid] at hdiff
  exact Int.ofNat_dvd.mp hdiff

theorem witness_295129 :
    4 * 245113 * 105556 * 694174204120892 =
      295129 * (245113 * 105556 + 245113 * 694174204120892 + 105556 * 694174204120892) := by
  decide

theorem witness_376009 :
    4 * 160171 * 227546 * 1245829606731754 =
      376009 * (160171 * 227546 + 160171 * 1245829606731754 + 227546 * 1245829606731754) := by
  decide

/-! ## Part 4: Theorem 4 — Sharp threshold `4 * ell * s0 * r ≥ (ell + s0) * p + 1` (#147 sharpening) -/

/-- Core parameter lock for Theorem 4 via the nonnegative split
    `h*s*(ell + s0) - ell*s0*(h + alpha) = h*ell*(s - s0) + s0*(h*s - ell*alpha)`. -/
theorem upper_sharp_threshold_lock
    (p ell s0 h alpha beta s r : Nat)
    (hell11 : 11 ≤ ell) (hell2 : ell ^ 2 < p)
    (hs0_le : 3 * s0 ≤ ell + 2) (hs0_pos : 1 ≤ s0)
    (hh : ell ≤ h) (halpha_lo : s0 ≤ alpha) (halpha_hi : alpha ≤ s) (hs_hi : s ≤ ell + 1)
    (hbeta_lo : 1 ≤ beta) (hbeta_hi : beta ≤ s)
    (heq : 4 * h * s * r = (h + alpha) * p + beta)
    (hthr : (ell + s0) * p + 1 ≤ 4 * ell * s0 * r) :
    h = ell ∧ alpha = s0 ∧ s = s0 := by
  have hmul_eq : 4 * ell * s0 * r * (h * s) = ell * s0 * ((h + alpha) * p + beta) := by
    have h1 : ell * s0 * (4 * h * s * r) = ell * s0 * ((h + alpha) * p + beta) :=
      congrArg (ell * s0 * ·) heq
    have h2 : 4 * ell * s0 * r * (h * s) = ell * s0 * (4 * h * s * r) := by ac_rfl
    rw [h2]; exact h1
  have hmul_le : h * s * ((ell + s0) * p + 1) ≤ ell * s0 * ((h + alpha) * p + beta) := by
    have h1 : ((ell + s0) * p + 1) * (h * s) ≤ 4 * ell * s0 * r * (h * s) :=
      Nat.mul_le_mul_right (h * s) hthr
    rw [Nat.mul_comm] at h1
    omega
  have hL : h * s * ((ell + s0) * p + 1) = (h * s * (ell + s0)) * p + h * s := by
    rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc]
  have hR : ell * s0 * ((h + alpha) * p + beta) =
      (ell * s0 * (h + alpha)) * p + ell * s0 * beta := by
    rw [Nat.mul_add, ← Nat.mul_assoc]
  have hineq :
      (h * s * (ell + s0)) * p + h * s ≤ (ell * s0 * (h + alpha)) * p + ell * s0 * beta := by
    omega
  have hs_ge_s0 : s0 ≤ s := Nat.le_trans halpha_lo halpha_hi
  have hhs_ge : ell * alpha ≤ h * s := Nat.mul_le_mul hh halpha_hi
  have hcoeff :
      h * s * (ell + s0) =
        ell * s0 * (h + alpha) + h * ell * (s - s0) + s0 * (h * s - ell * alpha) := by
    have h1 : h * s * (ell + s0) = h * s * ell + h * s * s0 := Nat.mul_add (h * s) ell s0
    have h2 : ell * s0 * (h + alpha) = ell * s0 * h + ell * s0 * alpha :=
      Nat.mul_add (ell * s0) h alpha
    have h3 : h * ell * (s - s0) + ell * s0 * h = h * s * ell := by
      have : h * ell * (s - s0) + h * ell * s0 = h * ell * s := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hs_ge_s0]
      have ha : ell * s0 * h = h * ell * s0 := by ac_rfl
      have hb : h * ell * s = h * s * ell := by ac_rfl
      omega
    have h4 : s0 * (h * s - ell * alpha) + ell * s0 * alpha = h * s * s0 := by
      have : s0 * (h * s - ell * alpha) + s0 * (ell * alpha) = s0 * (h * s) := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hhs_ge]
      have ha : ell * s0 * alpha = s0 * (ell * alpha) := by ac_rfl
      have hb : s0 * (h * s) = h * s * s0 := by ac_rfl
      omega
    omega
  have hmain : (h * ell * (s - s0) + s0 * (h * s - ell * alpha)) * p + h * s ≤ ell * s0 * beta := by
    have hmul_p : (h * s * (ell + s0)) * p =
        (ell * s0 * (h + alpha)) * p +
          (h * ell * (s - s0) + s0 * (h * s - ell * alpha)) * p := by
      rw [hcoeff, Nat.add_assoc, Nat.add_mul]
    omega
  have hs_eq : s = s0 := by
    by_cases hgt : s0 < s
    · have hs1 : 1 ≤ s - s0 := by omega
      have hterm1 : h * ell * p ≤ (h * ell * (s - s0) + s0 * (h * s - ell * alpha)) * p := by
        have : h * ell ≤ h * ell * (s - s0) := by
          calc h * ell = h * ell * 1 := (Nat.mul_one _).symm
            _ ≤ h * ell * (s - s0) := Nat.mul_le_mul_left _ hs1
        exact Nat.mul_le_mul_right p (Nat.le_trans this (Nat.le_add_right _ _))
      have hell_p : ell * (ell ^ 2) < h * ell * p := by
        have h1 : ell * ell ≤ h * ell := Nat.mul_le_mul_right ell hh
        have h2 : ell ^ 2 * ell ^ 2 < ell ^ 2 * p := by
          have hpos : 0 < ell ^ 2 := by
            have : 0 < ell * ell := Nat.mul_pos (by omega) (by omega)
            simpa [Nat.pow_two] using this
          exact Nat.mul_lt_mul_of_pos_left hell2 hpos
        have h3 : ell ^ 2 * p ≤ h * ell * p := by
          have : ell ^ 2 ≤ h * ell := by simpa [Nat.pow_two] using h1
          exact Nat.mul_le_mul_right p this
        have h4 : ell * ell ^ 2 ≤ ell ^ 2 * ell ^ 2 := by
          have : ell ≤ ell ^ 2 := by
            have : ell * 1 ≤ ell * ell := Nat.mul_le_mul_left ell (by omega)
            simpa [Nat.pow_two] using this
          exact Nat.mul_le_mul_right (ell ^ 2) this
        omega
      have hs0s_lt : s0 * s < ell ^ 2 := by
        have h3s : 3 * (s0 * s) ≤ (ell + 2) * (ell + 1) := by
          have : 3 * s0 * s ≤ (ell + 2) * (ell + 1) := Nat.mul_le_mul hs0_le hs_hi
          rw [Nat.mul_assoc] at this
          exact this
        have hquad : (ell + 2) * (ell + 1) < 3 * ell ^ 2 := by
          have h1 : (ell + 2) * (ell + 1) = ell ^ 2 + 3 * ell + 2 := by
            simp only [Nat.pow_two]
            rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
            omega
          have h2 : 3 * ell + 2 < 2 * ell ^ 2 := by
            have : 11 * ell ≤ ell ^ 2 := by
              have : 11 * ell ≤ ell * ell := Nat.mul_le_mul_right ell hell11
              simpa [Nat.pow_two] using this
            omega
          omega
        omega
      have hrhs_lt : ell * s0 * beta < ell * ell ^ 2 := by
        have h1 : ell * s0 * beta ≤ ell * s0 * s := Nat.mul_le_mul_left (ell * s0) hbeta_hi
        have h2 : ell * (s0 * s) < ell * ell ^ 2 := Nat.mul_lt_mul_of_pos_left hs0s_lt (by omega)
        have h3 : ell * s0 * s = ell * (s0 * s) := Nat.mul_assoc ell s0 s
        omega
      omega
    · omega
  have halpha_eq : alpha = s0 := by omega
  have hh_eq : h = ell := by
    by_cases hgt : ell < h
    · have hdiff : s0 ≤ h * s - ell * alpha := by
        rw [hs_eq, halpha_eq]
        have : (ell + 1) * s0 ≤ h * s0 := Nat.mul_le_mul_right s0 (by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      have hterm2 : s0 * s0 * p ≤ (h * ell * (s - s0) + s0 * (h * s - ell * alpha)) * p := by
        have h1 : s0 * s0 ≤ s0 * (h * s - ell * alpha) := Nat.mul_le_mul_left s0 hdiff
        exact Nat.mul_le_mul_right p (Nat.le_trans h1 (Nat.le_add_left _ _))
      have hell_lt_p : ell < p := by
        have : ell ≤ ell ^ 2 := by
          have : ell * 1 ≤ ell * ell := Nat.mul_le_mul_left ell (by omega)
          simpa [Nat.pow_two] using this
        omega
      have hrhs : ell * s0 * beta ≤ ell * (s0 * s0) := by
        have h1 : beta ≤ s0 := by omega
        have h2 : ell * s0 * beta ≤ ell * s0 * s0 := Nat.mul_le_mul_left (ell * s0) h1
        have h3 : ell * s0 * s0 = ell * (s0 * s0) := Nat.mul_assoc ell s0 s0
        omega
      have hcmp : ell * (s0 * s0) < s0 * s0 * p := by
        have hpos : 0 < s0 * s0 := Nat.mul_pos hs0_pos hs0_pos
        have : s0 * s0 * ell < s0 * s0 * p := Nat.mul_lt_mul_of_pos_left hell_lt_p hpos
        rw [Nat.mul_comm ell (s0 * s0)]
        exact this
      omega
    · omega
  exact ⟨hh_eq, halpha_eq, hs_eq⟩

theorem upper_sharp_threshold_strict_impossible
    (p ell s0 h alpha s r : Nat)
    (hell11 : 11 ≤ ell) (hell2 : ell ^ 2 < p)
    (hs0_le : 3 * s0 ≤ ell + 2) (hs0_pos : 1 ≤ s0)
    (hh : ell ≤ h) (halpha_lo : s0 ≤ alpha) (halpha_hi : alpha ≤ s) (hs_hi : s ≤ ell + 1)
    (heq : 4 * h * s * r = (h + alpha) * p + 1)
    (hstrict : (ell + s0) * p + 1 < 4 * ell * s0 * r) :
    False := by
  have hlock := upper_sharp_threshold_lock p ell s0 h alpha 1 s r
    hell11 hell2 hs0_le hs0_pos hh halpha_lo halpha_hi hs_hi (by decide) (by omega) heq (by omega)
  rcases hlock with ⟨rfl, rfl, rfl⟩
  omega

theorem sat_40609_equality : 4 * 11 * 4 * 3461 = (11 + 4) * 40609 + 1 := by decide
theorem witness_1129_compositeR : 4 * 539 + 1 = 3 * 719 ∧ 462 * 462 % 539 = 0 := by decide
theorem rescue_236807209_307 :
    (236807209 + 39 * 49 * 49) % (4 * 307) = 0 ∧
    ((236807209 + 307) / 4 + 1) % 307 = 0 := by decide

#print axioms sym_pair_error_lt
#print axioms bonferroni_odd_nonpos
#print axioms window_Wp_edge_bound
#print axioms window_W3_edge_bound
#print axioms reciprocity_sign_product
#print axioms mod11_universal_antisymmetry
#print axioms dominance_one_step_absorption
#print axioms dominance_disjoint_closed_empty
#print axioms tournament_disjoint_closed_exclusion
#print axioms mod12_disjoint_three_maximal_iff
#print axioms multi_sink_mod11_lock
#print axioms upper_ell_div_x_i0_j0
#print axioms upper_ell_div_x_i1_j0
#print axioms upper_ell_div_x_i0_j1
#print axioms upper_ell_div_x_i1_j1
#print axioms upper_ell_div_x_i2_j1_mod8_lock
#print axioms upper_ell_div_x_i2_j1_contradiction
#print axioms upper_ell_div_x_j2_reductions
#print axioms cor_156_ell13_general
#print axioms cor_156_ell11_general
#print axioms witness_295129
#print axioms witness_376009
#print axioms upper_sharp_threshold_lock
#print axioms upper_sharp_threshold_strict_impossible
#print axioms sat_40609_equality
#print axioms witness_1129_compositeR
#print axioms rescue_236807209_307

end StructureAndSharpThreshold20261125
