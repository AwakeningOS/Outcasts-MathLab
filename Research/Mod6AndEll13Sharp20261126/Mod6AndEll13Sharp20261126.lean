/-
  Mod6AndEll13Sharp20261126.lean
  Standalone Lean 4 (v4.34.0, pure Init, zero external imports, no sorry/admit/axiom/native_decide)
  Formalizing:
    1. General Type I unit-fraction soundness & Theorem 4 equality witness e = s0^2 * r
       and closed-form decomposition 4/p = 1/(s0*r) + 1/(ell*r) + 1/(p*ell*s0*r) (#163, #164 §1)
    2. General beta = 1 deduction from gcd(alpha, beta) = 1 and beta | alpha, plus hc = alpha*p + beta
    3. Parity impossibility of Theorem 4 equality for ell ≡ 1 (mod 6) (#164 §1)
    4. Universal mod-8 lock (h + alpha + beta) % 8 = (4 * h * s) % 8 for p ≡ 1 (mod 8) and odd r
    5. Theorem 5A: Universal zero-free bound (ell + 4) * r >= p (s != ell) for ALL ell ≡ 1 (mod 6)
    6. Theorem 5B: Complete classification for ell = 13 on 408 * r >= 23 * p + 1 (s != 13):
       - QR-cofactor branch uniquely forces (s, alpha, beta, h) = (6, 6, 1, 17), 408*r = 23*p + 1, 17 | p + 3
       - s = 17 QNR branch eliminates j = 0, 1 and reduces j = 2 to c | p^2 + 68
       - Explicit prime counterexamples p = 128051449, 123297007849, 250067982481 with 408*r > 23*p + 1
    7. #163 transfer lemma (17 | p + 3 => 13 -15-> 17 and d = 5) and #164 §3 reachability of 14731
-/

/-! ### Section 1: Type I Soundness, Theorem 4 Equality Witness, and Helper Reductions -/

/-- General Type I algebraic soundness:
    Whenever `4 * x = p + c`, `x * x = e * e'`, and `4 * e + 1 = m * c` (all positive),
    setting `y = m * e' - x` and `z = p * (m * x - e)` yields positive integers satisfying
    `4 * x * y * z = p * (x * y + x * z + y * z)`. -/
theorem type1_unit_fraction_sound
    (p c x e e' m : Nat)
    (hp : 0 < p) (hc : 0 < c) (he : 0 < e) (he' : 0 < e')
    (hx : 4 * x = p + c) (hxx : x * x = e * e') (hm : 4 * e + 1 = m * c) :
    let y := m * e' - x
    let z := p * (m * x - e)
    0 < y ∧ 0 < z ∧ 4 * x * y * z = p * (x * y + x * z + y * z) := by
  have hm_pos : 0 < m := by
    by_cases h0 : m = 0
    · subst h0; omega
    · omega
  have hmp_pos : 0 < m * p := Nat.mul_pos hm_pos hp
  have h4mx_eq : 4 * (m * x) = m * p + (4 * e + 1) := by
    calc 4 * (m * x)
      _ = m * (4 * x) := by ac_rfl
      _ = m * (p + c) := by rw [hx]
      _ = m * p + m * c := Nat.mul_add m p c
      _ = m * p + (4 * e + 1) := by rw [← hm]
  have hmx_gt : e < m * x := by omega
  have hcy : c * x + (p * x + e') = c * (m * e') := by
    have h1 : c * (m * e') = (m * c) * e' := by ac_rfl
    have h2 : (m * c) * e' = 4 * (e * e') + e' := by
      rw [← hm, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
    have h3 : 4 * (e * e') = (p + c) * x := by
      rw [← hxx, ← Nat.mul_assoc, hx]
    rw [h1, h2, h3, Nat.add_mul]
    omega
  have hy_gt : x < m * e' := by
    by_cases hle : m * e' ≤ x
    · have : c * (m * e') ≤ c * x := Nat.mul_le_mul_left c hle
      omega
    · omega
  dsimp only
  refine ⟨by omega, Nat.mul_pos hp (by omega), ?_⟩
  have hcy_sub : c * (m * e' - x) = p * x + e' := by
    rw [Nat.mul_sub_left_distrib]
    omega
  have hey_sub : e * (m * e' - x) = x * (m * x - e) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
    have h1 : e * (m * e') = m * (e * e') := by ac_rfl
    have h2 : m * (e * e') = x * (m * x) := by
      rw [← hxx]
      ac_rfl
    have h3 : e * x = x * e := Nat.mul_comm e x
    rw [h1, h2, h3]
  have h4xy : 4 * x * (m * e' - x) = p * (m * e' - x) + p * x + e' := by
    have h1 : (p + c) * (m * e' - x) = p * (m * e' - x) + c * (m * e' - x) := Nat.add_mul _ _ _
    rw [← hx] at h1
    omega
  have hlhs : 4 * x * (m * e' - x) * (p * (m * x - e)) =
      (p * (m * e' - x) + p * x + e') * (p * (m * x - e)) := by
    rw [h4xy]
  by_cases hx0 : x = 0
  · subst hx0; omega
  · have hx_pos : 0 < x := by omega
    have he'_term : x * (e' * (m * x - e)) = x * (x * (m * e' - x)) := by
      calc x * (e' * (m * x - e))
        _ = e' * (x * (m * x - e)) := by ac_rfl
        _ = e' * (e * (m * e' - x)) := by rw [← hey_sub]
        _ = (e * e') * (m * e' - x) := by ac_rfl
        _ = (x * x) * (m * e' - x) := by rw [hxx]
        _ = x * (x * (m * e' - x)) := by rw [Nat.mul_assoc]
    have he'_eq : e' * (m * x - e) = x * (m * e' - x) :=
      Nat.eq_of_mul_eq_mul_left hx_pos he'_term
    have he'_z : e' * (p * (m * x - e)) = p * (x * (m * e' - x)) := by
      calc e' * (p * (m * x - e))
        _ = p * (e' * (m * x - e)) := by ac_rfl
        _ = p * (x * (m * e' - x)) := by rw [he'_eq]
    rw [hlhs, Nat.add_mul, Nat.add_mul, he'_z]
    simp only [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
    ac_rfl

/-- Closing the beta = 1 step in Theorem 4: if `gcd alpha beta = 1` and `beta ∣ alpha`, then `beta = 1`. -/
theorem gcd_eq_one_dvd_self_eq_one (alpha beta : Nat)
    (hgcd : Nat.gcd alpha beta = 1) (hdvd : beta ∣ alpha) :
    beta = 1 := by
  have h1 : beta ∣ Nat.gcd alpha beta := Nat.dvd_gcd hdvd (Nat.dvd_refl beta)
  rw [hgcd] at h1
  exact Nat.eq_one_of_dvd_one h1

/-- Algebraic derivation of `h * c = alpha * p + beta` and `4 * h * s * r = (h + alpha) * p + beta`
    from `4 * s * r = p + c`, `f * beta = s * alpha`, and `4 * (f * r) + 1 = m * c`. -/
theorem upper_j1_hc_derive
    (p c s r f alpha beta m : Nat)
    (hbeta : 0 < beta)
    (hx : 4 * s * r = p + c) (hf : f * beta = s * alpha) (hm : 4 * (f * r) + 1 = m * c) :
    alpha < beta * m ∧
    (beta * m - alpha) * c = alpha * p + beta ∧
    4 * (beta * m - alpha) * s * r = ((beta * m - alpha) + alpha) * p + beta := by
  have hmul : beta * (4 * (f * r) + 1) = beta * (m * c) := by rw [hm]
  have h4fr : beta * (4 * (f * r)) = alpha * (p + c) := by
    calc beta * (4 * (f * r))
      _ = (f * beta) * (4 * r) := by ac_rfl
      _ = (s * alpha) * (4 * r) := by rw [hf]
      _ = alpha * (4 * s * r) := by ac_rfl
      _ = alpha * (p + c) := by rw [hx]
  have heq1 : alpha * p + alpha * c + beta = (beta * m) * c := by
    rw [Nat.mul_add] at hmul
    rw [h4fr, Nat.mul_add] at hmul
    have : beta * (m * c) = (beta * m) * c := (Nat.mul_assoc beta m c).symm
    omega
  have hlt : alpha < beta * m := by
    by_cases hle : beta * m ≤ alpha
    · have : (beta * m) * c ≤ alpha * c := Nat.mul_le_mul_right c hle
      omega
    · omega
  have hhc : (beta * m - alpha) * c = alpha * p + beta := by
    rw [Nat.sub_mul]
    omega
  refine ⟨hlt, hhc, ?_⟩
  have h4sr : 4 * (beta * m - alpha) * s * r = (beta * m - alpha) * (p + c) := by
    calc 4 * (beta * m - alpha) * s * r
      _ = (beta * m - alpha) * (4 * s * r) := by ac_rfl
      _ = (beta * m - alpha) * (p + c) := by rw [hx]
  rw [h4sr, Nat.mul_add, hhc, Nat.add_mul]
  omega

/-- #163 & #164 §1: At Theorem 4 equality `4 * ell * s0 * r = (ell + s0) * p + 1` with `ell * c = s0 * p + 1`,
    the witness `e = s0^2 * r` identically satisfies `4 * e + 1 = (ell + s0) * c`, and gives the explicit
    closed-form decomposition `4 / p = 1 / (s0 * r) + 1 / (ell * r) + 1 / (p * ell * s0 * r)`. -/
theorem thm4_equality_witness_sq
    (p ell s0 r c : Nat)
    (hell : 0 < ell)
    (hc : ell * c = s0 * p + 1)
    (heq : 4 * ell * s0 * r = (ell + s0) * p + 1) :
    4 * (s0 * s0 * r) + 1 = (ell + s0) * c ∧
    4 * (s0 * r) * (ell * r) * (p * ell * s0 * r) =
      p * ((s0 * r) * (ell * r) + (s0 * r) * (p * ell * s0 * r) + (ell * r) * (p * ell * s0 * r)) := by
  constructor
  · have hmul : ell * (4 * (s0 * s0 * r) + 1) = ell * ((ell + s0) * c) := by
      have h1 : ell * (4 * (s0 * s0 * r) + 1) = s0 * (4 * ell * s0 * r) + ell := by
        rw [Nat.mul_add, Nat.mul_one]
        have : ell * (4 * (s0 * s0 * r)) = s0 * (4 * ell * s0 * r) := by ac_rfl
        rw [this]
      have h2 : ell * ((ell + s0) * c) = (ell + s0) * (ell * c) := by ac_rfl
      rw [h1, heq, h2, hc]
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]
      ac_rfl
    exact Nat.eq_of_mul_eq_mul_left hell hmul
  · have hlhs : 4 * (s0 * r) * (ell * r) * (p * ell * s0 * r) =
        (4 * ell * s0 * r) * (p * (ell * (s0 * (r * r)))) := by ac_rfl
    have hrhs : p * ((s0 * r) * (ell * r) + (s0 * r) * (p * ell * s0 * r) + (ell * r) * (p * ell * s0 * r)) =
        ((ell + s0) * p + 1) * (p * (ell * (s0 * (r * r)))) := by
      simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_assoc, Nat.add_assoc]
      ac_rfl
    rw [hlhs, hrhs, heq]

/-- #164 §1: Parity impossibility of Theorem 4 equality whenever `ell = 6 * k + 1` and `s0 = 2 * k + 1`. -/
theorem thm4_equality_mod6_one_impossible
    (p k r : Nat) :
    4 * (6 * k + 1) * (2 * k + 1) * r ≠ ((6 * k + 1) + (2 * k + 1)) * p + 1 := by
  intro h
  have hlhs : (4 * (6 * k + 1) * (2 * k + 1) * r) % 2 = 0 := by
    have h2 : 4 * (6 * k + 1) * (2 * k + 1) * r = 2 * (2 * (6 * k + 1) * (2 * k + 1) * r) := by
      simp only [Nat.mul_assoc]
      omega
    rw [h2]
    omega
  have hrhs : (((6 * k + 1) + (2 * k + 1)) * p + 1) % 2 = 1 := by
    have h2 : ((6 * k + 1) + (2 * k + 1)) * p + 1 = 2 * ((4 * k + 1) * p) + 1 := by
      have : (6 * k + 1) + (2 * k + 1) = 2 * (4 * k + 1) := by omega
      rw [this, Nat.mul_assoc]
    rw [h2]
    omega
  have hmod := congrArg (· % 2) h
  omega

/-! ### Section 2: Universal Mod-8 Lock and Theorem 5A (`(ell + 4) * r >= p` for all `ell ≡ 1 (mod 6)`) -/

/-- Universal mod-8 lock for `j = 1` upper sources:
    When `p % 8 = 1` and `r % 2 = 1`, `4 * h * s * r = (h + alpha) * p + beta` forces
    `(h + alpha + beta) % 8 = (4 * h * s) % 8`. -/
theorem upper_j1_mod8_lock
    (p h s r alpha beta : Nat)
    (hp8 : p % 8 = 1) (hr2 : r % 2 = 1)
    (heq : 4 * h * s * r = (h + alpha) * p + beta) :
    (h + alpha + beta) % 8 = (4 * h * s) % 8 := by
  have h1 : (4 * h * s * r) % 8 = (4 * h * s) % 8 := by
    have hr : r = 2 * (r / 2) + 1 := by omega
    conv => lhs; rw [hr]
    rw [Nat.mul_add, Nat.mul_one]
    have : 4 * h * s * (2 * (r / 2)) = 8 * (h * s * (r / 2)) := by
      calc 4 * h * s * (2 * (r / 2))
        _ = (4 * 2) * (h * s * (r / 2)) := by ac_rfl
        _ = 8 * (h * s * (r / 2)) := rfl
    rw [this]
    omega
  have h2 : ((h + alpha) * p + beta) % 8 = (h + alpha + beta) % 8 := by
    have hp : p = 8 * (p / 8) + 1 := by omega
    conv => lhs; rw [hp]
    rw [Nat.mul_add, Nat.mul_one]
    have : (h + alpha) * (8 * (p / 8)) = 8 * ((h + alpha) * (p / 8)) := by ac_rfl
    rw [this]
    omega
  have hm := congrArg (· % 8) heq
  omega

/-- Composite factorizations confirming that for `ell = 6 * k + 1` (`k >= 1`), every integer in
    `{6*k+2, 6*k+3, 6*k+4, 6*k+6}` splits into proper factors strictly less than `ell`. -/
theorem mod6_one_smooth_neighbors (k : Nat) (hk : 1 ≤ k) :
    (6 * k + 2 = 2 * (3 * k + 1) ∧ 3 * k + 1 < 6 * k + 1) ∧
    (6 * k + 3 = 3 * (2 * k + 1) ∧ 2 * k + 1 < 6 * k + 1) ∧
    (6 * k + 4 = 2 * (3 * k + 2) ∧ 3 * k + 2 < 6 * k + 1) ∧
    (6 * k + 6 = 6 * (k + 1) ∧ k + 1 < 6 * k + 1 ∧ 6 < 6 * k + 1) := by
  omega

/-- Theorem 5A (Universal `ell + 4` Zero-Free Law for `ell ≡ 1 (mod 6)`):
    For `ell = 6 * k + 1` (`k >= 2`, so `ell >= 13`), `p > ell^2`, `p % 8 = 1`, `r` odd with
    `(ell + 4) * r >= p`, `1 <= s`, `s * r < p`, `s != ell`, `alpha ∣ s`, `beta ∣ s`,
    `gcd alpha beta = 1`, `ell <= h <= 3 * alpha`, and `h ∉ {6*k+2, 6*k+3, 6*k+4, 6*k+6}`
    (which are QR by `mod6_one_smooth_neighbors`), `4 * h * s * r = (h + alpha) * p + beta` is impossible. -/
theorem mod6_one_plus_four_zero_free
    (k p h s r alpha beta : Nat)
    (hk : 2 ≤ k)
    (hp_sq : (6 * k + 1) * (6 * k + 1) < p)
    (hp8 : p % 8 = 1) (hr2 : r % 2 = 1)
    (hr_ge : p ≤ (6 * k + 5) * r)
    (hs_pos : 1 ≤ s) (hx_lt : s * r < p) (hs_ne : s ≠ 6 * k + 1)
    (ha_dvd : alpha ∣ s) (hb_dvd : beta ∣ s) (hgcd : Nat.gcd alpha beta = 1)
    (hh_lo : 6 * k + 1 ≤ h) (hh_hi : h ≤ 3 * alpha)
    (hh_not_qr : h ≠ 6 * k + 2 ∧ h ≠ 6 * k + 3 ∧ h ≠ 6 * k + 4 ∧ h ≠ 6 * k + 6)
    (heq : 4 * h * s * r = (h + alpha) * p + beta) :
    False := by
  have hs_hi : s ≤ 6 * k + 4 := by
    by_cases hgt : 6 * k + 5 ≤ s
    · have : (6 * k + 5) * r ≤ s * r := Nat.mul_le_mul_right r hgt
      omega
    · omega
  have ha_le_s : alpha ≤ s := Nat.le_of_dvd hs_pos ha_dvd
  have hb_le_s : beta ≤ s := Nat.le_of_dvd hs_pos hb_dvd
  have hs_lo : 2 * k + 1 ≤ s := by omega
  have hmod8 := upper_j1_mod8_lock p h s r alpha beta hp8 hr2 heq
  by_cases hs1 : s = 2 * k + 1
  · have ha_eq : alpha = 2 * k + 1 := by omega
    have hb_eq : beta = 1 := by
      apply gcd_eq_one_dvd_self_eq_one alpha beta hgcd
      rw [ha_eq, ← hs1]
      exact hb_dvd
    subst hs1 ha_eq hb_eq
    have heven : (4 * h * (2 * k + 1)) % 2 = 0 := by
      have hrew : 4 * h * (2 * k + 1) = 2 * (2 * (h * (2 * k + 1))) := by
        calc 4 * h * (2 * k + 1)
          _ = (2 * 2) * (h * (2 * k + 1)) := by rw [Nat.mul_assoc]
          _ = 2 * (2 * (h * (2 * k + 1))) := by rw [Nat.mul_assoc]
      rw [hrew]
      omega
    have hpar : (h + (2 * k + 1) + 1) % 2 = 0 := by omega
    omega
  · by_cases hs2 : s = 2 * k + 2
    · have ha_eq : alpha = 2 * k + 2 := by
        rcases ha_dvd with ⟨q, hq⟩
        by_cases hq0 : q = 0
        · subst hq0; omega
        · by_cases hq1 : q = 1
          · subst hq1; omega
          · have hq2 : 2 ≤ q := by omega
            have : alpha * 2 ≤ alpha * q := Nat.mul_le_mul_left alpha hq2
            omega
      have hb_eq : beta = 1 := by
        apply gcd_eq_one_dvd_self_eq_one alpha beta hgcd
        rw [ha_eq, ← hs2]
        exact hb_dvd
      subst hs2 ha_eq hb_eq
      have hdiv8 : (4 * h * (2 * k + 2)) % 8 = 0 := by
        have hrew : 4 * h * (2 * k + 2) = 8 * (h * (k + 1)) := by
          have : 2 * k + 2 = 2 * (k + 1) := by omega
          rw [this]
          calc 4 * h * (2 * (k + 1))
            _ = (4 * 2) * (h * (k + 1)) := by ac_rfl
            _ = 8 * (h * (k + 1)) := rfl
        rw [hrew]
        omega
      have hh_eq : h = 6 * k + 5 := by omega
      subst hh_eq
      have hmul : 4 * (2 * k + 2) * p ≤ 4 * (2 * k + 2) * ((6 * k + 5) * r) :=
        Nat.mul_le_mul_left (4 * (2 * k + 2)) hr_ge
      have hrew1 : 4 * (2 * k + 2) * ((6 * k + 5) * r) = 4 * (6 * k + 5) * (2 * k + 2) * r := by ac_rfl
      have hrew2 : 4 * (2 * k + 2) * p = ((6 * k + 5) + (2 * k + 2)) * p + p := by
        have : 4 * (2 * k + 2) = (6 * k + 5) + (2 * k + 2) + 1 := by omega
        rw [this, Nat.add_mul, Nat.one_mul]
      rw [hrew1, hrew2, heq] at hmul
      have hp_pos : 2 ≤ p := by
        have : 1 ≤ (6 * k + 1) * (6 * k + 1) := Nat.mul_pos (by omega) (by omega)
        omega
      omega
    · have hs3 : 2 * k + 3 ≤ s := by omega
      have hmul : 4 * h * s * p ≤ (6 * k + 5) * h * p + (6 * k + 5) * alpha * p + (6 * k + 5) * beta := by
        have h1 : 4 * h * s * p ≤ 4 * h * s * ((6 * k + 5) * r) := Nat.mul_le_mul_left (4 * h * s) hr_ge
        have h2 : 4 * h * s * ((6 * k + 5) * r) = (6 * k + 5) * (4 * h * s * r) := by ac_rfl
        have h3 : (6 * k + 5) * ((h + alpha) * p + beta) =
            (6 * k + 5) * h * p + (6 * k + 5) * alpha * p + (6 * k + 5) * beta := by
          simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
        rw [h2, heq, h3] at h1
        exact h1
      have ha_bound : (6 * k + 5) * alpha * p ≤ (6 * k + 5) * s * p :=
        Nat.mul_le_mul_right p (Nat.mul_le_mul_left (6 * k + 5) ha_le_s)
      have hb_bound : (6 * k + 5) * beta ≤ (6 * k + 5) * (6 * k + 4) :=
        Nat.mul_le_mul_left (6 * k + 5) (Nat.le_trans hb_le_s hs_hi)
      -- Prove `(6*k + 5) * h + (6*k + 5) * s + 8 <= 4 * h * s` cleanly via two linear subcases:
      have hgap : (6 * k + 5) * h + (6 * k + 5) * s + 8 ≤ 4 * h * s := by
        by_cases hsmid : s ≤ 3 * k + 2
        · -- Subcase A (`s <= 3*k + 2`): multiply by 3 and use `9 * s >= 18*k + 27` and `3 * h >= 18*k + 3`:
          have h9s : (18 * k + 27) * h ≤ 9 * (h * s) := by
            have h1 : (18 * k + 27) * h ≤ (9 * s) * h := Nat.mul_le_mul_right h (by omega)
            have h2 : (9 * s) * h = 9 * (h * s) := by ac_rfl
            omega
          have h3h : (18 * k + 3) * s ≤ 3 * (h * s) := by
            have h1 : (18 * k + 3) * s ≤ (3 * h) * s := Nat.mul_le_mul_right s (by omega)
            have h2 : (3 * h) * s = 3 * (h * s) := by ac_rfl
            omega
          have h12 : 9 * (h * s) + 3 * (h * s) = 3 * (4 * h * s) := by
            calc 9 * (h * s) + 3 * (h * s)
              _ = (9 + 3) * (h * s) := (Nat.add_mul 9 3 (h * s)).symm
              _ = (3 * 4) * (h * s) := rfl
              _ = 3 * (4 * h * s) := by ac_rfl
          have h18h : (18 * k + 27) * h = 3 * ((6 * k + 5) * h) + 12 * h := by
            have : 18 * k + 27 = 3 * (6 * k + 5) + 12 := by omega
            rw [this, Nat.add_mul, Nat.mul_assoc]
          have h18s : (18 * k + 3) * s + 12 * s = 3 * ((6 * k + 5) * s) := by
            have : (18 * k + 3) + 12 = 3 * (6 * k + 5) := by omega
            rw [← Nat.add_mul, this, Nat.mul_assoc]
          omega
        · -- Subcase B (`3*k + 3 <= s`): use `2 * s >= 6*k + 6` and `2 * h >= 6*k + 6`:
          have h2s : (6 * k + 6) * h ≤ 2 * (h * s) := by
            have h1 : (6 * k + 6) * h ≤ (2 * s) * h := Nat.mul_le_mul_right h (by omega)
            have h2 : (2 * s) * h = 2 * (h * s) := by ac_rfl
            omega
          have h2h : (6 * k + 6) * s ≤ 2 * (h * s) := by
            have h1 : (6 * k + 6) * s ≤ (2 * h) * s := Nat.mul_le_mul_right s (by omega)
            have h2 : (2 * h) * s = 2 * (h * s) := by ac_rfl
            omega
          have h4 : 2 * (h * s) + 2 * (h * s) = 4 * h * s := by
            calc 2 * (h * s) + 2 * (h * s)
              _ = (2 + 2) * (h * s) := (Nat.add_mul 2 2 (h * s)).symm
              _ = 4 * h * s := by rw [← Nat.mul_assoc]
          have h6h : (6 * k + 6) * h = (6 * k + 5) * h + h := by
            have : 6 * k + 6 = (6 * k + 5) + 1 := by omega
            rw [this, Nat.add_mul, Nat.one_mul]
          have h6s : (6 * k + 6) * s = (6 * k + 5) * s + s := by
            have : 6 * k + 6 = (6 * k + 5) + 1 := by omega
            rw [this, Nat.add_mul, Nat.one_mul]
          omega
      have hgap_p : (6 * k + 5) * h * p + (6 * k + 5) * s * p + 8 * p ≤ 4 * h * s * p := by
        have hp_mul := Nat.mul_le_mul_right p hgap
        rw [Nat.add_mul, Nat.add_mul] at hp_mul
        exact hp_mul
      -- Bound `(6*k + 5) * (6*k + 4) < 4 * (6*k + 1)^2 < 4 * p < 8 * p`:
      have hp_gt : (6 * k + 5) * (6 * k + 4) < 8 * p := by
        have hlt1 : 6 * k + 5 < 2 * (6 * k + 1) := by omega
        have hlt2 : 6 * k + 4 < 2 * (6 * k + 1) := by omega
        have hprod : (6 * k + 5) * (6 * k + 4) < (2 * (6 * k + 1)) * (2 * (6 * k + 1)) :=
          Nat.mul_lt_mul_of_lt_of_lt hlt1 hlt2
        have h4sq : (2 * (6 * k + 1)) * (2 * (6 * k + 1)) = 4 * ((6 * k + 1) * (6 * k + 1)) := by
          calc (2 * (6 * k + 1)) * (2 * (6 * k + 1))
            _ = (2 * 2) * ((6 * k + 1) * (6 * k + 1)) := by ac_rfl
            _ = 4 * ((6 * k + 1) * (6 * k + 1)) := rfl
        omega
      omega

/-! ### Section 3: Theorem 5B (Complete Classification for `ell = 13` on `408 * r >= 23 * p + 1`) -/

/-- Decidable check that `h` (`<= 168`) has at least one prime factor `>= 13` to an odd exponent:
    after stripping `{2, 3, 5, 7, 11}`, any 13-rough integer `< 169 = 13^2` is a non-square iff `!= 1`. -/
def stripPrime (p : Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => if n % p == 0 then stripPrime p k (n / p) else n

def rough13Part (h : Nat) : Nat :=
  let h1 := stripPrime 2 6 h
  let h2 := stripPrime 3 4 h1
  let h3 := stripPrime 5 3 h2
  let h4 := stripPrime 7 3 h3
  stripPrime 11 2 h4

def hasOddPrimeGe13 (h : Nat) : Bool :=
  rough13Part h != 1

def validOtherEll13Tuple (s alpha beta h : Nat) : Bool :=
  (s != 13) &&
  !(s == 6 && alpha == 6 && beta == 1 && h == 17) &&
  (alpha > 0) && (beta > 0) &&
  (s % alpha == 0) && (s % beta == 0) &&
  (Nat.gcd alpha beta == 1) &&
  (13 <= h) && (h <= 3 * alpha) &&
  hasOddPrimeGe13 h &&
  ((h + alpha + beta) % 8 == (4 * h * s) % 8) &&
  (!((h * s) % 3 == 0) || ((h + alpha + beta) % 3 == 0)) &&
  (92 * h * s * 1009 + 4 * h * s <= 408 * (h + alpha) * 1009 + 408 * beta)

def anyOtherEll13Tuple : Bool :=
  (List.range 18).any fun s =>
    if s == 0 then false else
    (List.range (s + 1)).any fun alpha =>
      (List.range (s + 1)).any fun beta =>
        (List.range (3 * alpha + 1)).any fun h =>
          validOtherEll13Tuple s alpha beta h

theorem no_other_ell13_qr_tuple : anyOtherEll13Tuple = false := by decide

theorem list_any_false_forall {α : Type} (l : List α) (f : α → Bool)
    (h : l.any f = false) (x : α) (hx : x ∈ l) : f x = false := by
  induction l with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    rcases List.mem_cons.mp hx with rfl | htl
    · exact h.1
    · exact ih h.2 htl

theorem scale_down_p_to_1009 (A B C D p : Nat)
    (hp : 1009 ≤ p) (hgt : B ≤ A) (hineq : A * p + C ≤ B * p + D) :
    A * 1009 + C ≤ B * 1009 + D := by
  have hA : A = B + (A - B) := (Nat.add_sub_of_le hgt).symm
  rw [hA, Nat.add_mul, Nat.add_assoc] at hineq
  have h1 : (A - B) * p + C ≤ D := Nat.le_of_add_le_add_left hineq
  have h2 : (A - B) * 1009 + C ≤ (A - B) * p + C :=
    Nat.add_le_add_right (Nat.mul_le_mul_left (A - B) hp) C
  have h3 : B * 1009 + ((A - B) * 1009 + C) ≤ B * 1009 + D :=
    Nat.add_le_add_left (Nat.le_trans h2 h1) (B * 1009)
  rw [hA, Nat.add_mul, Nat.add_assoc]
  exact h3

/-- Theorem 5B (Part 1 — QR-cofactor branch for `ell = 13`):
    Whenever `p >= 1009`, `p % 24 = 1`, `r` odd with `408 * r >= 23 * p + 1`, `1 <= s`,
    `s * r < p`, `s != 13`, `alpha ∣ s`, `beta ∣ s`, `gcd alpha beta = 1`,
    `13 <= h <= 3 * alpha`, `hasOddPrimeGe13 h = true`, `h * c = alpha * p + beta`, and
    `4 * h * s * r = (h + alpha) * p + beta`, we MUST have `(s, alpha, beta, h) = (6, 6, 1, 17)`,
    `408 * r = 23 * p + 1`, and `17 ∣ p + 3`. -/
theorem ell13_qr_cofactor_sharp_lock
    (p c h s r alpha beta : Nat)
    (hp1009 : 1009 ≤ p) (hp24 : p % 24 = 1) (hr2 : r % 2 = 1)
    (hr_ge : 23 * p + 1 ≤ 408 * r)
    (hs_pos : 1 ≤ s) (hx_lt : s * r < p) (hs_ne : s ≠ 13)
    (ha_dvd : alpha ∣ s) (hb_dvd : beta ∣ s) (hgcd : Nat.gcd alpha beta = 1)
    (hh_lo : 13 ≤ h) (hh_hi : h ≤ 3 * alpha) (hh_odd13 : hasOddPrimeGe13 h = true)
    (hhc : h * c = alpha * p + beta)
    (heq : 4 * h * s * r = (h + alpha) * p + beta) :
    s = 6 ∧ alpha = 6 ∧ beta = 1 ∧ h = 17 ∧ 408 * r = 23 * p + 1 ∧ 17 ∣ (p + 3) := by
  have hs_le17 : s ≤ 17 := by
    by_cases h18 : 18 ≤ s
    · have h1 : 18 * r ≤ s * r := Nat.mul_le_mul_right r h18
      omega
    · omega
  have ha_le : alpha ≤ s := Nat.le_of_dvd hs_pos ha_dvd
  have hb_le : beta ≤ s := Nat.le_of_dvd hs_pos hb_dvd
  have ha_pos : 0 < alpha := by omega
  have hb_pos : 0 < beta := by
    by_cases hb0 : beta = 0
    · subst hb0; simp at hgcd; omega
    · omega
  have hmod8 := upper_j1_mod8_lock p h s r alpha beta (by omega) hr2 heq
  have hmod3 : ¬((h * s) % 3 = 0) ∨ (h + alpha + beta) % 3 = 0 := by
    by_cases h3 : (h * s) % 3 = 0
    · right
      have hlhs3 : (4 * h * s * r) % 3 = 0 := by
        have hrew : 4 * h * s * r = (h * s) * (4 * r) := by ac_rfl
        rw [hrew, Nat.mul_mod, h3]
        simp
      have hrhs3 : ((h + alpha) * p + beta) % 3 = (h + alpha + beta) % 3 := by
        have hp' : p = 3 * (p / 3) + 1 := by omega
        conv => lhs; rw [hp']
        rw [Nat.mul_add, Nat.mul_one]
        have : (h + alpha) * (3 * (p / 3)) = 3 * ((h + alpha) * (p / 3)) := by ac_rfl
        rw [this]
        omega
      have hm := congrArg (· % 3) heq
      omega
    · exact Or.inl h3
  have hsize_p : 92 * (h * s) * p + 4 * (h * s) ≤ 408 * (h + alpha) * p + 408 * beta := by
    have hmul : 4 * (h * s) * (23 * p + 1) ≤ 4 * (h * s) * (408 * r) :=
      Nat.mul_le_mul_left (4 * (h * s)) hr_ge
    have h1 : 4 * (h * s) * (23 * p + 1) = 92 * (h * s) * p + 4 * (h * s) := by
      rw [Nat.mul_add, Nat.mul_one]
      have : 4 * (h * s) * (23 * p) = (4 * 23) * (h * s) * p := by ac_rfl
      rw [this]
    have h2 : 4 * (h * s) * (408 * r) = 408 * (4 * h * s * r) := by ac_rfl
    have h3 : 408 * ((h + alpha) * p + beta) = 408 * (h + alpha) * p + 408 * beta := by
      rw [Nat.mul_add, Nat.mul_assoc]
    rw [h1, h2, heq, h3] at hmul
    exact hmul
  have hsize_1009 : 92 * h * s * 1009 + 4 * h * s ≤ 408 * (h + alpha) * 1009 + 408 * beta := by
    have h92 : 92 * h * s = 92 * (h * s) := Nat.mul_assoc 92 h s
    have h4 : 4 * h * s = 4 * (h * s) := Nat.mul_assoc 4 h s
    rw [h92, h4]
    have hhs_max : h * s ≤ 51 * 17 := Nat.mul_le_mul (by omega) hs_le17
    by_cases hcmp : 23 * (h * s) ≤ 102 * (h + alpha)
    · by_cases heq_c : 23 * (h * s) = 102 * (h + alpha)
      · exact scale_down_p_to_1009 (92 * (h * s)) (408 * (h + alpha)) (4 * (h * s)) (408 * beta) p
          hp1009 (by omega) hsize_p
      · have hstep : 23 * (h * s) + 1 ≤ 102 * (h + alpha) := by omega
        have hstep_m : 4036 * (23 * (h * s) + 1) ≤ 4036 * (102 * (h + alpha)) :=
          Nat.mul_le_mul_left 4036 hstep
        omega
    · exact scale_down_p_to_1009 (92 * (h * s)) (408 * (h + alpha)) (4 * (h * s)) (408 * beta) p
        hp1009 (by omega) hsize_p
  have htuple : s = 6 ∧ alpha = 6 ∧ beta = 1 ∧ h = 17 := by
    by_cases hgoal : s = 6 ∧ alpha = 6 ∧ beta = 1 ∧ h = 17
    · exact hgoal
    · have hs_mem : s ∈ List.range 18 := List.mem_range.mpr (by omega)
      have h1 := list_any_false_forall _ _ no_other_ell13_qr_tuple s hs_mem
      have hs0 : (s == 0) = false := beq_false_of_ne (by omega)
      rw [hs0] at h1
      dsimp at h1
      have ha_mem : alpha ∈ List.range (s + 1) := List.mem_range.mpr (by omega)
      have h2 := list_any_false_forall _ _ h1 alpha ha_mem
      have hb_mem : beta ∈ List.range (s + 1) := List.mem_range.mpr (by omega)
      have h3 := list_any_false_forall _ _ h2 beta hb_mem
      have hh_mem : h ∈ List.range (3 * alpha + 1) := List.mem_range.mpr (by omega)
      have h4 := list_any_false_forall _ _ h3 h hh_mem
      unfold validOtherEll13Tuple at h4
      have hb_sne : (s != 13) = true := bne_iff_ne.mpr hs_ne
      have hb_not6 : (!(s == 6 && alpha == 6 && beta == 1 && h == 17)) = true := by
        cases h6 : (s == 6 && alpha == 6 && beta == 1 && h == 17)
        · rfl
        · simp only [Bool.and_eq_true, beq_iff_eq] at h6
          rcases h6 with ⟨⟨⟨hs6, ha6⟩, hb1⟩, hh17⟩
          exact False.elim (hgoal ⟨hs6, ha6, hb1, hh17⟩)
      have hb_apos : decide (alpha > 0) = true := decide_eq_true ha_pos
      have hb_bpos : decide (beta > 0) = true := decide_eq_true hb_pos
      have hb_advd : (s % alpha == 0) = true := beq_iff_eq.mpr (Nat.mod_eq_zero_of_dvd ha_dvd)
      have hb_bdvd : (s % beta == 0) = true := beq_iff_eq.mpr (Nat.mod_eq_zero_of_dvd hb_dvd)
      have hb_gcd : (Nat.gcd alpha beta == 1) = true := beq_iff_eq.mpr hgcd
      have hb_hlo : decide (13 ≤ h) = true := decide_eq_true hh_lo
      have hb_hhi : decide (h ≤ 3 * alpha) = true := decide_eq_true hh_hi
      have hb_m8 : ((h + alpha + beta) % 8 == (4 * h * s) % 8) = true := beq_iff_eq.mpr hmod8
      have hb_m3 : (!((h * s) % 3 == 0) || ((h + alpha + beta) % 3 == 0)) = true := by
        rcases hmod3 with hn3 | hy3
        · have hq : ((h * s) % 3 == 0) = false := beq_false_of_ne hn3
          rw [hq]
          rfl
        · have hq : ((h + alpha + beta) % 3 == 0) = true := beq_iff_eq.mpr hy3
          rw [hq, Bool.or_true]
      have hb_sz : decide (92 * h * s * 1009 + 4 * h * s ≤ 408 * (h + alpha) * 1009 + 408 * beta) = true :=
        decide_eq_true hsize_1009
      rw [hb_sne, hb_not6, hb_apos, hb_bpos, hb_advd, hb_bdvd, hb_gcd, hb_hlo, hb_hhi,
          hh_odd13, hb_m8, hb_m3, hb_sz] at h4
      simp only [Bool.and_self] at h4
      exact Bool.noConfusion h4
  rcases htuple with ⟨rfl, rfl, rfl, rfl⟩
  have heq408 : 408 * r = 23 * p + 1 := by omega
  have hdvd17 : 17 ∣ (p + 3) := ⟨3 * c - p, by omega⟩
  exact ⟨rfl, rfl, rfl, rfl, heq408, hdvd17⟩

/-- Theorem 5B (Part 2 — Second QNR prime `s = 17` reductions):
    When `68 * r = p + c`, `1009 <= p`, `23 * p + 1 <= 408 * r` (which automatically forces `c > 17p/6`),
    `c % 4 = 3`, and `gcd 17 c = 1`:
    (1) `e = 17` fails (`¬ c ∣ 69`);
    (2) `e = 17 * r` fails (`¬ c ∣ 68 * r + 1`);
    (3) `e = 17 * r^2` succeeds iff `c ∣ p^2 + 68`. -/
theorem ell13_s17_qnr_reductions
    (p c r : Nat)
    (hp1009 : 1009 ≤ p) (hx : 68 * r = p + c)
    (hr_ge : 23 * p + 1 ≤ 408 * r)
    (hc4 : c % 4 = 3) (hgcd17 : Nat.gcd 17 c = 1) :
    ¬(c ∣ (4 * 17 + 1)) ∧
    ¬(c ∣ (4 * (17 * r) + 1)) ∧
    ((c ∣ (4 * (17 * r * r) + 1)) ↔ (c ∣ (p * p + 68))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hd
    have hc_gt : 69 < c := by omega
    have hle := Nat.le_of_dvd (by decide) hd
    omega
  · intro ⟨m, hm⟩
    have h68 : 4 * (17 * r) + 1 = p + c + 1 := by omega
    by_cases hm0 : m = 0
    · subst hm0; omega
    · by_cases hm1 : m = 1
      · subst hm1; omega
      · have h2c : c * 2 ≤ c * m := Nat.mul_le_mul_left c (by omega)
        omega
  · have hid : 68 * (4 * (17 * r * r) + 1) = (p * p + 68) + c * (2 * p + c) := by
      calc 68 * (4 * (17 * r * r) + 1)
        _ = (68 * r) * (68 * r) + 68 := by
          rw [Nat.mul_add, Nat.mul_one]
          have : 68 * (4 * (17 * r * r)) = (68 * r) * (68 * r) := by ac_rfl
          rw [this]
        _ = (p + c) * (p + c) + 68 := by rw [hx]
        _ = (p * p + 68) + c * (2 * p + c) := by
          have htwo : 2 * p = p + p := Nat.two_mul p
          rw [htwo]
          simp only [Nat.add_mul, Nat.mul_add, Nat.add_assoc]
          ac_rfl
    have hgcd4 : Nat.gcd c 4 = 1 := by
      rw [Nat.gcd_comm, Nat.gcd_rec 4 c, hc4]
      decide
    have hgcd68 : Nat.gcd c 68 = 1 := by
      have h17 : Nat.gcd c 17 = 1 := by rw [Nat.gcd_comm]; exact hgcd17
      exact Nat.Coprime.mul_right hgcd4 h17
    constructor
    · intro ⟨k, hk⟩
      rw [hk] at hid
      have hrew : p * p + 68 = c * (68 * k - (2 * p + c)) := by
        have h1 : 68 * (c * k) = c * (68 * k) := by ac_rfl
        rw [h1] at hid
        have hle2 : 2 * p + c ≤ 68 * k := by
          by_cases hgt : 68 * k < 2 * p + c
          · have : c * (68 * k) < c * (2 * p + c) := Nat.mul_lt_mul_of_pos_left hgt (by omega)
            omega
          · omega
        rw [Nat.mul_sub_left_distrib]
        omega
      exact ⟨68 * k - (2 * p + c), hrew⟩
    · intro ⟨k, hk⟩
      have hdvd_prod : c ∣ 68 * (4 * (17 * r * r) + 1) := by
        refine ⟨k + (2 * p + c), ?_⟩
        rw [hid, hk, ← Nat.mul_add]
      exact Nat.Coprime.dvd_of_dvd_mul_left hgcd68 hdvd_prod

/-! ### Section 4: #163 Transfer Lemma, #164 §3 Reachability, and Explicit Prime Counterexamples -/

/-- #163 Transfer Lemma: For any `p > 2925` with `p % 12 = 1`, `p % 5 = 4`, and `17 ∣ (p + 3)`,
    root `13`'s multiplier `t = 15` (`c0 = 39 * 15^2 < 3 * p`) gives `17 ∣ (p + c0) / 4`,
    and child `17`'s multiplier `t = 1` (`c1 = 51 < p / 3`) has Type II witness `d = 5`. -/
theorem transfer_13_to_17_d5
    (p : Nat) (hp_gt : 2925 < p) (hp12 : p % 12 = 1) (hp5 : p % 5 = 4) (hp17 : 17 ∣ (p + 3)) :
    39 * 15 * 15 < 3 * p ∧
    (p + 39 * 15 * 15) % 4 = 0 ∧
    17 ∣ ((p + 39 * 15 * 15) / 4) ∧
    3 * 51 < p ∧
    5 ∣ ((p + 51) / 4) ∧
    51 ∣ ((p + 51) / 4 + 5) := by
  rcases hp17 with ⟨k, hk⟩
  refine ⟨by omega, by omega, ?_, by omega, ?_, ?_⟩
  · have hdiv4 : 4 * ((p + 39 * 15 * 15) / 4) = 17 * (k + 516) := by omega
    have h4k : 4 ∣ (k + 516) := by omega
    rcases h4k with ⟨u, hu⟩
    exact ⟨u, by omega⟩
  · omega
  · have h12 : 12 ∣ (p + 71) := by omega
    have h17' : 17 ∣ (p + 71) := ⟨k + 4, by omega⟩
    rcases h12 with ⟨v, hv⟩
    have hdv : 17 ∣ 12 * v := by rw [← hv]; exact h17'
    have hcop' : Nat.gcd 17 12 = 1 := by decide
    rcases Nat.Coprime.dvd_of_dvd_mul_left hcop' hdv with ⟨w, hw⟩
    exact ⟨w, by omega⟩

/-- #164 §3 Reachability completion:
    In `p = 14,147,458,249`, vertex `q = 14,731` is directly reached from root `13` at `t = 1495`
    (distance 1). -/
theorem reach_14147458249_root_to_14731 :
    39 * 1495 * 1495 < 3 * 14147458249 ∧
    (14147458249 + 39 * 1495 * 1495) % (4 * 14731) = 0 ∧
    (14147458249 * 14147458249 + 52) % (14731 * 827 * 827) = 0 := by decide

/-- Counterexample 1 to `r / p <= 23 / 408` for `ell = 13, s != 13`:
    `p = 128,051,449`, `q = 122,130,889` (`c = 3 * q = 366,392,667`), `x = 17 * 7,271,237`,
    `408 * r > 23 * p + 1`, `c ∣ p^2 + 68`, and exact 3-term unit fraction decomposition. -/
theorem witness_128051449_gt_23_408 :
    let p := 128051449
    let c := 3 * 122130889
    let r := 7271237
    let x := 17 * r
    let y := 43201114
    let z := 40224230380259575468082
    4 * x = p + c ∧
    p < 3 * c ∧ c < 3 * p ∧
    23 * p + 1 < 408 * r ∧
    (p * p + 68) % c = 0 ∧
    (4 * (17 * r * r) + 1) % c = 0 ∧
    4 * x * y * z = p * (x * y + x * z + y * z) := by decide

/-- Counterexample 2 (`p = 123,297,007,849`, `p / r ≈ 17.001390 < 408 / 23`). -/
theorem witness_123297007849_gt_23_408 :
    let p := 123297007849
    let c := 369850701547
    let r := 7252172197
    let x := 17 * r
    let y := 41100122794
    let z := 36750543336207751533316366822882
    4 * x = p + c ∧
    p < 3 * c ∧ c < 3 * p ∧
    23 * p + 1 < 408 * r ∧
    (p * p + 68) % c = 0 ∧
    (4 * (17 * r * r) + 1) % c = 0 ∧
    4 * x * y * z = p * (x * y + x * z + y * z) := by decide

/-- Counterexample 3 (`p = 250,067,982,481`, `p / r ≈ 17.000281`, approaching `ell + 4 = 17` from above). -/
theorem witness_250067982481_gt_23_408 :
    let p := 250067982481
    let c := 750187422667
    let r := 14709638311
    let x := 17 * r
    let y := 83356453192
    let z := 306619175597585548179206931204472
    4 * x = p + c ∧
    p < 3 * c ∧ c < 3 * p ∧
    23 * p + 1 < 408 * r ∧
    (p * p + 68) % c = 0 ∧
    (4 * (17 * r * r) + 1) % c = 0 ∧
    4 * x * y * z = p * (x * y + x * z + y * z) := by decide

#print axioms type1_unit_fraction_sound
#print axioms gcd_eq_one_dvd_self_eq_one
#print axioms upper_j1_hc_derive
#print axioms thm4_equality_witness_sq
#print axioms thm4_equality_mod6_one_impossible
#print axioms upper_j1_mod8_lock
#print axioms mod6_one_smooth_neighbors
#print axioms mod6_one_plus_four_zero_free
#print axioms no_other_ell13_qr_tuple
#print axioms ell13_qr_cofactor_sharp_lock
#print axioms ell13_s17_qnr_reductions
#print axioms transfer_13_to_17_d5
#print axioms reach_14147458249_root_to_14731
#print axioms witness_128051449_gt_23_408
#print axioms witness_123297007849_gt_23_408
#print axioms witness_250067982481_gt_23_408
