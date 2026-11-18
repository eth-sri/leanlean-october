module

public import Chazelle.Core.Lemma41Main
public import Chazelle.Core.Lemma41Cover2
public import Chazelle.Core.Lemma41Levels

/-!
# WP-J, part 28: the cost of Lemma 4.1

With the oracle costs of `ShootCutSpec` (`F, G, H` at the final granularity `Gλ = γ'_λ`),
`l41Big ≤ K (lemma41Nat λ + 1)` for a constant `K` (`l41Big_le`).  Everything is measured in
`E = 2^(λ/75)`:
* `Gλ ≤ 2402 E^15`, `⌈log₂ Gλ⌉ + 1 ≤ 3λ`, `H(Gλ) ≤ 19216 E^3`, `F(Gλ) ≤ 14704 κ λ E^11`,
  `G(Gλ) ≤ 3κλ`, so one merge costs `≤ K₁ λ² E^14` per chord;
* the chords of a level: the leaves `≤ 10800 E^60` (two pieces per grade and Lemma 2.3), the
  merged nodes `≤ 252240 E^60`, so a level costs `≤ K₂ λ² E^74 = K₂ λ² 2^(74λ/75)`;
* with at most `⌈log₂ λ⌉ + 1` levels, the total is `O(lemma41Nat λ)`.
-/

namespace Chazelle.Core.L41

open Chazelle.Cost Finset

@[expose] public section

/-- The oracle costs of `ShootCutSpec` with constant `κ`. -/
noncomputable def scF (κ : ℕ) (γ : ℕ) : ℕ :=
  κ * (Nat.clog 2 γ + 1) * rpowCeil (cutGran γ * (γ + 1) ^ 2) ((1 : ℝ) / 3) + κ

/-- The cutter's piece count of `ShootCutSpec`. -/
def scG (κ : ℕ) (γ : ℕ) : ℕ := κ * (Nat.clog 2 γ + 1)

theorem cutGran_mono : Monotone cutGran := fun _ _ h =>
  gradeGran_mono (Nat.clog_mono_right 2 h)

theorem rpowCeil_mono {x y : ℕ} (a : ℝ) (ha : 0 ≤ a) (h : x ≤ y) : rpowCeil x a ≤ rpowCeil y a :=
  Nat.ceil_mono (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast h) ha)

theorem scF_mono (κ : ℕ) : Monotone (scF κ) := by
  intro x y h
  unfold scF
  have h1 := Nat.clog_mono_right 2 h
  have h2 : cutGran x * (x + 1) ^ 2 ≤ cutGran y * (y + 1) ^ 2 :=
    Nat.mul_le_mul (cutGran_mono h) (Nat.pow_le_pow_left (by omega) 2)
  have h3 := rpowCeil_mono ((1 : ℝ) / 3) (by norm_num) h2
  gcongr

theorem scG_mono (κ : ℕ) : Monotone (scG κ) := fun x y h => by
  have := Nat.clog_mono_right 2 h
  unfold scG; gcongr

/-! ## Powers of `E = 2^(λ/75)` -/

/-- `E^k = 2^(kλ/75)`. -/
theorem E_pow (lam k : ℕ) : ((2 : ℝ) ^ ((lam : ℝ) / 75)) ^ k = (2 : ℝ) ^ ((k : ℝ) * lam / 75) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; ring

theorem two_pow_le_E {n lam k : ℕ} {b : ℝ} (h : (n : ℝ) ≤ (k : ℝ) * lam / 75 + b) :
    (2 : ℝ) ^ n ≤ (2 : ℝ) ^ b * ((2 : ℝ) ^ ((lam : ℝ) / 75)) ^ k := by
  rw [E_pow, ← Real.rpow_natCast, two_rpow_mul_two_rpow]
  apply two_rpow_le_two_rpow; linarith

theorem ceilBeta_le_real (g : ℕ) : (ceilBeta g : ℝ) ≤ (g : ℝ) / 5 + 1 := by
  have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ beta * g by rw [beta_eq]; positivity)
  unfold ceilBeta; rw [beta_eq] at this ⊢; linarith

theorem le_ceilBeta_real (g : ℕ) : (g : ℝ) / 5 ≤ (ceilBeta g : ℝ) := by
  have := beta_mul_le_ceilBeta g; rw [beta_eq] at this; linarith

section bounds

variable {lam : ℕ}

/-- `2^⌈βλ⌉ ≤ 2 E^15`. -/
theorem two_pow_ceilBeta_le (lam : ℕ) :
    (2 : ℝ) ^ ceilBeta lam ≤ 2 * ((2 : ℝ) ^ ((lam : ℝ) / 75)) ^ 15 := by
  have := two_pow_le_E (n := ceilBeta lam) (lam := lam) (k := 15) (b := 1)
    (by have := ceilBeta_le_real lam; push_cast; linarith)
  simpa using this

/-- `γ'_λ ≤ 2402 E^15`. -/
theorem gradeGran_le_E (lam : ℕ) :
    (gradeGran lam : ℝ) ≤ 2402 * ((2 : ℝ) ^ ((lam : ℝ) / 75)) ^ 15 := by
  have h1 := gradeGran_le_real lam
  have h2 := two_pow_ceilBeta_le lam
  linarith

/-- `⌈log₂ γ'_λ⌉ + 1 ≤ 3λ` for `λ ≥ 6`. -/
theorem clog_gradeGran_add_one_le (h6 : 6 ≤ lam) : Nat.clog 2 (gradeGran lam) + 1 ≤ 3 * lam := by
  have h1 := clog_gradeGran_le lam
  have h2 : Nat.clog 2 (gradeGran lam) ≤ Nat.clog 2 (gradeGran lam + 1) :=
    Nat.clog_mono_right 2 (by omega)
  have h3 := ceilBeta_le lam
  omega

/-- `H(γ'_λ) = γ'_{⌈log₂ γ'_λ⌉} ≤ 19216 E^3`. -/
theorem cutGran_le_E (lam : ℕ) :
    (cutGran (gradeGran lam) : ℝ) ≤ 19216 * ((2 : ℝ) ^ ((lam : ℝ) / 75)) ^ 3 := by
  unfold cutGran
  set CL := Nat.clog 2 (gradeGran lam) with hCL
  have h1 := gradeGran_le_real CL
  have hcl : (CL : ℝ) ≤ (lam : ℝ) / 5 + 12 := by
    have a1 := clog_gradeGran_le lam
    have a2 : CL ≤ Nat.clog 2 (gradeGran lam + 1) := Nat.clog_mono_right 2 (by omega)
    have a3 := ceilBeta_le_real lam
    have : (CL : ℝ) ≤ (ceilBeta lam : ℝ) + 11 := by exact_mod_cast (le_trans a2 a1)
    linarith
  have h2 : (2 : ℝ) ^ ceilBeta CL ≤ (2 : ℝ) ^ (4 : ℝ) * ((2 : ℝ) ^ ((lam : ℝ) / 75)) ^ 3 :=
    two_pow_le_E (by have := ceilBeta_le_real CL; push_cast; linarith)
  have h16 : (2 : ℝ) ^ (4 : ℝ) = 16 := by norm_num
  rw [h16] at h2
  nlinarith

/-- `λ ≤ 150 E`. -/
theorem lam_le_E (lam : ℕ) : (lam : ℝ) ≤ 150 * (2 : ℝ) ^ ((lam : ℝ) / 75) := by
  have := nat_le_two_rpow 75 (by norm_num) lam
  push_cast at this; linarith

theorem one_le_E (lam : ℕ) : (1 : ℝ) ≤ (2 : ℝ) ^ ((lam : ℝ) / 75) :=
  Real.one_le_rpow (by norm_num) (by positivity)

/-- `⌈(H (Gλ + 1)²)^{1/3}⌉ ≤ 4901 E^11`. -/
theorem rpowCeil_le_E (lam : ℕ) :
    (rpowCeil (cutGran (gradeGran lam) * (gradeGran lam + 1) ^ 2) ((1 : ℝ) / 3) : ℝ) ≤
      4901 * ((2 : ℝ) ^ ((lam : ℝ) / 75)) ^ 11 := by
  set E := (2 : ℝ) ^ ((lam : ℝ) / 75) with hE
  have hE1 : 1 ≤ E := one_le_E lam
  have hH := cutGran_le_E lam
  have hG := gradeGran_le_E lam
  rw [← hE] at hH hG
  have hG1 : ((gradeGran lam : ℕ) : ℝ) + 1 ≤ 2403 * E ^ 15 := by
    have : (1 : ℝ) ≤ E ^ 15 := one_le_pow₀ hE1
    linarith
  set X := cutGran (gradeGran lam) * (gradeGran lam + 1) ^ 2 with hX
  have hXR : (X : ℝ) ≤ (4900 * E ^ 11) ^ 3 := by
    rw [hX]; push_cast
    have h0 : (0 : ℝ) ≤ (gradeGran lam : ℝ) + 1 := by positivity
    calc (cutGran (gradeGran lam) : ℝ) * ((gradeGran lam : ℝ) + 1) ^ 2
        ≤ (19216 * E ^ 3) * (2403 * E ^ 15) ^ 2 := by
          apply mul_le_mul hH (pow_le_pow_left₀ h0 hG1 2) (by positivity) (by positivity)
      _ ≤ (4900 * E ^ 11) ^ 3 := by
          have : (0 : ℝ) ≤ E ^ 33 := by positivity
          nlinarith [this]
  have hroot : (X : ℝ) ^ ((1 : ℝ) / 3) ≤ 4900 * E ^ 11 := by
    have h0 : (0 : ℝ) ≤ 4900 * E ^ 11 := by positivity
    calc (X : ℝ) ^ ((1 : ℝ) / 3) ≤ ((4900 * E ^ 11) ^ 3) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hXR (by norm_num)
      _ = 4900 * E ^ 11 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul h0]; norm_num
  unfold rpowCeil
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg X) ((1 : ℝ) / 3))
  have : (1 : ℝ) ≤ E ^ 11 := one_le_pow₀ hE1
  linarith

/-- **The cost factor of one merge**: `φ ≤ K₁ λ² E^14`. -/
theorem phiL_le (κM κ : ℕ) {L : ℕ} (h7 : 7 ≤ lam) (hL : L ≤ 2 ^ lam) :
    (phiL (fun _ => κM) (scF κ) (scG κ) cutGran (gradeGran lam) L : ℝ) ≤
      (κM * κ ^ 2 * 14704 * 3 * 19368 : ℝ) * (lam : ℝ) ^ 2 *
        ((2 : ℝ) ^ ((lam : ℝ) / 75)) ^ 14 := by
  set E := (2 : ℝ) ^ ((lam : ℝ) / 75) with hE
  have hE1 : 1 ≤ E := one_le_E lam
  have hl : (lam : ℝ) ≤ 150 * E := lam_le_E lam
  have hl7 : (7 : ℝ) ≤ lam := by exact_mod_cast h7
  have hCL : ((Nat.clog 2 (gradeGran lam) + 1 : ℕ) : ℝ) ≤ 3 * lam := by
    exact_mod_cast clog_gradeGran_add_one_le (by omega)
  have hR := rpowCeil_le_E lam
  have hH := cutGran_le_E lam
  rw [← hE] at hR hH
  have hLc : Nat.clog 2 (L + 1) ≤ lam + 1 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_succ]; have := Nat.one_le_two_pow (n := lam); omega
  have hLcR : (Nat.clog 2 (L + 1) : ℝ) ≤ lam + 1 := by exact_mod_cast hLc
  unfold phiL scF scG
  push_cast
  push_cast at hCL
  have hκ : (0 : ℝ) ≤ κ := Nat.cast_nonneg _
  have hκM : (0 : ℝ) ≤ κM := Nat.cast_nonneg _
  set c := (Nat.clog 2 (gradeGran lam) : ℝ) + 1 with hc
  set r := (rpowCeil (cutGran (gradeGran lam) * (gradeGran lam + 1) ^ 2) ((1 : ℝ) / 3) : ℝ)
    with hr
  have hc0 : 0 ≤ c := by positivity
  have hr0 : 0 ≤ r := by positivity
  have hE11 : 1 ≤ E ^ 11 := one_le_pow₀ hE1
  have hE3 : 1 ≤ E ^ 3 := one_le_pow₀ hE1
  have hEE : E ≤ E ^ 3 := by
    calc E = E ^ 1 := (pow_one E).symm
      _ ≤ E ^ 3 := pow_le_pow_right₀ hE1 (by norm_num)
  -- the three factors
  have hFb : (κ : ℝ) * c * r + κ ≤ κ * 14704 * lam * E ^ 11 := by
    have : c * r ≤ 3 * lam * (4901 * E ^ 11) :=
      mul_le_mul hCL hR hr0 (by positivity)
    have h1 : (1 : ℝ) ≤ lam * E ^ 11 := by nlinarith
    nlinarith
  have hGb : (κ : ℝ) * c ≤ κ * (3 * lam) := mul_le_mul_of_nonneg_left hCL hκ
  have hHb : (cutGran (gradeGran lam) : ℝ) + (Nat.clog 2 (L + 1) : ℝ) + 1 ≤ 19368 * E ^ 3 := by
    nlinarith
  have hF0 : 0 ≤ (κ : ℝ) * c * r + κ := by positivity
  have hG0 : 0 ≤ (κ : ℝ) * c := by positivity
  calc (κM : ℝ) * ((κ : ℝ) * c * r + κ) * ((κ : ℝ) * c) *
        ((cutGran (gradeGran lam) : ℝ) + (Nat.clog 2 (L + 1) : ℝ) + 1)
      ≤ (κM : ℝ) * (κ * 14704 * lam * E ^ 11) * (κ * (3 * lam)) * (19368 * E ^ 3) := by
        gcongr
    _ = (κM * κ ^ 2 * 14704 * 3 * 19368 : ℝ) * (lam : ℝ) ^ 2 * E ^ 14 := by ring

end bounds


section rest

variable {lam : ℕ}

/-- The chord bound of a leaf of grade `g`. -/
noncomputable def leafW (g : ℕ) : ℕ := 60 * (2 * 2 ^ g + 7) / gradeGran g

theorem leafW_le (g : ℕ) : leafW g ≤ 540 * 2 ^ (g - ceilBeta g) := by
  unfold leafW
  have hcb := ceilBeta_le g
  have h1 : 60 * (2 * 2 ^ g + 7) ≤ 540 * 2 ^ g := by
    have := Nat.one_le_two_pow (n := g); omega
  have h2 : 2 ^ ceilBeta g ≤ gradeGran g := two_pow_ceilBeta_le_gradeGran g
  have h3 : 2 ^ g = 2 ^ ceilBeta g * 2 ^ (g - ceilBeta g) := by
    rw [← pow_add]; congr 1; omega
  calc 60 * (2 * 2 ^ g + 7) / gradeGran g ≤ 540 * 2 ^ g / 2 ^ ceilBeta g :=
        Nat.div_le_div h1 h2 (by positivity)
    _ = 540 * 2 ^ (g - ceilBeta g) := by
        rw [h3, show 540 * (2 ^ ceilBeta g * 2 ^ (g - ceilBeta g)) =
          2 ^ ceilBeta g * (540 * 2 ^ (g - ceilBeta g)) by ring,
          Nat.mul_div_cancel_left _ (by positivity)]

/-- **The chords of the leaves**: `≤ 10800 E^60`. -/
theorem leafKb_le {a L : ℕ} (h1 : 1 ≤ lam) (hL : L ≤ 2 ^ lam) :
    (leafKb lam a L : ℝ) ≤ 10800 * ((2 : ℝ) ^ ((lam : ℝ) / 75)) ^ 60 := by
  have hsub : leafKb lam a L ≤ ((leafShp lam (a + L) a).map kb).sum :=
    sublist_sum_le ((List.filter_sublist).map kb)
  have hmap : (leafShp lam (a + L) a).map kb = (cover lam (a + L) a).map fun q => leafW q.1 := by
    unfold leafShp; rw [List.map_map]; rfl
  have hw := cover_weight_le (b := a + L) (x := a) leafW h1 (by omega)
  rw [← hmap] at hw
  have hsum : ∑ g ∈ range lam, leafW g ≤ ∑ g ∈ range lam, 540 * 2 ^ (g - ceilBeta g) :=
    Finset.sum_le_sum fun g _ => leafW_le g
  have hR : ((∑ g ∈ range lam, 540 * 2 ^ (g - ceilBeta g) : ℕ) : ℝ) ≤
      5400 * ((2 : ℝ) ^ ((lam : ℝ) / 75)) ^ 60 := by
    push_cast
    rw [← Finset.mul_sum]
    have := resetCost_le lam
    have e : (2 : ℝ) ^ ((1 - beta) * lam) = ((2 : ℝ) ^ ((lam : ℝ) / 75)) ^ 60 := by
      rw [E_pow, beta_eq]; congr 1; push_cast; ring
    rw [e] at this
    linarith
  have : (leafKb lam a L : ℝ) ≤ 2 * ((∑ g ∈ range lam, 540 * 2 ^ (g - ceilBeta g) : ℕ) : ℝ) := by
    exact_mod_cast (le_trans hsub (le_trans hw (Nat.mul_le_mul_left 2 hsum)))
  linarith

/-- **The chords of the merged nodes**: `(120 L + 420 J) / (γ'_{λ-1} + 1) ≤ 252240 E^60`. -/
theorem mergedKb_le {L J : ℕ} (h1 : 1 ≤ lam) (hL : L ≤ 2 ^ lam) (hJ : J ≤ 2 * lam) :
    (((120 * L + 420 * J) / (gradeGran (lam - 1) + 1) : ℕ) : ℝ) ≤
      252240 * ((2 : ℝ) ^ ((lam : ℝ) / 75)) ^ 60 := by
  set E := (2 : ℝ) ^ ((lam : ℝ) / 75) with hE
  have hE1 : 1 ≤ E := one_le_E lam
  have hl : (lam : ℝ) ≤ 150 * E := lam_le_E lam
  refine le_trans (Nat.cast_div_le) ?_
  have hG0 : E ^ 15 ≤ 2 * ((gradeGran (lam - 1) : ℝ) + 1) := by
    have a1 : ((2 ^ ceilBeta (lam - 1) : ℕ) : ℝ) ≤ gradeGran (lam - 1) := by
      exact_mod_cast two_pow_ceilBeta_le_gradeGran (lam - 1)
    have a2 : E ^ 15 ≤ (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ ((ceilBeta (lam - 1) : ℕ) : ℝ) := by
      rw [hE, E_pow, two_rpow_mul_two_rpow]
      apply two_rpow_le_two_rpow
      have := le_ceilBeta_real (lam - 1)
      have e : ((lam - 1 : ℕ) : ℝ) = (lam : ℝ) - 1 := by rw [Nat.cast_sub h1]; simp
      rw [e] at this; push_cast; linarith
    rw [Real.rpow_natCast, Real.rpow_one] at a2
    push_cast at a1
    linarith
  have hpos : (0 : ℝ) < (gradeGran (lam - 1) : ℝ) + 1 := by positivity
  push_cast
  rw [div_le_iff₀ hpos]
  have hLR : (L : ℝ) ≤ E ^ 75 := by
    have : ((L : ℕ) : ℝ) ≤ ((2 ^ lam : ℕ) : ℝ) := by exact_mod_cast hL
    rw [hE, E_pow]; push_cast at this ⊢
    rw [show (75 : ℝ) * lam / 75 = (lam : ℝ) by ring, Real.rpow_natCast]; exact this
  have hJR : (J : ℝ) ≤ 300 * E := by
    have : (J : ℝ) ≤ 2 * lam := by exact_mod_cast hJ
    linarith
  have hE60 : 0 ≤ E ^ 60 := by positivity
  have hEE : E ≤ E ^ 75 := by
    calc E = E ^ 1 := (pow_one E).symm
      _ ≤ E ^ 75 := pow_le_pow_right₀ hE1 (by norm_num)
  have e75 : E ^ 75 = E ^ 60 * E ^ 15 := by ring
  nlinarith

/-- The constant of one level. -/
def lvK (κM κ : ℕ) : ℕ := κM * κ ^ 2 * 14704 * 3 * 19368 * 263340 + 728

/-- **One level**: `lvBound ≤ K₂ λ² E^74`. -/
theorem lvBound_le (κM κ : ℕ) {a L J : ℕ} (h7 : 7 ≤ lam) (hL : L ≤ 2 ^ lam) (hJ : J ≤ 2 * lam) :
    (lvBound (fun _ => κM) (scF κ) (scG κ) cutGran (gradeGran lam) (gradeGran (lam - 1)) J L
      (leafKb lam a L) : ℝ) ≤
      (lvK κM κ : ℝ) * (lam : ℝ) ^ 2 * ((2 : ℝ) ^ ((lam : ℝ) / 75)) ^ 74 := by
  unfold lvK
  set E := (2 : ℝ) ^ ((lam : ℝ) / 75) with hE
  have hE1 : 1 ≤ E := one_le_E lam
  have hl : (lam : ℝ) ≤ 150 * E := lam_le_E lam
  have hl1 : (1 : ℝ) ≤ lam := by exact_mod_cast (show 1 ≤ lam by omega)
  have hφ := phiL_le κM κ h7 hL
  have hLS := leafKb_le (a := a) (lam := lam) (by omega) hL
  have hM := mergedKb_le (lam := lam) (L := L) (J := J) (by omega) hL hJ
  rw [← hE] at hφ hLS hM
  have hJR : (J : ℝ) ≤ 300 * E ^ 60 := by
    have : (J : ℝ) ≤ 2 * lam := by exact_mod_cast hJ
    have : E ≤ E ^ 60 := by
      calc E = E ^ 1 := (pow_one E).symm
        _ ≤ E ^ 60 := pow_le_pow_right₀ hE1 (by norm_num)
    linarith
  set R := (leafKb lam a L : ℝ) + (((120 * L + 420 * J) / (gradeGran (lam - 1) + 1) : ℕ) : ℝ) +
    (J : ℝ) with hR
  have hRb : R ≤ 263340 * E ^ 60 := by linarith
  have hR0 : 0 ≤ R := by positivity
  set K1 : ℝ := (κM * κ ^ 2 * 14704 * 3 * 19368 : ℝ) with hK1
  have hK1 : 0 ≤ K1 := by positivity
  have hφ0 : (0 : ℝ) ≤ phiL (fun _ => κM) (scF κ) (scG κ) cutGran (gradeGran lam) L :=
    Nat.cast_nonneg _
  have hprod : (phiL (fun _ => κM) (scF κ) (scG κ) cutGran (gradeGran lam) L : ℝ) * R ≤
      K1 * (lam : ℝ) ^ 2 * E ^ 14 * (263340 * E ^ 60) :=
    mul_le_mul hφ hRb hR0 (by positivity)
  have hE74 : 1 ≤ E ^ 74 := one_le_pow₀ hE1
  have hsq : (lam : ℝ) ≤ (lam : ℝ) ^ 2 := by nlinarith
  have hJ2 : (J : ℝ) ≤ 2 * lam := by exact_mod_cast hJ
  unfold lvBound
  push_cast
  rw [← hR] at *
  have hl2E : (lam : ℝ) ^ 2 ≤ (lam : ℝ) ^ 2 * E ^ 74 := by nlinarith
  have e : K1 * (lam : ℝ) ^ 2 * E ^ 14 * (263340 * E ^ 60) =
      K1 * 263340 * ((lam : ℝ) ^ 2 * E ^ 74) := by ring
  nlinarith

/-- **Lemma 4.1's step bound is `O(lemma41Nat λ)`.** -/
theorem l41Big_le (κM κ : ℕ) {a L : ℕ} (h7 : 7 ≤ lam) (_hL1 : 2 ^ (lam - 1) < L)
    (hL : L ≤ 2 ^ lam) :
    l41Big (fun _ => κM) (scF κ) (scG κ) cutGran lam a L ≤
      (lvK κM κ + 400) * (lemma41Nat lam + 1) := by
  obtain ⟨K2, hK2⟩ : ∃ K2, lvK κM κ = K2 := ⟨_, rfl⟩
  rw [hK2]
  set j := (cover lam (a + L) a).length with hj
  have hj2 : j ≤ 2 * lam := cover_length_le (by omega) (by omega)
  have hcj : Nat.clog 2 j ≤ Nat.clog 2 lam + 1 := clog_le_of_le_two_mul hj2
  have hlv := lvBound_le κM κ (a := a) (L := L) (J := j) h7 hL hj2
  rw [hK2] at hlv
  set E := (2 : ℝ) ^ ((lam : ℝ) / 75) with hE
  have hE1 : 1 ≤ E := one_le_E lam
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = (lam : ℝ) ^ 2 * ((Nat.clog 2 lam : ℝ) + 1) * E ^ 74 :=
    ⟨_, rfl⟩
  have hN : V ≤ lemma41Nat lam := by
    unfold lemma41Nat
    have e : E ^ 74 = (2 : ℝ) ^ ((74 : ℝ) / 75 * lam) := by
      rw [hE, E_pow]; congr 1; push_cast; ring
    rw [hV, e]; exact Nat.le_ceil _
  have hl1 : (1 : ℝ) ≤ lam := by exact_mod_cast (show 1 ≤ lam by omega)
  have hE74 : 1 ≤ E ^ 74 := one_le_pow₀ hE1
  have hcl0 : (0 : ℝ) ≤ Nat.clog 2 lam := Nat.cast_nonneg _
  have hsq : (lam : ℝ) ≤ (lam : ℝ) ^ 2 := by nlinarith
  have hV1 : (lam : ℝ) ^ 2 ≤ V := by
    have h1 : (1 : ℝ) ≤ ((Nat.clog 2 lam : ℝ) + 1) * E ^ 74 := by nlinarith
    calc (lam : ℝ) ^ 2 = (lam : ℝ) ^ 2 * 1 := by ring
      _ ≤ (lam : ℝ) ^ 2 * (((Nat.clog 2 lam : ℝ) + 1) * E ^ 74) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = V := by rw [hV]; ring
  have hV2 : ((Nat.clog 2 lam : ℝ) + 1) ≤ V := by
    have h1 : (1 : ℝ) ≤ (lam : ℝ) ^ 2 * E ^ 74 := by nlinarith
    calc ((Nat.clog 2 lam : ℝ) + 1) = ((Nat.clog 2 lam : ℝ) + 1) * 1 := by ring
      _ ≤ ((Nat.clog 2 lam : ℝ) + 1) * ((lam : ℝ) ^ 2 * E ^ 74) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = V := by rw [hV]; ring
  have hcjR : (Nat.clog 2 j : ℝ) ≤ (Nat.clog 2 lam : ℝ) + 1 := by exact_mod_cast hcj
  have hjR : (j : ℝ) ≤ 2 * lam := by exact_mod_cast hj2
  have hlvR : (lvBound (fun _ => κM) (scF κ) (scG κ) cutGran (gradeGran lam) (gradeGran (lam - 1))
      j L (leafKb lam a L) : ℝ) + 2 ≤ (K2 : ℝ) * (lam : ℝ) ^ 2 * E ^ 74 + 2 := by linarith
  have hK2 : (0 : ℝ) ≤ K2 := Nat.cast_nonneg _
  have hmain : (Nat.clog 2 j : ℝ) * ((lvBound (fun _ => κM) (scF κ) (scG κ) cutGran
      (gradeGran lam) (gradeGran (lam - 1)) j L (leafKb lam a L) : ℝ) + 2) ≤
      (K2 : ℝ) * V + 2 * V := by
    have h0 : (0 : ℝ) ≤ (lvBound (fun _ => κM) (scF κ) (scG κ) cutGran (gradeGran lam)
      (gradeGran (lam - 1)) j L (leafKb lam a L) : ℝ) + 2 := by positivity
    calc (Nat.clog 2 j : ℝ) * ((lvBound (fun _ => κM) (scF κ) (scG κ) cutGran
          (gradeGran lam) (gradeGran (lam - 1)) j L (leafKb lam a L) : ℝ) + 2)
        ≤ ((Nat.clog 2 lam : ℝ) + 1) * ((K2 : ℝ) * (lam : ℝ) ^ 2 * E ^ 74 + 2) :=
          mul_le_mul hcjR hlvR h0 (by positivity)
      _ = (K2 : ℝ) * V + 2 * ((Nat.clog 2 lam : ℝ) + 1) := by rw [hV]; ring
      _ ≤ (K2 : ℝ) * V + 2 * V := by linarith
  have hbig : (l41Big (fun _ => κM) (scF κ) (scG κ) cutGran lam a L : ℝ) ≤
      ((K2 + 400 : ℕ) : ℝ) * V := by
    unfold l41Big
    rw [← hj]
    push_cast
    have : 40 * (lam : ℝ) ^ 2 + 169 * lam + 84 + 11 * j ≤ 315 * (lam : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hfin : ((K2 + 400 : ℕ) : ℝ) * V ≤ ((K2 + 400 : ℕ) : ℝ) * ((lemma41Nat lam : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  have : (l41Big (fun _ => κM) (scF κ) (scG κ) cutGran lam a L : ℝ) ≤
      (((K2 + 400) * (lemma41Nat lam + 1) : ℕ) : ℝ) := by
    push_cast at hfin hbig ⊢; linarith
  exact_mod_cast this

end rest

end

end Chazelle.Core.L41
