/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.SeibergDecomp
public import DOZZ.GMC.SharpMoments.SeibergPieces

/-! # Positive moments of the Coulomb mass

Below the bulk threshold and every insertion threshold, including the one at infinity, the
Coulomb mass has a finite moment of every positive order: the root pieces are weighted local
masses, the bulk piece is the mass of a bounded disk, and the exterior piece is a weighted local
mass of the inverted measure, which has the law of the original one. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Integrals against an `IsGMCOf` version of a fixed measurable function are a.e. measurable. -/
theorem gmc_lintegral_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (f : ℂ → ℝ≥0∞) (hf : Measurable f) :
    AEMeasurable (fun ω => ∫⁻ x, f x ∂M ω) P := by
  simpa using gmc_setLIntegral_aemeasurable P X hX γ hγ hγ2 M hM f hf Set.univ MeasurableSet.univ

/-- Coulomb masses of an `IsGMCOf` version are a.e. measurable. -/
theorem gmc_coulombMass_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {N : ℕ} (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf : ℝ) :
    AEMeasurable (fun ω => coulombMass γ (M ω) α z αinf) P := by
  simp only [coulombMass_eq_lintegral_coulombWeight]
  exact gmc_lintegral_aemeasurable P X hX γ hγ hγ2 M hM _ (measurable_coulombWeight γ α z αinf)

/-- A constant multiple of a positive power of an a.e. measurable function with finite
expectation has finite expectation. -/
theorem lintegral_const_mul_rpow_lt_top {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → ℝ≥0∞} (hf : AEMeasurable f P) {c : ℝ≥0∞} (hc : c ≠ ⊤) {t : ℝ} (ht : 0 < t)
    (hfin : ∫⁻ ω, f ω ^ t ∂P < ⊤) :
    ∫⁻ ω, (c * f ω) ^ t ∂P < ⊤ := by
  rw [lintegral_congr fun ω => ENNReal.mul_rpow_of_nonneg c (f ω) ht.le,
    lintegral_const_mul'' _ (hf.pow_const t)]
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg ht.le hc) hfin

theorem lintegral_rpow_le_of_le_pieces
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}
    (Y : Ω → ℝ≥0∞) (Xr : Fin N → Ω → ℝ≥0∞) (B V : Ω → ℝ≥0∞) (a : Fin N → ℝ≥0∞) (b e : ℝ≥0∞)
    (hXr : ∀ k, AEMeasurable (Xr k) P) (hB : AEMeasurable B P) (hV : AEMeasurable V P)
    (hY : ∀ᵐ ω ∂P, Y ω ≤ ∑ k, a k * Xr k ω + b * B ω + e * V ω) {t : ℝ} (ht : 0 < t) :
    ∫⁻ ω, Y ω ^ t ∂P ≤
      2 ^ t * (2 ^ t * ((N : ℝ≥0∞) ^ t * ∑ k, a k ^ t * ∫⁻ ω, Xr k ω ^ t ∂P +
        b ^ t * ∫⁻ ω, B ω ^ t ∂P) + e ^ t * ∫⁻ ω, V ω ^ t ∂P) := by
  have hcard : ((Finset.univ : Finset (Fin N)).card : ℝ≥0∞) = N := by
    rw [Finset.card_univ, Fintype.card_fin]
  have hpt : ∀ᵐ ω ∂P, Y ω ^ t ≤
      2 ^ t * (2 ^ t * ((N : ℝ≥0∞) ^ t * ∑ k, a k ^ t * Xr k ω ^ t + b ^ t * B ω ^ t) +
        e ^ t * V ω ^ t) := by
    filter_upwards [hY] with ω hω
    calc Y ω ^ t ≤ ((∑ k, a k * Xr k ω + b * B ω) + e * V ω) ^ t :=
          ENNReal.rpow_le_rpow hω ht.le
      _ ≤ 2 ^ t * ((∑ k, a k * Xr k ω + b * B ω) ^ t + (e * V ω) ^ t) :=
          ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow _ _ ht.le
      _ ≤ 2 ^ t * (2 ^ t * ((∑ k, a k * Xr k ω) ^ t + (b * B ω) ^ t) + (e * V ω) ^ t) := by
          gcongr
          exact ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow _ _ ht.le
      _ ≤ 2 ^ t * (2 ^ t * ((N : ℝ≥0∞) ^ t * ∑ k, (a k * Xr k ω) ^ t + (b * B ω) ^ t) +
            (e * V ω) ^ t) := by
          gcongr
          rw [← hcard]
          exact ennreal_finset_sum_rpow_le_card_rpow_sum_of_pos _ _ ht
      _ = _ := by simp only [ENNReal.mul_rpow_of_nonneg _ _ ht.le]
  have hXk : ∀ k ∈ (Finset.univ : Finset (Fin N)),
      AEMeasurable (fun ω => a k ^ t * Xr k ω ^ t) P := fun k _ =>
    aemeasurable_const.mul ((hXr k).pow_const t)
  have hS : AEMeasurable (fun ω => ∑ k, a k ^ t * Xr k ω ^ t) P :=
    Finset.aemeasurable_fun_sum _ hXk
  have hA : AEMeasurable (fun ω => (N : ℝ≥0∞) ^ t * ∑ k, a k ^ t * Xr k ω ^ t) P :=
    aemeasurable_const.mul hS
  have hAB : AEMeasurable (fun ω => (N : ℝ≥0∞) ^ t * ∑ k, a k ^ t * Xr k ω ^ t +
      b ^ t * B ω ^ t) P := hA.add (aemeasurable_const.mul (hB.pow_const t))
  have hLAB : AEMeasurable (fun ω => 2 ^ t * ((N : ℝ≥0∞) ^ t * ∑ k, a k ^ t * Xr k ω ^ t +
      b ^ t * B ω ^ t)) P := aemeasurable_const.mul hAB
  have hall : AEMeasurable (fun ω => 2 ^ t * ((N : ℝ≥0∞) ^ t * ∑ k, a k ^ t * Xr k ω ^ t +
      b ^ t * B ω ^ t) + e ^ t * V ω ^ t) P :=
    hLAB.add (aemeasurable_const.mul (hV.pow_const t))
  refine (lintegral_mono_ae hpt).trans (le_of_eq ?_)
  rw [lintegral_const_mul'' _ hall, lintegral_add_left' hLAB, lintegral_const_mul'' _ hAB,
    lintegral_add_left' hA, lintegral_const_mul'' _ hS, lintegral_finsetSum' _ hXk,
    lintegral_const_mul'' _ (hB.pow_const t), lintegral_const_mul'' _ (hV.pow_const t)]
  have hk : ∀ k, ∫⁻ ω, a k ^ t * Xr k ω ^ t ∂P = a k ^ t * ∫⁻ ω, Xr k ω ^ t ∂P := fun k =>
    lintegral_const_mul'' _ ((hXr k).pow_const t)
  simp only [hk]

/-- Positive moments of the Coulomb mass are bounded by explicit multiples of the moments of its
pieces. -/
theorem coulombMass_moment_le_pieces
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {N : ℕ} (z : Fin N → ℂ) (α : Fin N → ℝ) (αinf : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ j k, j ≠ k → 2 * δ ≤ ‖z j - z k‖) {Rr : ℝ} (hRr1 : 1 ≤ Rr)
    (hzRr : ∀ j, 2 * ‖z j‖ ≤ Rr) (t : ℝ) (ht : 0 < t) :
    ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α z αinf) t ∂P ≤
      2 ^ t * (2 ^ t * ((N : ℝ≥0∞) ^ t *
          ∑ k, ENNReal.ofReal (((2 + 2 * ∑ j, ‖z j‖) / δ) ^
            (∑ j, |γ * α j| + |γ * αinf|)) ^ t * weightedGmcBallMoment P M γ (α k) (z k) δ t +
        ENNReal.ofReal (((1 + Rr + ∑ j, ‖z j‖) / δ) ^ (∑ j, |γ * α j| + |γ * αinf|)) ^ t *
          gmcMassMoment P M (Metric.closedBall 0 Rr) t) +
        ENNReal.ofReal ((2 : ℝ) ^ (∑ j, |γ * α j|)) ^ t *
          weightedGmcBallMoment P M γ αinf 0 (1 / Rr) t) := by
  have hRr0 : 0 < Rr := by linarith
  set cR : ℝ≥0∞ := ENNReal.ofReal (((2 + 2 * ∑ j, ‖z j‖) / δ) ^
    (∑ j, |γ * α j| + |γ * αinf|)) with hcR
  set cB : ℝ≥0∞ := ENNReal.ofReal (((1 + Rr + ∑ j, ‖z j‖) / δ) ^
    (∑ j, |γ * α j| + |γ * αinf|)) with hcB
  set cE : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (∑ j, |γ * α j|)) with hcE
  set W : Fin N → Ω → ℝ≥0∞ := fun k ω => weightedGmcBallMass γ (M ω) (α k) (z k) δ with hW
  set MB : Ω → ℝ≥0∞ := fun ω => M ω (Metric.closedBall 0 Rr) with hMB
  set V : Ω → ℝ≥0∞ := fun ω => ∫⁻ x in {x : ℂ | Rr < ‖x‖},
    ENNReal.rpow (ENNReal.ofReal ‖x‖) (γ * αinf) ∂M ω with hV
  have hWm  := fun k =>
    gmc_weighted_mass_aemeasurable P X hX γ hγ hγ2 M hM (α k) (z k) δ
  have hMBm : AEMeasurable MB P :=
    gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM _
      Metric.isClosed_closedBall.measurableSet
  have hg : Measurable fun x : ℂ => ENNReal.rpow (ENNReal.ofReal ‖x‖) (γ * αinf) :=
    (ENNReal.continuous_rpow_const (y := γ * αinf)).measurable.comp
      (ENNReal.measurable_ofReal.comp measurable_norm)
  have hVm : AEMeasurable V P :=
    gmc_setLIntegral_aemeasurable P X hX γ hγ hγ2 M hM _ hg _
      (measurableSet_lt measurable_const measurable_norm)
  have hdec : ∀ᵐ ω ∂P, coulombMass γ (M ω) α z αinf ≤
      (∑ k, cR * W k ω) + cB * MB ω + cE * V ω := by
    filter_upwards [ae_all_iff.mpr (fun k => gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM (z k))]
      with ω hω
    exact coulombMass_le_pieces (M ω) γ α z αinf hδ hδ1 hsep hω hRr1 hzRr
  refine (lintegral_rpow_le_of_le_pieces _ W MB V (fun _ => cR) cB cE hWm hMBm hVm hdec ht).trans ?_
  gcongr <;> first | exact le_rfl | exact gmc_exterior_moment_le_weighted P X hX γ hγ hγ2 M hM αinf hRr0 t ht.le

/-- Below the bulk threshold and every insertion threshold, the Coulomb mass has a finite moment
of every positive order. -/
theorem coulombMass_moment_lt_top_of_pos
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {N : ℕ} (z : Fin N → ℂ) (hz : Function.Injective z) (α : Fin N → ℝ) (αinf : ℝ)
    (t : ℝ) (ht : 0 < t) (htb : t < 4 / γ ^ 2) (hti : ∀ k, t < 2 / γ * (Q γ - α k))
    (htinf : t < 2 / γ * (Q γ - αinf)) :
    ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α z αinf) t ∂P < ⊤ := by
  obtain ⟨δ, hδ, hδ8, hsep⟩ := exists_root_separation z hz
  obtain ⟨hR, hzR⟩ := coulomb_exterior_radius_bounds z
  refine (coulombMass_moment_le_pieces P X hX γ hγ hγ2 M hM z α αinf
    hδ (hδ8.trans (by norm_num)) hsep hR hzR t ht).trans_lt ?_
  have hroot k := weightedGmcBallMoment_lt_top_of_sharp_range P X hX γ hγ hγ2 M hM
    (α k) (z k) δ hδ t ht (lt_min htb (hti k))
  have hbulk := gmc_bounded_moment_lt_top P X hX γ hγ hγ2 M hM _
    (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 + 2 * ∑ j, ‖z j‖)) t ht.le htb
  have hext := weightedGmcBallMoment_lt_top_of_sharp_range P X hX γ hγ hγ2 M hM αinf 0
    (1 / (1 + 2 * ∑ j, ‖z j‖)) (by positivity) t ht (lt_min htb htinf)
  repeat' first
    | apply ENNReal.mul_lt_top
    | apply ENNReal.add_lt_top.mpr; constructor
    | apply ENNReal.sum_lt_top.mpr; intro k hk
  all_goals first | exact hroot _ | assumption | apply ENNReal.rpow_lt_top_of_nonneg ht.le; finiteness

/-- A lower integral of an a.e. positive a.e. measurable function against a probability measure
is positive. -/
theorem lintegral_pos_of_ae_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ≥0∞} (hf : AEMeasurable f P) (h : ∀ᵐ ω ∂P, 0 < f ω) :
    0 < ∫⁻ ω, f ω ∂P := by
  refine pos_iff_ne_zero.mpr fun h0 => ?_
  have hz := (lintegral_eq_zero_iff' hf).mp h0
  obtain ⟨ω, hω1, hω2⟩ := (h.and hz).exists
  exact (ne_of_gt hω1) hω2

/-- Small positive moments give a.e. finiteness for subcritical insertions. -/
theorem coulombMass_ae_lt_top {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {N : ℕ} (z : Fin N → ℂ) (hz : Function.Injective z) (α : Fin N → ℝ) (αinf : ℝ)
    (hα : ∀ k, α k < Q γ) (hαinf : αinf < Q γ) :
    ∀ᵐ ω ∂P, coulombMass γ (M ω) α z αinf < ⊤ := by
  have e₁ : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioo 0 (4 / γ ^ 2) :=
    Ioo_mem_nhdsGT (by positivity)
  have e₂ : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioo 0 (2 / γ * (Q γ - αinf)) :=
    Ioo_mem_nhdsGT (mul_pos (by positivity) (sub_pos.mpr hαinf))
  have e₃ : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ k, t ∈ Set.Ioo 0 (2 / γ * (Q γ - α k)) :=
    eventually_all.mpr fun k => Ioo_mem_nhdsGT (mul_pos (by positivity) (sub_pos.mpr (hα k)))
  obtain ⟨t, ht, hi, hk⟩ := (e₁.and (e₂.and e₃)).exists
  have h := coulombMass_moment_lt_top_of_pos P X hX γ hγ hγ2 M hM z hz α αinf t
    ht.1 ht.2 (fun k => (hk k).2) hi.2
  have hm := gmc_coulombMass_aemeasurable P X hX γ hγ hγ2 M hM α z αinf
  exact (ae_lt_top' (hm.pow_const t) h.ne).mono fun _ =>
    (ENNReal.rpow_lt_top_iff_of_pos ht.1).mp

/-- Positivity needs no moment hypotheses: the mass dominates a positive exterior disk mass. -/
theorem coulombMass_ae_pos {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf : ℝ) :
    ∀ᵐ ω ∂P, 0 < coulombMass γ (M ω) α z αinf := by
  obtain ⟨hR, hzR⟩ := coulomb_exterior_radius_bounds z
  have hB := gmc_ball_mass_pos_ae P X hX γ hγ hγ2 M hM
    (((1 + 2 * ∑ j, ‖z j‖ + 1 : ℝ)) : ℂ) (1 / 8) (by norm_num)
  filter_upwards [hB] with ω hω
  exact lt_of_lt_of_le (by positivity) (coulombMass_ge_exterior_ball (M ω) γ α z αinf hR hzR)

/-- The global extended moment on `U_N`. -/
theorem equatorGFF_extendedSeiberg_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) {N : ℕ} (z : Fin N → ℂ) (hz : Function.Injective z)
    (α : Fin N → ℝ) (αinf : ℝ) (hαQ : ∀ k, α k < Q γ) (hαinf : αinf < Q γ)
    (hbulk : (2 * Q γ - (∑ k, α k + αinf)) / γ < 4 / γ ^ 2)
    (hins : ∀ k, (2 * Q γ - (∑ k, α k + αinf)) / γ < 2 / γ * (Q γ - α k))
    (hinsinf : (2 * Q γ - (∑ k, α k + αinf)) / γ < 2 / γ * (Q γ - αinf)) :
    0 < ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α z αinf)
        ((2 * Q γ - (∑ k, α k + αinf)) / γ) ∂P ∧
      ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α z αinf)
        ((2 * Q γ - (∑ k, α k + αinf)) / γ) ∂P < ⊤ := by
  let _ : IsProbabilityMeasure P := hX.1
  set s : ℝ := (2 * Q γ - (∑ k, α k + αinf)) / γ with hs
  set Z : Ω → ℝ≥0∞ := fun ω => coulombMass γ (M ω) α z αinf with hZ
  have hZm : AEMeasurable Z P := gmc_coulombMass_aemeasurable P X hX γ hγ hγ2 M hM α z αinf
  -- the lower bound by a fixed exterior disk
  set c : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (-∑ j, |γ * α j|)) *
    ENNReal.ofReal ((1 + 2 * ∑ j, ‖z j‖ + 2) ^ (-|γ * αinf|)) with hc
  set B : Set ℂ := Metric.ball (((1 + 2 * ∑ j, ‖z j‖ + 1 : ℝ)) : ℂ) (1 / 8) with hB
  have hc0 : c ≠ 0 := by
    have hsum : 0 ≤ ∑ j, ‖z j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
    refine mul_ne_zero ?_ ?_
    · positivity
    · exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by linarith) _)).ne'
  have hctop : c ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  obtain ⟨hRr1, hzRr⟩ := coulomb_exterior_radius_bounds z
  have hlow : ∀ ω, c * M ω B ≤ Z ω := fun ω =>
    coulombMass_ge_exterior_ball (M ω) γ α z αinf hRr1 hzRr
  have hBm : AEMeasurable (fun ω => M ω B) P :=
    gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM B Metric.isOpen_ball.measurableSet
  -- almost surely the Coulomb mass is positive and finite
  have hZfin := coulombMass_ae_lt_top P X hX γ hγ hγ2 M hM z hz α αinf hαQ hαinf
  have hZpos := coulombMass_ae_pos P X hX γ hγ hγ2 M hM α z αinf
  refine ⟨lintegral_pos_of_ae_pos (hZm.pow_const s) ?_, ?_⟩
  · filter_upwards [hZfin, hZpos] with ω h1 h2
    exact ENNReal.rpow_pos h2 h1.ne
  rcases lt_trichotomy s 0 with hneg | hzero | hpos
  · -- negative Seiberg exponent: the inverse moments of a fixed disk
    calc ∫⁻ ω, ENNReal.rpow (Z ω) s ∂P ≤ ∫⁻ ω, (c * M ω B) ^ s ∂P :=
          lintegral_mono fun ω => ennreal_rpow_antitone_of_nonpos (hlow ω) hneg.le
      _ = c ^ s * gmcMassMoment P M B s := by
          rw [lintegral_congr fun ω => ennreal_mul_rpow_of_ne_zero_ne_top c (M ω B) hc0 hctop s,
            lintegral_const_mul'' _ (hBm.pow_const s)]
          rfl
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.rpow_ne_top_of_ne_zero hc0 hctop).lt_top
          (gmc_ball_moment_lt_top_any_center P X hX γ hγ hγ2 M hM _ (1 / 8) (by norm_num) le_rfl
            s (by linarith))
  · -- zero Seiberg exponent
    have h1 : ∀ ω, ENNReal.rpow (coulombMass γ (M ω) α z αinf) s = 1 := fun ω => by
      rw [hzero]
      exact ENNReal.rpow_zero
    simp only [h1, lintegral_const, measure_univ, mul_one]
    exact ENNReal.one_lt_top
  · -- positive Seiberg exponent
    apply coulombMass_moment_lt_top_of_pos <;> assumption

end DOZZ.Proofs
