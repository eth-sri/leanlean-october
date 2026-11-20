/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.CutoffUIBound
public import DOZZ.GMC.SharpMoments.CutoffConvergence

/-! # The bad region of regularized Coulomb masses

The bad region consists of small disks about the roots and the exterior of a large disk. Once the
cutoff scale is below the disk radius, the cutoff Coulomb mass of the bad region has a small
moment, uniformly over compact parameter sets: the root disks are cutoff weighted masses of small
disks, and the far exterior decays by exact exterior scaling. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The bad region: disks of radius `ρ` about the roots and the exterior of the disk of radius
`1/ρ`. -/
def coulombBadRegion {N : ℕ} (z : Fin N → ℂ) (ρ : ℝ) : Set ℂ :=
  (⋃ k, Metric.ball (z k) ρ) ∪ {x : ℂ | 1 / ρ < ‖x‖}

section
variable {N : ℕ} (z : Fin N → ℂ) (ρ : ℝ)
include N

theorem measurableSet_coulombBadRegion :
    MeasurableSet (coulombBadRegion z ρ) :=
  (MeasurableSet.iUnion fun _ => Metric.isOpen_ball.measurableSet).union
    (measurableSet_lt measurable_const measurable_norm)

theorem mem_coulombBadRegion_compl (x : ℂ) :
    x ∈ (coulombBadRegion z ρ)ᶜ ↔ ‖x‖ ≤ 1 / ρ ∧ ∀ k, ρ ≤ ‖x - z k‖ := by
  simp only [coulombBadRegion, Set.mem_compl_iff, Set.mem_union, Set.mem_iUnion,
    Metric.mem_ball, dist_eq_norm, not_or, not_exists, not_lt, Set.mem_ofPred_eq]
  tauto

end

/-- The bad part of a weighted mass is at most the sum of its root and exterior pieces. -/
theorem lintegral_coulombBadRegion_le {N : ℕ} (μ : Measure ℂ) (G : ℂ → ℝ≥0∞)
    (z : Fin N → ℂ) (ρ : ℝ) :
    ∫⁻ x in coulombBadRegion z ρ, G x ∂μ ≤
      ∑ k, ∫⁻ x in Metric.ball (z k) ρ, G x ∂μ + ∫⁻ x in {x : ℂ | 1 / ρ < ‖x‖}, G x ∂μ := by
  refine (lintegral_union_le _ _ _).trans (add_le_add_left ?_ _)
  simpa only [tsum_fintype] using (lintegral_iUnion_le (μ := μ) (fun k => Metric.ball (z k) ρ) G)

/-- Enlarge the strict exterior to its closure after a pointwise comparison. -/
theorem lintegral_coulombExterior_le (μ : Measure ℂ) (G F : ℂ → ℝ≥0∞)
    (hF : Measurable F) (R : ℝ) (a : ℝ≥0∞) (h : ∀ x : ℂ, R < ‖x‖ → G x ≤ a * F x) :
    ∫⁻ x in {x : ℂ | R < ‖x‖}, G x ∂μ ≤ a * ∫⁻ x in {x : ℂ | R ≤ ‖x‖}, F x ∂μ := by
  rw [← lintegral_const_mul _ hF]
  exact (setLIntegral_mono' (measurableSet_lt measurable_const measurable_norm) h).trans
    (lintegral_mono_set fun _ hx => (show R < ‖_‖ from hx).le)

/-- The far exterior coefficient: `(2/ρ)^{βt} (ρ R₀)^{ξ} ≤ 2^{Et} R₀^{4t} ρ^κ`. -/
theorem farExterior_coeff_le {ρ R0 β E t ξ κ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hR0 : 1 ≤ R0)
    (hβE : β ≤ E) (ht : 0 < t) (hξ : ξ ≤ 4 * t) (hκ : κ ≤ ξ - β * t) :
    (2 * (1 / ρ)) ^ (β * t) * ((1 / ρ) / R0) ^ (-ξ) ≤ 2 ^ (E * t) * R0 ^ (4 * t) * ρ ^ κ := by
  have hR0pos : 0 < R0 := by linarith
  have h1 : (2 * (1 / ρ)) ^ (β * t) = 2 ^ (β * t) * ρ ^ (-(β * t)) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), one_div, Real.inv_rpow hρ.le,
      ← Real.rpow_neg hρ.le]
  have h2 : ((1 / ρ) / R0) ^ (-ξ) = ρ ^ ξ * R0 ^ ξ := by
    rw [div_div, one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), neg_neg,
      Real.mul_rpow hρ.le hR0pos.le]
  rw [h1, h2]
  have h3 : 2 ^ (β * t) * ρ ^ (-(β * t)) * (ρ ^ ξ * R0 ^ ξ) =
      2 ^ (β * t) * R0 ^ ξ * ρ ^ (ξ - β * t) := by
    rw [sub_eq_add_neg, Real.rpow_add hρ]
    ring
  rw [h3]
  have hb : (2 : ℝ) ^ (β * t) ≤ 2 ^ (E * t) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_right hβE ht.le)
  have hr  := Real.rpow_le_rpow_of_exponent_le hR0 hξ
  have hp  := Real.rpow_le_rpow_of_exponent_ge hρ hρ1 hκ
  calc 2 ^ (β * t) * R0 ^ ξ * ρ ^ (ξ - β * t) ≤ 2 ^ (E * t) * R0 ^ (4 * t) * ρ ^ (ξ - β * t) := by
        gcongr
    _ ≤ 2 ^ (E * t) * R0 ^ (4 * t) * ρ ^ κ := by gcongr

/-- Far exterior cutoff moments of the power weight at infinity, uniformly over a compact
parameter set. -/
theorem cutoffUI_far_exterior_moment_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (N : ℕ) (S : Set (CoulombParameters N)) (hS : IsCompact S) {tst : ℝ}
    (htst : 0 < tst)
    (hinf : ∀ c ∈ S, 0 < weightedCutoffSlack (c.1, max c.2.2.2 0, tst))
    {E : ℝ} (hE : 0 ≤ E) (hEinf : ∀ c ∈ S, |c.1 * c.2.2.2| ≤ E) {R0 : ℝ} (hR0 : 2 ≤ R0) :
    ∃ A : ℝ≥0∞, A < ⊤ ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ c ∈ S, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / R0 →
      ∀ r : ℝ, 0 ≤ r →
        ∫⁻ ω, (∫⁻ x in {x : ℂ | 1 / ρ ≤ ‖x‖}, ENNReal.ofReal (‖x‖ ^ max (c.1 * c.2.2.2) 0)
          ∂regularizedGMC P Xc c.1 r ω) ^ tst ∂P ≤ A * ENNReal.ofReal (ρ ^ κ) := by
  classical
  obtain ⟨κ, hκi, hκpos⟩ := ((cutoffUI_eventually_exterior_decay hS (fun _ => tst)
    continuousOn_const hinf).and self_mem_nhdsWithin).exists
  -- the zero-charge disk bound
  obtain ⟨K0, hK0fin, hdb⟩ := cutoffUI_disk_moment_bound P X hX Xc hXc hS
    (fun _ => tst) continuousOn_const hinf htst.le (fun _ _ => le_rfl)
    (show 1 ≤ 2 * R0 + 1 by linarith)
  have hdisk (c : CoulombParameters N) (hc : c ∈ S) (r : ℝ) (hr : 0 ≤ r) :=
    hdb c hc (2 * R0 + 1) (by linarith) le_rfl r hr
  set Gm : ℝ≥0∞ := ((1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ κ) ^ (1 / max 1 tst)) ^ (max 1 tst))⁻¹
    with hGm
  refine ⟨ENNReal.ofReal (2 ^ (E * tst) * R0 ^ (4 * tst)) * K0 * Gm,
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK0fin)
      (geometric_factor_lt_top hκpos), κ, hκpos, fun c hc ρ hρ hρR0 r hr => ?_⟩
  obtain ⟨hγ0, hγ2, -⟩ := (weightedCutoffSlack_pos_iff _).mp (hinf c hc)
  have hρ1 : ρ ≤ 1 := hρR0.trans (by rw [div_le_one (by linarith)]; linarith)
  have hinvρ : R0 ≤ 1 / ρ := by
    rw [le_div_iff₀ hρ]
    rw [le_div_iff₀ (by linarith)] at hρR0
    linarith
  have hK0b : ∀ r' : ℝ, 0 ≤ r' →
      ∫⁻ ω, regularizedGMC P Xc c.1 r' ω (exteriorAnnulus R0 0) ^ tst ∂P ≤ K0 := by
    intro r' hr'
    refine le_trans (lintegral_mono fun ω => ENNReal.rpow_le_rpow (measure_mono ?_) htst.le)
      (hdisk c hc r' hr')
    intro x hx
    rw [Metric.mem_ball, dist_zero_right]
    have := hx.2
    simp only [zero_add, pow_one] at this
    linarith
  have hfar : ∀ r' : ℝ, 0 ≤ r' →
      ∫⁻ ω, regularizedGMC P Xc c.1 r' ω (exteriorAnnulus (1 / ρ) 0) ^ tst ∂P ≤
        ENNReal.ofReal ((1 / ρ / R0) ^ (-(2 * tst + c.1 ^ 2 * tst / 2 -
          c.1 ^ 2 * tst ^ 2 / 2))) * K0 := fun r' hr' =>
    exteriorAnnulus_moment_le_far P X hX Xc hXc c.1 hR0 hinvρ hK0b hr'
  have hext := cutoff_exterior_power_moment_le P X hX Xc hXc c.1 (le_trans hR0 hinvρ)
    (le_max_right (c.1 * c.2.2.2) 0) htst hfar hr
  refine hext.trans ?_
  have hβE  := max_le ((le_abs_self _).trans (hEinf c hc)) hE
  have hξ : 2 * tst + c.1 ^ 2 * tst / 2 - c.1 ^ 2 * tst ^ 2 / 2 ≤ 4 * tst := by
    have hγsq  := pow_lt_pow_left₀ hγ2 hγ0.le two_ne_zero
    have h1  := mul_lt_mul_of_pos_right hγsq htst
    have h2 : 0 ≤ c.1 ^ 2 * tst ^ 2 := by positivity
    linarith only [h1, h2]
  have hcoeff := farExterior_coeff_le (κ := κ) hρ hρ1 (by linarith : (1 : ℝ) ≤ R0)
    hβE htst hξ (hκi c hc)
  have hG := geometric_factor_le hκpos (hκi c hc) (le_refl tst)
  unfold cutoffExteriorDecay at hG
  rw [← mul_assoc (ENNReal.ofReal _) (ENNReal.ofReal _) K0,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
  refine (mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal hcoeff) le_rfl) hG).trans_eq ?_
  rw [ENNReal.ofReal_mul (by positivity)]
  ring

/-- The combined coefficient for the root disks and the far exterior. -/
noncomputable def badRegionMomentCoeff {N : ℕ} (t : ℝ) (a e : ℝ≥0∞)
    (C : Fin N → ℝ≥0∞) (A : ℝ≥0∞) : ℝ≥0∞ :=
  2 ^ t * (2 ^ t * ((N : ℝ≥0∞) ^ t * ∑ k, a ^ t * C k) + e ^ t * A)

theorem badRegionMomentCoeff_lt_top {N : ℕ} {t : ℝ} (ht : 0 < t) {a e : ℝ≥0∞}
    (ha : a ≠ ⊤) (he : e ≠ ⊤) {C : Fin N → ℝ≥0∞} (hC : ∀ k, C k < ⊤)
    {A : ℝ≥0∞} (hA : A < ⊤) : badRegionMomentCoeff t a e C A < ⊤ := by
  have hr {x : ℝ≥0∞} (hx : x ≠ ⊤) : x ^ t < ⊤ := ENNReal.rpow_lt_top_of_nonneg ht.le hx
  have h2 : (2 : ℝ≥0∞) ^ t < ⊤ := hr (by norm_num)
  exact ENNReal.mul_lt_top h2 (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top h2 (ENNReal.mul_lt_top
    (hr (ENNReal.natCast_ne_top N)) (ENNReal.sum_lt_top.mpr fun k _ => ENNReal.mul_lt_top (hr ha) (hC k))),
    ENNReal.mul_lt_top (hr he) hA⟩)

/-- Root and exterior moments with a shared small-radius factor give a bound for the whole bad part. -/
theorem badRegion_moment_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}
    {Y V : Ω → ℝ≥0∞} {W : Fin N → Ω → ℝ≥0∞} {a e A L : ℝ≥0∞} {C : Fin N → ℝ≥0∞}
    (hW : ∀ k, AEMeasurable (W k) P) (hV : AEMeasurable V P)
    (hY : ∀ᵐ ω ∂P, Y ω ≤ ∑ k, a * W k ω + e * V ω) {t : ℝ} (ht : 0 < t)
    (hr : ∀ k, ∫⁻ ω, W k ω ^ t ∂P ≤ C k * L) (he : ∫⁻ ω, V ω ^ t ∂P ≤ A * L) :
    ∫⁻ ω, Y ω ^ t ∂P ≤ badRegionMomentCoeff t a e C A * L := by
  have hm := lintegral_rpow_le_of_le_pieces Y W (fun _ => 0) V (fun _ => a) 0 e
    hW aemeasurable_const hV (by simpa only [mul_zero, add_zero] using hY) ht
  simp only [ENNReal.zero_rpow_of_pos ht, zero_mul, add_zero] at hm
  refine (hm.trans (show _ ≤ 2 ^ t * (2 ^ t * ((N : ℝ≥0∞) ^ t *
    ∑ k, a ^ t * (C k * L)) + e ^ t * (A * L)) from ?_)).trans_eq ?_
  · gcongr with k hk
    exact hr k
  · simp only [← mul_assoc (a ^ t), ← Finset.sum_mul, badRegionMomentCoeff]
    ring

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
include Ω X hX hXc

/-- Replace the local radius exponent by one common positive lower bound. -/
theorem cutoffUI_root_moment_decay
    {N : ℕ} {S : Set (CoulombParameters N)} (hS : IsCompact S) (t : ℝ)
    (a : Fin N → CoulombParameters N → ℝ) (ha : ∀ k, ContinuousOn (a k) S)
    (h : ∀ c ∈ S, ∀ k, 0 < weightedCutoffSlack (c.1, a k c, t)) {Z : ℝ}
    (hZ : ∀ c ∈ S, ∑ j, ‖c.2.1 j‖ ≤ Z) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ C : Fin N → ℝ, (∀ k, 0 < C k) ∧
      ∀ k c, c ∈ S → ∀ δ ρ : ℝ, 0 < δ → δ ≤ ρ → ρ ≤ 1 →
        ∫⁻ ω, cutoffWeightedGmcBallMass P Xc c.1 (a k c) (c.2.1 k) ρ δ ω ^ t ∂P ≤
          ENNReal.ofReal (C k) * ENNReal.ofReal (ρ ^ κ) := by
  have hζ k := cutoffUI_eventually_root_decay hS (a k) (ha k) t (fun c hc => h c hc k)
  obtain ⟨κ, hκ, hκpos⟩ := ((eventually_all.mpr hζ).and self_mem_nhdsWithin).exists
  have hC k := cutoffUI_root_moment_bound P X hX Xc hXc hS (a k) (fun _ => t) (ha k)
    continuousOn_const (fun c hc => h c hc k) k hZ
  choose C hC0 hb using hC
  refine ⟨κ, hκpos, C, hC0, fun k c hc δ ρ hδ hδρ hρ => (hb k c hc δ ρ hδ hδρ hρ).trans ?_⟩
  rw [← ENNReal.ofReal_mul (hC0 k).le]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge (hδ.trans_le hδρ) hρ (hκ k c hc)) (hC0 k).le)

/-- Cutoff moments of the bad part are uniformly small once the cutoff scale is below the disk
radius. -/
theorem cutoffUI_bad_cutoff_moment_le (partition : GMCChartPartition)
    (N : ℕ) (S : Set (CoulombParameters N)) (hS : IsCompact S) {tst : ℝ}
    (htst : 0 < tst)
    (hroot : ∀ c ∈ S, ∀ k, 0 < weightedCutoffSlack (c.1, c.2.2.1 k, tst))
    (hinf : ∀ c ∈ S, 0 < weightedCutoffSlack (c.1, max c.2.2.2 0, tst))
    {ρs : ℝ} (hρs : 0 < ρs) (hρs1 : ρs ≤ 1)
    (hsep : ∀ c ∈ S, ∀ j k, j ≠ k → 2 * ρs ≤ ‖c.2.1 j - c.2.1 k‖) :
    ∃ ρ1 : ℝ, 0 < ρ1 ∧ ∃ A : ℝ≥0∞, A < ⊤ ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ c ∈ S, ∀ ρ : ℝ, 0 < ρ →
      ρ ≤ ρ1 → ∀ r : ℝ, Real.log (1 / ρ) ≤ r →
        ∫⁻ ω, (∫⁻ x in coulombBadRegion c.2.1 ρ,
          coulombCutoffWeight partition c.1 c.2.2.1 c.2.1 c.2.2.2 r x
            ∂regularizedGMC P Xc c.1 r ω) ^ tst ∂P ≤ A * ENNReal.ofReal (ρ ^ κ) := by
  classical
  obtain ⟨Zs, E, hZs, hE, hZc, -, hEα, hEinf⟩ := compact_coulomb_bounds hS
  obtain ⟨κr, hκr, Ck, -, hCkb⟩ := cutoffUI_root_moment_decay P X hX Xc hXc hS tst
    (fun k c => c.2.2.1 k) (fun k => by fun_prop) hroot hZc
  -- partition supports and the exterior radius
  obtain ⟨Rf, Ri, hRf, hRi, hsuppf, hsuppi⟩ := partition_support_bounds partition
  set R0 : ℝ := max (2 * Zs + 2) Rf with hR0def
  have hR0Z : 2 * Zs + 2 ≤ R0 := le_max_left _ _
  have hR02 : 2 ≤ R0 := le_trans (by linarith) hR0Z
  have hsuppf' : ∀ x, partition.finiteWeight x ≠ 0 → ‖x‖ < R0 := fun x hx =>
    lt_of_lt_of_le (hsuppf x hx) (le_max_right _ _)
  -- pointwise bounds for the weight
  obtain ⟨CR, hCR0, hCR⟩ := coulombCutoffWeight_le_root partition N hZs hE hρs hρs1 hRi hsuppi
  obtain ⟨CE, hCE0, hCE⟩ := coulombCutoffWeight_le_exterior partition N hZs hE hR0Z hsuppf'
  obtain ⟨Ae, hAe, κe, hκe, he⟩ := cutoffUI_far_exterior_moment_le P X hX Xc hXc N S hS htst
    hinf hE hEinf hR02
  let κ := min κr κe
  let A := badRegionMomentCoeff tst (ENNReal.ofReal CR) (ENNReal.ofReal CE) (fun k => ENNReal.ofReal (Ck k)) Ae
  refine ⟨min ρs (1 / R0), lt_min hρs (by positivity), A,
    badRegionMomentCoeff_lt_top htst ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
      (fun _ => ENNReal.ofReal_lt_top) hAe, κ, lt_min hκr hκe, ?_⟩
  intro c hc ρ hρ hρ1 r hr
  have hρs'  := hρ1.trans (min_le_left _ _)
  have hρR0  := hρ1.trans (min_le_right _ _)
  have hρ1'  := hρs'.trans hρs1
  have hinvρ : R0 ≤ 1 / ρ := by
    rw [le_div_iff₀ hρ]
    rw [le_div_iff₀ (by linarith)] at hρR0
    linarith
  have hr0 : 0 ≤ r := le_trans (Real.log_nonneg (by rw [le_div_iff₀ hρ]; linarith)) hr
  have hδρ : Real.exp (-r) ≤ ρ := by
    have := Real.exp_le_exp.mpr (neg_le_neg hr)
    rwa [Real.log_div one_ne_zero hρ.ne', Real.log_one, zero_sub, neg_neg, Real.exp_log hρ]
      at this
  have hlog : Real.log (1 / Real.exp (-r)) = r := by
    simp
  -- the pieces, pointwise in the sample
  set cw : Fin N → Ω → ℝ≥0∞ := fun k ω =>
    cutoffWeightedGmcBallMass P Xc c.1 (c.2.2.1 k) (c.2.1 k) ρ (Real.exp (-r)) ω with hcw
  set V : Ω → ℝ≥0∞ := fun ω => ∫⁻ x in {x : ℂ | 1 / ρ ≤ ‖x‖},
    ENNReal.ofReal (‖x‖ ^ max (c.1 * c.2.2.2) 0) ∂regularizedGMC P Xc c.1 r ω with hV
  have hpt : ∀ ω, (∫⁻ x in coulombBadRegion c.2.1 ρ,
      coulombCutoffWeight partition c.1 c.2.2.1 c.2.1 c.2.2.2 r x ∂regularizedGMC P Xc c.1 r ω) ≤
        ∑ k, ENNReal.ofReal CR * cw k ω + ENNReal.ofReal CE * V ω := by
    intro ω
    let μ := regularizedGMC P Xc c.1 r ω
    have hne0 : ∀ᵐ x ∂μ, x ≠ 0 :=
      measure_eq_zero_iff_ae_notMem.mp (regularizedGMC_singleton_eq_zero P Xc c.1 r ω 0)
    refine (lintegral_coulombBadRegion_le μ _ c.2.1 ρ).trans
      (add_le_add (Finset.sum_le_sum fun k _ => ?_) ?_)
    · rw [hcw]
      simp only []
      have hw : Measurable fun x : ℂ =>
          ENNReal.ofReal ((‖x - c.2.1 k‖ + Real.exp (-r)) ^ (-c.1 * c.2.2.1 k)) := by fun_prop
      rw [cutoffWeightedGmcBallMass, hlog, ← lintegral_const_mul _ hw]
      refine setLIntegral_mono_ae' Metric.isOpen_ball.measurableSet ?_
      filter_upwards [hne0] with x hx0 hx
      exact hCR c.1 c.2.2.1 c.2.1 c.2.2.2 r k x hr0 (hZc c hc) (hEα c hc) (hEinf c hc)
        (fun j hj => hsep c hc j k hj) (Metric.ball_subset_ball hρs' hx) hx0
    · exact lintegral_coulombExterior_le μ _ _ (by fun_prop) _ _ fun x hx =>
        hCE c.1 c.2.2.1 c.2.1 c.2.2.2 r x hr0 (hZc c hc) (hEα c hc) (hEinf c hc)
          (hinvρ.trans hx.le)
  have hcwm : ∀ k, AEMeasurable (cw k) P := fun k =>
    (measurable_cutoffWeightedGmcBallMass P X hX Xc hXc _ _ _ _ _).aemeasurable
  have hEm : MeasurableSet {x : ℂ | 1 / ρ ≤ ‖x‖} :=
    measurableSet_le measurable_const measurable_norm
  have hVm : AEMeasurable V P := by
    have hf : Measurable fun x : ℂ => ENNReal.ofReal (‖x‖ ^ max (c.1 * c.2.2.2) 0) :=
      ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)
    have h := (Measure.measurable_lintegral (hf.indicator hEm)).comp
      (regularizedGMC_measurable P X hX Xc hXc c.1 r)
    refine Measurable.aemeasurable ?_
    convert h using 1
    funext ω
    simp only [Function.comp_apply, hV, lintegral_indicator hEm]
  refine badRegion_moment_le hcwm hVm (Eventually.of_forall hpt) htst (fun k => ?_) ?_
  · exact (hCkb k c hc _ ρ (Real.exp_pos _) hδρ hρ1').trans
      (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_exponent_ge hρ hρ1' (min_le_left _ _))))
  · exact (he c hc ρ hρ hρR0 r hr0).trans
      (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_exponent_ge hρ hρ1' (min_le_right _ _))))

end

end DOZZ.Proofs
