/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.WeightedCutoffEstimates

public import DOZZ.GMC.SharpMoments.CutoffUIBound
public import DOZZ.GMC.SharpMoments.CutoffConvergence
public import DOZZ.GMC.SharpMoments.CompactBounds

/-! # The bad region of regularized Coulomb masses

The bad region consists of small disks about the roots and the exterior of a large disk. Once the
cutoff scale is below the disk radius, the cutoff Coulomb mass of the bad region has a small
moment, uniformly over compact parameter sets: the root disks are cutoff weighted masses of small
disks, and the far exterior decays by exact exterior scaling. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {N : ℕ} (z : Fin N → ℂ) (ρ : ℝ)

include N z ρ in
/-- The bad region: disks of radius `ρ` about the roots and the exterior of the disk of radius
`1/ρ`. -/
def coulombBadRegion  : Set ℂ :=
  (⋃ k, Metric.ball (z k) ρ) ∪ {x : ℂ | 1 / ρ < ‖x‖}

include N z ρ in
theorem measurableSet_coulombBadRegion  :
    MeasurableSet (coulombBadRegion z ρ) :=
  (MeasurableSet.iUnion fun _ => Metric.isOpen_ball.measurableSet).union
    (measurableSet_lt measurable_const measurable_norm)

include N z ρ in
theorem mem_coulombBadRegion_compl  (x : ℂ) :
    x ∈ (coulombBadRegion z ρ)ᶜ ↔ ‖x‖ ≤ 1 / ρ ∧ ∀ k, ρ ≤ ‖x - z k‖ := by
  simp only [coulombBadRegion, Set.mem_compl_iff, Set.mem_union, Set.mem_iUnion,
    Metric.mem_ball, dist_eq_norm, not_or, not_exists, not_lt, Set.mem_ofPred_eq]
  tauto

/-- The bad part of a weighted mass is at most the sum of its root and exterior pieces. -/
theorem lintegral_coulombBadRegion_le {N : ℕ} (μ : Measure ℂ) (G : ℂ → ℝ≥0∞)
    (hG : Measurable G) (z : Fin N → ℂ) (ρ : ℝ) :
    ∫⁻ x in coulombBadRegion z ρ, G x ∂μ ≤
      ∑ k, ∫⁻ x in Metric.ball (z k) ρ, G x ∂μ + ∫⁻ x in {x : ℂ | 1 / ρ < ‖x‖}, G x ∂μ := by
  have hBm : ∀ k, MeasurableSet (Metric.ball (z k) ρ) := fun k =>
    Metric.isOpen_ball.measurableSet
  have hEm : MeasurableSet {x : ℂ | 1 / ρ < ‖x‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hS : Measurable fun x => ∑ k, (Metric.ball (z k) ρ).indicator G x :=
    Finset.measurable_fun_sum _ fun k _ => hG.indicator (hBm k)
  rw [← lintegral_indicator (measurableSet_coulombBadRegion z ρ)]
  calc ∫⁻ x, (coulombBadRegion z ρ).indicator G x ∂μ
      ≤ ∫⁻ x, (∑ k, (Metric.ball (z k) ρ).indicator G x +
          {x : ℂ | 1 / ρ < ‖x‖}.indicator G x) ∂μ := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ coulombBadRegion z ρ
        · rw [Set.indicator_of_mem hx]
          rcases hx with hx | hx
          · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
            refine le_trans ?_ (le_add_right le_rfl)
            calc G x = (Metric.ball (z k) ρ).indicator G x :=
                  (Set.indicator_of_mem hk G).symm
              _ ≤ ∑ j, (Metric.ball (z j) ρ).indicator G x :=
                Finset.single_le_sum (f := fun j => (Metric.ball (z j) ρ).indicator G x)
                  (fun _ _ => zero_le) (Finset.mem_univ k)
          · rw [Set.indicator_of_mem hx]
            exact le_add_left le_rfl
        · rw [Set.indicator_of_notMem hx]
          exact zero_le
    _ = _ := by
        rw [lintegral_add_left hS, lintegral_finsetSum _ fun k _ => hG.indicator (hBm k),
          lintegral_indicator hEm]
        simp only [lintegral_indicator (hBm _)]

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
    (N : ℕ) (S : Set (ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ))) (hS : IsCompact S) {tst : ℝ}
    (htst : 0 < tst)
    (hinf : ∀ c ∈ S, 0 < weightedCutoffSlack (c.1, max c.2.2.2 0, tst))
    {E : ℝ} (hE : 0 ≤ E) (hEinf : ∀ c ∈ S, |c.1 * c.2.2.2| ≤ E) {R0 : ℝ} (hR0 : 2 ≤ R0) :
    ∃ A : ℝ≥0∞, A < ⊤ ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ c ∈ S, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / R0 →
      ∀ r : ℝ, 0 ≤ r →
        ∫⁻ ω, (∫⁻ x in {x : ℂ | 1 / ρ ≤ ‖x‖}, ENNReal.ofReal (‖x‖ ^ max (c.1 * c.2.2.2) 0)
          ∂regularizedGMC P Xc c.1 r ω) ^ tst ∂P ≤ A * ENNReal.ofReal (ρ ^ κ) := by
  classical
  let _  := hX.1
  have hadmInf : ∀ c ∈ S, 0 < c.1 ∧ c.1 < 2 ∧ 0 < tst ∧ tst < 4 / c.1 ^ 2 ∧
      tst < 2 / c.1 * (Q c.1 - max c.2.2.2 0) := by
    intro c hc
    have h := (weightedCutoffSlack_pos_iff _).mp (hinf c hc)
    exact ⟨h.1, h.2.1, h.2.2.2.1, (lt_min_iff.mp h.2.2.2.2).1, (lt_min_iff.mp h.2.2.2.2).2⟩
  have hζi : ∀ᶠ κ in 𝓝[>] (0 : ℝ), ∀ c ∈ S,
      κ ≤ 2 * tst + c.1 ^ 2 * tst / 2 - c.1 ^ 2 * tst ^ 2 / 2 - max (c.1 * c.2.2.2) 0 * tst := by
    refine eventually_le_of_isCompact_of_pos hS (by fun_prop) fun c hc => ?_
    obtain ⟨hγ0, -, -, -, htinf⟩ := hadmInf c hc
    have hmax : max (c.1 * c.2.2.2) 0 = c.1 * max c.2.2.2 0 := by
      rw [mul_max_of_nonneg _ _ hγ0.le, mul_zero]
    have hQ : c.1 * Q c.1 = 2 + c.1 ^ 2 / 2 := by
      rw [Q]
      field_simp
    have hp := weightedCutoff_exponent_pos (hinf c hc)
    nlinarith [hQ, hmax]
  obtain ⟨κ, hκi, hκ0⟩ := (hζi.and self_mem_nhdsWithin).exists
  have hκpos : 0 < κ := hκ0
  -- the zero-charge disk bound
  obtain ⟨C0, hC0, hC0b⟩ := regularizedGMC_disk_moment_uniform_compact
    P X hX Xc hXc hS Prod.fst (fun _ => tst) (by fun_prop) continuousOn_const
    (fun c hc => by
      obtain ⟨hg, hg2, ht, ht4, _⟩ := hadmInf c hc
      exact ⟨hg, hg2, ht, ht4⟩)
    htst.le (fun _ _ => le_rfl) (by linarith : 1 ≤ 2 * R0 + 1)
  let K0 := ENNReal.ofReal (C0 * (2 * R0 + 1) ^ (4 * tst))
  have hdisk := fun c hc r hr => hC0b c hc (2 * R0 + 1) (by linarith) le_rfl r hr
  set Gm : ℝ≥0∞ := ((1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ κ) ^ (1 / max 1 tst)) ^ (max 1 tst))⁻¹
    with hGm
  refine ⟨ENNReal.ofReal (2 ^ (E * tst) * R0 ^ (4 * tst)) * K0 * Gm,
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
      (geometric_factor_lt_top hκpos), κ, hκpos, fun c hc ρ hρ hρR0 r hr => ?_⟩
  obtain ⟨hγ0, hγ2, -, -, -⟩ := hadmInf c hc
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
  have hβE : max (c.1 * c.2.2.2) 0 ≤ E := max_le ((le_abs_self _).trans (hEinf c hc)) hE
  have hξ : 2 * tst + c.1 ^ 2 * tst / 2 - c.1 ^ 2 * tst ^ 2 / 2 ≤ 4 * tst := by
    have hγsq : c.1 ^ 2 < 2 ^ 2 := pow_lt_pow_left₀ hγ2 hγ0.le two_ne_zero
    have h1 : c.1 ^ 2 * tst < 2 ^ 2 * tst := mul_lt_mul_of_pos_right hγsq htst
    have h2 : 0 ≤ c.1 ^ 2 * tst ^ 2 := by positivity
    linarith only [h1, h2]
  have hcoeff := farExterior_coeff_le (κ := κ) hρ hρ1 (by linarith : (1 : ℝ) ≤ R0)
    hβE htst hξ (by linarith [hκi c hc])
  have hG := geometric_factor_le hκpos (hκi c hc) (le_refl tst)
  calc ENNReal.ofReal ((2 * (1 / ρ)) ^ (max (c.1 * c.2.2.2) 0 * tst)) *
        (ENNReal.ofReal ((1 / ρ / R0) ^ (-(2 * tst + c.1 ^ 2 * tst / 2 -
          c.1 ^ 2 * tst ^ 2 / 2))) * K0) *
        ((1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ (2 * tst + c.1 ^ 2 * tst / 2 -
          c.1 ^ 2 * tst ^ 2 / 2 - max (c.1 * c.2.2.2) 0 * tst)) ^ (1 / max 1 tst)) ^
            (max 1 tst))⁻¹
      = ENNReal.ofReal ((2 * (1 / ρ)) ^ (max (c.1 * c.2.2.2) 0 * tst) *
          (1 / ρ / R0) ^ (-(2 * tst + c.1 ^ 2 * tst / 2 - c.1 ^ 2 * tst ^ 2 / 2))) * K0 *
        ((1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ (2 * tst + c.1 ^ 2 * tst / 2 -
          c.1 ^ 2 * tst ^ 2 / 2 - max (c.1 * c.2.2.2) 0 * tst)) ^ (1 / max 1 tst)) ^
            (max 1 tst))⁻¹ := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _), mul_assoc
          (ENNReal.ofReal _) (ENNReal.ofReal _) K0]
    _ ≤ ENNReal.ofReal (2 ^ (E * tst) * R0 ^ (4 * tst) * ρ ^ κ) * K0 * Gm := by
        gcongr
    _ = ENNReal.ofReal (2 ^ (E * tst) * R0 ^ (4 * tst)) * K0 * Gm * ENNReal.ofReal (ρ ^ κ) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        ring

/-- Cutoff moments of the bad part are uniformly small once the cutoff scale is below the disk
radius. -/
theorem cutoffUI_bad_cutoff_moment_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (partition : GMCChartPartition)
    (N : ℕ) (S : Set (ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ))) (hS : IsCompact S) {tst : ℝ}
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
  let _  := hX.1
  have hadmInf : ∀ c ∈ S, 0 < c.1 ∧ c.1 < 2 ∧ 0 < tst ∧ tst < 4 / c.1 ^ 2 ∧
      tst < 2 / c.1 * (Q c.1 - max c.2.2.2 0) := by
    intro c hc
    have h := (weightedCutoffSlack_pos_iff _).mp (hinf c hc)
    exact ⟨h.1, h.2.1, h.2.2.2.1, (lt_min_iff.mp h.2.2.2.2).1, (lt_min_iff.mp h.2.2.2.2).2⟩
  -- uniform sizes
  obtain ⟨Zs, E, hZs, hE, hZc, _, hEα, hEinf⟩ := compact_coulomb_parameter_bounds hS
  -- uniform decay rates
  have hζr := fun k => weightedCutoff_exponent_eventually hS
    (fun c => (c.1, c.2.2.1 k, tst)) (by fun_prop)
    (fun c hc => hroot c hc k)
  obtain ⟨κr, hκrb, hκr0⟩ := ((eventually_all.mpr hζr).and self_mem_nhdsWithin).exists
  -- partition supports and the exterior radius
  obtain ⟨Rf, Ri, hRf, hRi, hsuppf, hsuppi⟩ := partition_support_bounds partition
  set R0 : ℝ := max (2 * Zs + 2) Rf with hR0def
  have hR0Z : 2 * Zs + 2 ≤ R0 := le_max_left _ _
  have hR02 : 2 ≤ R0 := le_trans (by linarith) hR0Z
  obtain ⟨Ae, hAe, κe, hκe, hfarb⟩ := cutoffUI_far_exterior_moment_le
    P X hX Xc hXc N S hS htst hinf hE hEinf hR02
  let κ := min κr κe
  have hκpos : 0 < κ := lt_min hκr0 hκe
  have hκr : ∀ k, ∀ c ∈ S,
      κ ≤ c.1 * (Q c.1 - c.2.2.1 k) * tst - c.1 ^ 2 * tst ^ 2 / 2 :=
    fun k c hc => (min_le_left _ _).trans (hκrb k c hc)
  have hsuppf' : ∀ x, partition.finiteWeight x ≠ 0 → ‖x‖ < R0 := fun x hx =>
    lt_of_lt_of_le (hsuppf x hx) (le_max_right _ _)
  -- pointwise bounds for the weight
  obtain ⟨CR, hCR0, hCR⟩ := coulombCutoffWeight_le_root partition N hZs hE hρs hρs1 hRi hsuppi
  obtain ⟨CE, hCE0, hCE⟩ := coulombCutoffWeight_le_exterior partition N hZs hE hR0Z hsuppf'
  -- the uniform weighted cutoff bounds at the roots
  have hCk : ∀ k : Fin N, ∃ C : ℝ, 0 < C ∧ ∀ c ∈ S, ∀ δ R : ℝ, 0 < δ → δ ≤ R → R ≤ 1 →
      (∫⁻ ω, ENNReal.rpow (cutoffWeightedGmcBallMass P Xc c.1 (c.2.2.1 k) (c.2.1 k) R δ ω)
        tst ∂P) ≤ ENNReal.ofReal (C * Real.rpow R
          (c.1 * (Q c.1 - c.2.2.1 k) * tst - c.1 ^ 2 * tst ^ 2 / 2)) := by
    intro k
    have hcont : ContinuousOn (fun c : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) =>
        (c.1, c.2.2.1 k, tst)) S :=
      (continuous_fst.continuousOn).prodMk ((continuous_apply k |>.comp
        (continuous_fst.comp (continuous_snd.comp continuous_snd))).continuousOn.prodMk
          continuousOn_const)
    obtain ⟨C, hC, hCb⟩ := weightedCutoff_bound_uniform_compact P X hX Xc hXc _
      (hS.image_of_continuousOn hcont) (by
        rintro _ ⟨c, hc, rfl⟩
        exact hroot c hc k) (closedBall 0 Zs) (isCompact_closedBall _ _) 1 one_pos
    refine ⟨C, hC, fun c hc δ R hδ hδR hR1 => ?_⟩
    have hzk : c.2.1 k ∈ closedBall (0 : ℂ) Zs := by
      rw [mem_closedBall, dist_zero_right]
      exact (Finset.single_le_sum (f := fun j => ‖c.2.1 j‖) (fun j _ => norm_nonneg _)
        (Finset.mem_univ k)).trans (hZc c hc)
    exact hCb _ ⟨c, hc, rfl⟩ _ hzk δ R hδ hδR hR1
  choose Ck hCkpos hCkb using hCk
  -- the zero-charge disk bound
  set A : ℝ≥0∞ := 2 ^ tst * (2 ^ tst * ((N : ℝ≥0∞) ^ tst *
      ∑ k, ENNReal.ofReal CR ^ tst * ENNReal.ofReal (Ck k)) +
    ENNReal.ofReal CE ^ tst * (Ae))
    with hA
  have hfin : ∀ x : ℝ≥0∞, x ≠ ⊤ → x ^ tst < ⊤ := fun x hx =>
    ENNReal.rpow_lt_top_of_nonneg htst.le hx
  refine ⟨min ρs (1 / R0), lt_min hρs (by positivity), A, ?_, κ, hκpos, ?_⟩
  · refine ENNReal.mul_lt_top (hfin _ (by norm_num)) (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
    · refine ENNReal.mul_lt_top (hfin _ (by norm_num)) (ENNReal.mul_lt_top
        (hfin _ (ENNReal.natCast_ne_top N)) (ENNReal.sum_lt_top.mpr fun k _ =>
          ENNReal.mul_lt_top (hfin _ ENNReal.ofReal_ne_top) ENNReal.ofReal_lt_top))
    · exact ENNReal.mul_lt_top (hfin _ ENNReal.ofReal_ne_top) hAe
  intro c hc ρ hρ hρ1 r hr
  obtain ⟨hγ0, hγ2, -, -, -⟩ := hadmInf c hc
  have hρs' : ρ ≤ ρs := hρ1.trans (min_le_left _ _)
  have hρR0 : ρ ≤ 1 / R0 := hρ1.trans (min_le_right _ _)
  have hρ1' : ρ ≤ 1 := hρs'.trans hρs1
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
    rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  -- the pieces, pointwise in the sample
  set cw : Fin N → Ω → ℝ≥0∞ := fun k ω =>
    cutoffWeightedGmcBallMass P Xc c.1 (c.2.2.1 k) (c.2.1 k) ρ (Real.exp (-r)) ω with hcw
  set V : Ω → ℝ≥0∞ := fun ω => ∫⁻ x in {x : ℂ | 1 / ρ ≤ ‖x‖},
    ENNReal.ofReal (‖x‖ ^ max (c.1 * c.2.2.2) 0) ∂regularizedGMC P Xc c.1 r ω with hV
  have hGm  :=
    measurable_coulombCutoffWeight partition c.1 c.2.2.1 c.2.1 c.2.2.2 r
  have hpt : ∀ ω, (∫⁻ x in coulombBadRegion c.2.1 ρ,
      coulombCutoffWeight partition c.1 c.2.2.1 c.2.1 c.2.2.2 r x ∂regularizedGMC P Xc c.1 r ω) ≤
        ∑ k, ENNReal.ofReal CR * cw k ω + 0 * 0 + ENNReal.ofReal CE * V ω := by
    intro ω
    set μ : Measure ℂ := regularizedGMC P Xc c.1 r ω with hμ
    have hne0 : ∀ᵐ x ∂μ, x ≠ 0 := by
      rw [ae_iff]
      simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
      exact regularizedGMC_singleton_eq_zero P Xc c.1 r ω 0
    refine (lintegral_coulombBadRegion_le μ _ hGm c.2.1 ρ).trans ?_
    rw [mul_zero, add_zero]
    refine add_le_add (Finset.sum_le_sum fun k _ => ?_) ?_
    · rw [hcw]
      simp only []
      have hw : Measurable fun x : ℂ =>
          ENNReal.ofReal ((‖x - c.2.1 k‖ + Real.exp (-r)) ^ (-c.1 * c.2.2.1 k)) :=
        ENNReal.measurable_ofReal.comp (((measurable_id.sub_const _).norm.add_const _).pow_const _)
      rw [cutoffWeightedGmcBallMass, hlog, ← lintegral_const_mul _ hw]
      refine setLIntegral_mono_ae' Metric.isOpen_ball.measurableSet ?_
      filter_upwards [hne0] with x hx0 hx
      exact hCR c.1 c.2.2.1 c.2.1 c.2.2.2 r k x hr0 (hZc c hc) (hEα c hc) (hEinf c hc)
        (fun j hj => hsep c hc j k hj) (Metric.ball_subset_ball hρs' hx) hx0
    · rw [hV]
      simp only []
      have hpow : Measurable fun x : ℂ => ENNReal.ofReal (‖x‖ ^ max (c.1 * c.2.2.2) 0) :=
        ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)
      rw [← lintegral_const_mul _ hpow]
      calc ∫⁻ x in {x : ℂ | 1 / ρ < ‖x‖},
            coulombCutoffWeight partition c.1 c.2.2.1 c.2.1 c.2.2.2 r x ∂μ
          ≤ ∫⁻ x in {x : ℂ | 1 / ρ < ‖x‖}, ENNReal.ofReal CE *
              ENNReal.ofReal (‖x‖ ^ max (c.1 * c.2.2.2) 0) ∂μ := by
            refine setLIntegral_mono' (measurableSet_lt measurable_const measurable_norm)
              fun x hx => ?_
            exact hCE c.1 c.2.2.1 c.2.1 c.2.2.2 r x hr0 (hZc c hc) (hEα c hc) (hEinf c hc)
              (hinvρ.trans hx.le)
        _ ≤ ∫⁻ x in {x : ℂ | 1 / ρ ≤ ‖x‖}, ENNReal.ofReal CE *
              ENNReal.ofReal (‖x‖ ^ max (c.1 * c.2.2.2) 0) ∂μ :=
            lintegral_mono_set fun x hx =>
              (le_of_lt (show 1 / ρ < ‖x‖ from hx) : 1 / ρ ≤ ‖x‖)
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
  have hmom := lintegral_rpow_le_of_le_pieces _ cw (fun _ => 0) V (fun _ => ENNReal.ofReal CR) 0
    (ENNReal.ofReal CE) hcwm aemeasurable_const hVm (Eventually.of_forall hpt) htst
  refine hmom.trans ?_
  -- bound the moments of the pieces
  have hcwb : ∀ k, ∫⁻ ω, cw k ω ^ tst ∂P ≤ ENNReal.ofReal (Ck k) * ENNReal.ofReal (ρ ^ κ) := by
    intro k
    refine (hCkb k c hc (Real.exp (-r)) ρ (Real.exp_pos _) hδρ hρ1').trans ?_
    rw [← ENNReal.ofReal_mul (hCkpos k).le]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (hCkpos k).le)
    exact Real.rpow_le_rpow_of_exponent_ge hρ hρ1' (hκr k c hc)
  have hVb : ∫⁻ ω, V ω ^ tst ∂P ≤ Ae * ENNReal.ofReal (ρ ^ κ) := by
    refine (hfarb c hc ρ hρ hρR0 r hr0).trans ?_
    exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hρ hρ1' (min_le_right _ _)))
  simp only [ENNReal.zero_rpow_of_pos htst, zero_mul, add_zero]
  rw [hA]
  calc 2 ^ tst * (2 ^ tst * ((N : ℝ≥0∞) ^ tst *
        ∑ k, ENNReal.ofReal CR ^ tst * ∫⁻ ω, cw k ω ^ tst ∂P) +
        ENNReal.ofReal CE ^ tst * ∫⁻ ω, V ω ^ tst ∂P)
      ≤ 2 ^ tst * (2 ^ tst * ((N : ℝ≥0∞) ^ tst *
        ∑ k, ENNReal.ofReal CR ^ tst * (ENNReal.ofReal (Ck k) * ENNReal.ofReal (ρ ^ κ))) +
        ENNReal.ofReal CE ^ tst * (Ae *
          ENNReal.ofReal (ρ ^ κ))) := by
        gcongr with k hk
        exact hcwb k
    _ = _ := by
        rw [show ∑ k, ENNReal.ofReal CR ^ tst * (ENNReal.ofReal (Ck k) * ENNReal.ofReal (ρ ^ κ)) =
            (∑ k, ENNReal.ofReal CR ^ tst * ENNReal.ofReal (Ck k)) * ENNReal.ofReal (ρ ^ κ) by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by ring]
        ring

end DOZZ.Proofs
