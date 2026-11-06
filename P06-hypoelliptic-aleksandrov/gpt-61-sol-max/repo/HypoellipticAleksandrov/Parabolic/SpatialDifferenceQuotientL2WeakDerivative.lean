module

public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientL2Transpose
public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientPairingLimit
public import HypoellipticAleksandrov.Parabolic.Dirichlet.HilbertWeakSequentialCompactnessCLM
public import HypoellipticAleksandrov.Topology.WeakLimitNorm
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import HypoellipticAleksandrov.Measure.TimeVelocity


/-!
# Uniform spatial difference quotients and weak velocity derivatives

This module turns a positive-step uniform interior `L²` difference-quotient
bound into a restricted-`L²` weak velocity derivative.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal Topology

/-- A positive-step family of spatial difference quotients uniformly bounded by
`C` has an `L²` weak velocity-partial limit whose norm is at most `C`. -/
theorem exists_hasWeakVelocityPartialDerivOn_norm_le_of_uniform_spatialDifferenceQuotient
    {d : ℕ} (U : HypoellipticAleksandrov.Parabolic.Region d) (hU : IsOpen U)
    (k : Fin d) (u : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hu : ParabolicMemLpOn U (2 ) u)
    (δ C : ℝ) (hδ : 0 < δ)
    (hDQmem : ∀ h : ℝ, 0 < h → h < δ →
      ParabolicMemLpOn U (2 )
        (spatialDifferenceQuotient k h u))
    (hDQbound : ∀ (h : ℝ) (hh0 : 0 < h) (hhδ : h < δ),
      ‖(hDQmem h hh0 hhδ).toLp
        (spatialDifferenceQuotient k h u)‖ ≤ C) :
    ∃ g : HypoellipticAleksandrov.Parabolic.ScalarField d,
      ∃ hg : ParabolicMemLpOn U (2 ) g,
        HasWeakVelocityPartialDerivOn U k u g ∧
          ‖hg.toLp g‖ ≤ C := by
  let sharedTerm_832a3d7aa2 := ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))
  let μ  := timeVelocityVolumeOn U
  letI : IsLocallyFiniteMeasure μ :=
    Measure.isLocallyFiniteMeasure_of_le Measure.restrict_le_self
  have huLoc : LocallyIntegrableOn u U sharedTerm_832a3d7aa2 := locallyIntegrableOn_of_locallyIntegrable_restrict
      (hu.locallyIntegrable (by norm_num))
  let a  := fun n => δ / ((n + 2 : ℕ) : ℝ)
  have ha_pos : ∀ n, 0 < a n := by
    intro n
    dsimp [a]
    positivity
  have ha_lt : ∀ n, a n < δ := by
    intro n
    dsimp [a]

    have hden : 1 < ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    rw [div_lt_iff₀ (by positivity : 0 < ((n + 2 : ℕ) : ℝ))]
    nlinarith

  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  letI : IsSeparable μ := inferInstance
  let H := Lp ℝ (2 ) μ
  let q  := fun n =>
    (hDQmem (a n) (ha_pos n) (ha_lt n)).toLp
      (spatialDifferenceQuotient k (a n) u)
  have hq_bound : ∀ n, ‖q n‖ ≤ C := by
    intro n
    exact hDQbound (a n) (ha_pos n) (ha_lt n)
  obtain ⟨v, σ, hσ, hweak⟩ :=
    Dirichlet.exists_strictMono_tendsto_clm_of_norm_le q C hq_bound
  have hv_norm  :=
    HypoellipticAleksandrov.norm_le_of_tendsto_clm_of_norm_le
      (fun n => q (σ n)) v C (fun n => hq_bound (σ n)) hweak
  have haσ_tendsto  :=
    (show Tendsto a atTop (𝓝[≠] 0) by
        apply (tendsto_nhdsWithin_iff).2
        constructor
        · simpa only [Function.comp_def, a] using (tendsto_const_div_atTop_nhds_zero_nat δ).comp
            (tendsto_add_atTop_nat 2)
        · filter_upwards with n
          exact (ne_of_gt (ha_pos n))).comp hσ.tendsto_atTop
  let hg  := Lp.memLp v
  refine ⟨fun z => v z, hg, ?_, ?_⟩
  intro φ hφ hφcompact hφU
  let φLp : H := (hφ.continuous.memLp_of_hasCompactSupport hφcompact).toLp φ
  let ell : H →L[ℝ] ℝ := InnerProductSpace.toDual ℝ H φLp
  have hq_ae : ∀ n, (q n : HypoellipticAleksandrov.Parabolic.ScalarField d) =ᵐ[μ]
      spatialDifferenceQuotient k (a n) u := by
    intro n
    exact (hDQmem (a n) (ha_pos n) (ha_lt n)).coeFn_toLp
  have hφ_ae : (φLp : HypoellipticAleksandrov.Parabolic.ScalarField d) =ᵐ[μ] φ := by
    exact (hφ.continuous.memLp_of_hasCompactSupport hφcompact).coeFn_toLp
  have hellq : ∀ n, ell (q (σ n)) =
      ∫ z in U, spatialDifferenceQuotient k (a (σ n)) u z * φ z
        ∂sharedTerm_832a3d7aa2 := by
    intro n
    change inner ℝ φLp (q (σ n)) = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hq_ae (σ n), hφ_ae] with z hzq hzφ
    rw [hzq, hzφ]
    rfl
  have hellv : ell v = ∫ z in U, v z * φ z ∂sharedTerm_832a3d7aa2 := by
    change inner ℝ φLp v = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hφ_ae] with z hzφ
    rw [hzφ]
    rfl
  have hpair : Tendsto
      (fun n => ∫ z in U, spatialDifferenceQuotient k (a (σ n)) u z * φ z
        ∂sharedTerm_832a3d7aa2) atTop
      (𝓝 (∫ z in U, v z * φ z ∂sharedTerm_832a3d7aa2)) := by
    rw [← hellv]
    exact (hweak ell).congr' (Filter.Eventually.of_forall hellq)
  obtain ⟨ε, hε, -, hshift⟩ :=
    IsCompact.exists_spatialShift_cthickening_collar hφcompact.isCompact hU hφU
  have haσ_nhds  :=
    (tendsto_nhdsWithin_iff.mp haσ_tendsto).1
  have hevent_shift : ∀ᶠ n in atTop,
      Set.MapsTo (spatialShift k (a (σ n))) (tsupport φ) U := by
    filter_upwards [haσ_nhds.eventually (Metric.ball_mem_nhds 0 hε)] with n hn
    apply hshift k (a (σ n))
    simpa only [Function.comp_def, Real.dist_eq, sub_zero] using le_of_lt hn
  have htranspose :
      (fun n => ∫ z in U, spatialDifferenceQuotient k (a (σ n)) u z * φ z
        ∂sharedTerm_832a3d7aa2) =ᶠ[atTop]
      fun n => -∫ z in U,
        u z * spatialDifferenceQuotient k (-(a (σ n))) φ z
          ∂sharedTerm_832a3d7aa2 := by
    filter_upwards [hevent_shift] with n hn
    exact setIntegral_spatialDifferenceQuotient_mul_eq_neg_mul_spatialDifferenceQuotient_neg
      U k (a (σ n)) u φ hu hφ.continuous hφcompact hφU hn
  have hback := tendsto_setIntegral_mul_backwardSpatialDifferenceQuotient
    hU u φ huLoc (hφ.of_le (by norm_num)) hφcompact hφU k
  have hbackσ := hback.comp haσ_tendsto
  have hback_eq : (fun n => -∫ z in U,
      u z * spatialDifferenceQuotient k (-(a (σ n))) φ z
        ∂sharedTerm_832a3d7aa2) =ᶠ[atTop]
      fun n => ∫ z in U, u z *
        ((φ (spatialShift k (-(a (σ n))) z) - φ z) / (a (σ n)))
          ∂sharedTerm_832a3d7aa2 := by
    filter_upwards with n
    rw [← integral_neg]
    congr with z
    simp only [spatialDifferenceQuotient_apply, spatialTranslate_apply]
    ring
  have hback_limit : Tendsto (fun n => -∫ z in U,
      u z * spatialDifferenceQuotient k (-(a (σ n))) φ z
        ∂sharedTerm_832a3d7aa2) atTop
      (𝓝 (-∫ z in U, u z * velocityGradient φ z k
        ∂sharedTerm_832a3d7aa2)) := hbackσ.congr' hback_eq.symm
  have hlimit := tendsto_nhds_unique hpair (hback_limit.congr' htranspose.symm)
  linarith
  · simpa only [hg, Lp.toLp_coeFn] using hv_norm

end HypoellipticAleksandrov.Parabolic
