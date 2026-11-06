module

public import HypoellipticAleksandrov.Measure.TimeVelocity
public import HypoellipticAleksandrov.Parabolic.Derivatives
public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientBound
public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientTest
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Difference-quotient pairing limits

This module localizes a smooth compactly supported test function to a compact
spatial-shift collar and applies dominated convergence to its signed backward
difference quotients.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped Topology

variable {d : ℕ} (φ : TimeVelocity d → ℝ)

private theorem hasDerivAt_backwardSpatialShift
     (hφ : ContDiff ℝ 1 φ)
    (k : Fin d) (z : TimeVelocity d) :
    HasDerivAt (fun h : ℝ => φ (spatialShift k (-h) z))
      (-velocityGradient φ z k) 0 := by
  have hline : HasDerivAt (fun h : ℝ => spatialShift k (-h) z)
      (-(0, PDE.basisVec k)) 0 := by
    convert ((hasDerivAt_id' (𝕜 := ℝ) 0).smul_const
      (-(0, PDE.basisVec k))).const_add z using 1 <;>
      ext <;> simp [spatialShift]
  have hφ' : HasFDerivAt φ (fderiv ℝ φ z) (spatialShift k (-0) z) := by
    simpa using (hφ.differentiable
      (by norm_num) z).hasFDerivAt
  have hcomp := hφ'.comp_hasDerivAt 0 hline
  simpa only [Function.comp_def, velocityGradient, map_neg, map_prod, map_zero, PDE.basisVec]
    using hcomp

private theorem tendsto_backwardSpatialDifferenceQuotient
     (hφ : ContDiff ℝ 1 φ)
    (k : Fin d) (z : TimeVelocity d) :
    Tendsto (fun h : ℝ => (φ (spatialShift k (-h) z) - φ z) / h)
      (𝓝[≠] 0) (𝓝 (-velocityGradient φ z k)) := by
  have h := (hasDerivAt_backwardSpatialShift φ hφ k z).tendsto_slope_zero
  simpa only [zero_add, smul_eq_mul, div_eq_mul_inv, mul_comm,
    neg_zero, spatialShift_zero, id_eq] using h

private theorem tsupport_backwardSpatialDifferenceQuotient_subset_cthickening
     {φ : TimeVelocity d → ℝ} (k : Fin d) (h r : ℝ)
    (hr : 0 ≤ r) (hh : |h| ≤ r) :
    tsupport (fun z => (φ (spatialShift k (-h) z) - φ z) / h) ⊆
      Metric.cthickening r (tsupport φ) := by
  have hq : (fun z => (φ (spatialShift k (-h) z) - φ z) / h) =
      -spatialDifferenceQuotient k (-h) φ := by
    funext z
    simp only [spatialDifferenceQuotient_apply, spatialTranslate_apply, Pi.neg_apply]
    ring
  rw [hq, tsupport_neg]
  intro z hz
  rcases tsupport_spatialDifferenceQuotient_subset k _ φ hz with hz | hz
  · rw [tsupport_spatialTranslate] at hz
    apply Metric.mem_cthickening_of_dist_le z (spatialShift k (-h) z) r (tsupport φ) hz
    have hcancel : spatialShift k h (spatialShift k (-h) z) = z := by
      calc
        spatialShift k h _ =
            (spatialShift k h ∘ spatialShift k _) z := rfl
        _ = spatialShift k _ z := by rw [spatialShift_comp]
        _ = z := by simp
    calc
      dist z _ =
          dist _ _ := by
        rw [hcancel]
      _ = |h| := dist_spatialShift k h _
      _ ≤ r := hh
  · exact Metric.mem_cthickening_of_dist_le z z r _ hz (by simp [hr])

private theorem eq_zero_of_not_mem_tsupport
    {X E : Type*} [TopologicalSpace X] [Zero E] {f : X → E} {x : X}
    (hx : x ∉ tsupport f) : f x = 0 := by
  by_contra hzero
  apply hx
  exact subset_closure (Function.mem_support.mpr hzero)

/-- Pairing against a compactly supported `C¹` test has the signed backward
spatial difference-quotient limit on every open time--velocity set. -/
theorem tendsto_setIntegral_mul_backwardSpatialDifferenceQuotient
     {U : Set (TimeVelocity d)}
    (hU : IsOpen U) (u φ : TimeVelocity d → ℝ)
    (hu : LocallyIntegrableOn u U
      (volume : Measure (TimeVelocity d)))
    (hφ : ContDiff ℝ 1 φ) (hφcompact : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (k : Fin d) :
    Tendsto
      (fun h : ℝ =>
        ∫ z in U, u z *
          ((φ (spatialShift k (-h) z) - φ z) / h)
          ∂(volume : Measure (TimeVelocity d)))
      (𝓝[≠] 0)
      (𝓝 (-∫ z in U, u z * velocityGradient φ z k
        ∂(volume : Measure (TimeVelocity d)))) := by
  let S  := tsupport φ
  obtain ⟨δ, hδ, hδU, -⟩ :=
    IsCompact.exists_spatialShift_cthickening_collar hφcompact.isCompact hU hφU
  let K  := Metric.cthickening (δ / 2) S
  have hKcompact : IsCompact K := hφcompact.isCompact.cthickening
  have hKmeas  := hKcompact.measurableSet
  have hKU : K ⊆ U := (Metric.cthickening_mono (by linarith) S).trans hδU
  obtain ⟨ε, C, hε, hC, -, -, -, hbound⟩ :=
    IsCompact.exists_spatialDifferenceQuotient_bound_of_contDiffOn_one hKcompact hU hKU
      hφ.contDiffOn
  have hIntK  :=
    hu.integrableOn_compact_subset hKU hKcompact
  have hsmall : ∀ᶠ h : ℝ in 𝓝[≠] 0, |h| ≤ δ / 2 ∧ |h| ≤ ε := by
    have hpos : 0 < min (δ / 2) ε := lt_min (by linarith) hε
    have hnhds : ∀ᶠ h : ℝ in 𝓝 0, |h| < min (δ / 2) ε := by
      filter_upwards [Metric.ball_mem_nhds _ hpos] with h hh
      simp_all
    filter_upwards [hnhds.filter_mono nhdsWithin_le_nhds] with h hh
    grind
  let q  := fun h z =>
    (φ (spatialShift k (-h) z) - φ z) / h
  have hq_support : ∀ᶠ h : ℝ in 𝓝[≠] 0, tsupport (q h) ⊆ K := by
    filter_upwards [hsmall] with h hh
    exact tsupport_backwardSpatialDifferenceQuotient_subset_cthickening k h _
      (by linarith) hh.1
  have hq_bound : ∀ᶠ h : ℝ in 𝓝[≠] 0,
      ∀ z ∈ K, |q h z| ≤ C := by
    filter_upwards [hsmall] with h hh z hz
    have hq : q h z = -spatialDifferenceQuotient k (-h) φ z := by
      simp only [spatialDifferenceQuotient_apply, spatialTranslate_apply]
      ring
    grind
  have hDCT : Tendsto
      (fun h : ℝ => ∫ z, u z * q h z ∂(volume.restrict K))
      (𝓝[≠] 0)
      (𝓝 (∫ z, u z * (-velocityGradient φ z k) ∂(volume.restrict K))) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun z => C * |u z|)
    · filter_upwards with h
      have hqcont : Continuous (q h) := by
        convert (ContDiff.spatialDifferenceQuotient hφ (k := k) (h := -h)).continuous.neg
          using 1
        ext z
        simp only [spatialDifferenceQuotient_apply, spatialTranslate_apply,
          Pi.neg_apply]
        ring
      exact hIntK.aestronglyMeasurable.mul
        (Continuous.aestronglyMeasurable hqcont)
    · filter_upwards [hq_bound] with h hh
      filter_upwards [ae_restrict_mem hKmeas] with z hz
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul_of_nonneg_left (hh z hz) (abs_nonneg _)).trans_eq (by ring)
    · exact (hIntK.abs.const_mul C)
    · filter_upwards with z
      exact tendsto_const_nhds.mul
        (tendsto_backwardSpatialDifferenceQuotient φ hφ k z)
  have hsource :
      (fun h : ℝ => ∫ z, u z * q h z ∂(volume.restrict K)) =ᶠ[𝓝[≠] 0]
        fun h : ℝ => ∫ z in U, u z * q h z ∂volume := by
    filter_upwards [hq_support] with h hsupp
    symm
    exact setIntegral_eq_of_subset_of_forall_diff_eq_zero hU.measurableSet hKU (fun z hz => by
      have hqzero : q h z = 0 := by
        apply eq_zero_of_not_mem_tsupport
        grind
      simp_all)
  have hvelocity_zero {z : TimeVelocity d} (hz : z ∉ K) : velocityGradient φ z k = 0 := by
    have hzS : z ∉ S := by
      intro hzS
      apply hz
      exact Metric.mem_cthickening_of_dist_le z z _ S hzS
        (by simpa using (show 0 ≤ δ / 2 by linarith))
    have hzderiv : z ∉ tsupport _ := fun hzderiv =>
      hzS ((tsupport_fderiv_subset ℝ) hzderiv)
    have hzero  := eq_zero_of_not_mem_tsupport hzderiv
    change fderiv ℝ φ z _ = 0
    simp_all
  have hlimit :
      (∫ z, u z * (-velocityGradient φ z k) ∂(volume.restrict K)) =
        -∫ z in U, u z * velocityGradient φ z k ∂volume := by
    calc
      (∫ z, u z * (-velocityGradient φ z k) ∂(volume.restrict K)) =
          ∫ z in K, u z * (-velocityGradient φ z k) ∂volume := rfl
      _ = ∫ z in U, u z * (-velocityGradient φ z k) ∂volume := by
        symm
        exact setIntegral_eq_of_subset_of_forall_diff_eq_zero hU.measurableSet hKU (fun z hz => by
          simp_all)
      _ = -∫ z in U, u z * velocityGradient φ z k ∂volume := by
        rw [← integral_neg]
        ring
  rw [hlimit] at hDCT
  exact hDCT.congr' hsource

end HypoellipticAleksandrov.Parabolic
