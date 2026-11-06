module

public import HypoellipticAleksandrov.Measure.TimeVelocity
public import HypoellipticAleksandrov.Parabolic.Derivatives
public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientBound
public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientTest
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.WeakDerivativesCompactGlobalization
public import HypoellipticAleksandrov.Measure.TimeVelocity


open private HypoellipticAleksandrov.Parabolic.value_eq_zero_of_not_mem_tsupport from HypoellipticAleksandrov.Parabolic.WeakDerivativesCompactGlobalization


/-!
# Difference-quotient pairing limits

This module localizes a smooth compactly supported test function to a compact
spatial-shift collar and applies dominated convergence to its signed backward
difference quotients.
-/

 public section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped Topology

variable {d : ℕ}

section
variable (φ : HypoellipticAleksandrov.Parabolic.ScalarField d) (hφ : ContDiff ℝ 1 φ) (k : Fin d) (z : TimeVelocity d)

include hφ
private theorem hasDerivAt_backwardSpatialShift
      :
    HasDerivAt (fun h  => φ (spatialShift k (-h) z))
      (-velocityGradient φ z k) 0 := by

  have hφ' : HasFDerivAt φ (fderiv ℝ φ z) (spatialShift k (-0) z) := by
    simpa using (hφ.differentiable
      (by norm_num) z).hasFDerivAt

  simpa only [velocityGradient, Function.comp_def, PDE.basisVec, map_neg] using (hφ'.comp_hasDerivAt 0 (show HasDerivAt (fun h  => spatialShift k (-h) z)
      (-(0, PDE.basisVec k)) 0 by
      convert ((hasDerivAt_id' (𝕜 := ℝ) 0).smul_const
        (-(0, PDE.basisVec k))).const_add z using 1 <;>
        ext <;> simp [spatialShift]))

private theorem tendsto_backwardSpatialDifferenceQuotient
      :
    Tendsto (fun h  => (φ (spatialShift k (-h) z) - φ z) / h)
      (𝓝[≠] 0) (𝓝 (-velocityGradient φ z k)) := by

  simpa only [zero_add, smul_eq_mul, div_eq_mul_inv, mul_comm,
    neg_zero, spatialShift_zero, id_eq] using ((hasDerivAt_backwardSpatialShift φ hφ k z).tendsto_slope_zero)
end


private theorem tsupport_backwardSpatialDifferenceQuotient_subset_cthickening
     {φ : HypoellipticAleksandrov.Parabolic.ScalarField d} (k : Fin d) (h r : ℝ)
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
  rcases tsupport_spatialDifferenceQuotient_subset k (-h) φ hz with hz | hz
  · rw [tsupport_spatialTranslate] at hz
    apply Metric.mem_cthickening_of_dist_le z _ r (tsupport φ) hz
    have hcancel : spatialShift k h (spatialShift k (-h) z) = z := by
      calc
        spatialShift k h (spatialShift k (-h) z) =
            (spatialShift k h ∘ spatialShift k (-h)) z := rfl
        _ = spatialShift k (-h + h) z := by rw [spatialShift_comp]
        _ = z := by simp
    calc
      dist z (spatialShift k (-h) z) =
          dist (spatialShift k h (spatialShift k (-h) z)) (spatialShift k (-h) z) := by
        rw [hcancel]
      _ = |h| := dist_spatialShift k h _
      _ ≤ r := hh
  · exact Metric.mem_cthickening_of_dist_le z z r (tsupport φ) hz (by simp [hr])




/-- Pairing against a compactly supported `C¹` test has the signed backward
spatial difference-quotient limit on every open time--velocity set. -/
theorem tendsto_setIntegral_mul_backwardSpatialDifferenceQuotient
    {d : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d}
    (hU : IsOpen U) (u φ : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hu : LocallyIntegrableOn u U
      )
    (hφ : ContDiff ℝ 1 φ) (hφcompact : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (k : Fin d) :
    Tendsto
      (fun h  =>
        ∫ z in U, u z *
          ((φ (spatialShift k (-h) z) - φ z) / h)
          ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))
      (𝓝[≠] 0)
      (𝓝 (-∫ z in U, u z * velocityGradient φ z k
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))) := by
  let sharedTerm_70d83bb77d := ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))
  let S  := tsupport φ
  obtain ⟨δ, hδ, hδU, -⟩ :=
    IsCompact.exists_spatialShift_cthickening_collar hφcompact.isCompact hU hφU
  let K  := Metric.cthickening (δ / 2) S
  have hKcompact : IsCompact K := by
    exact hφcompact.isCompact.cthickening
  have hKmeas  := hKcompact.measurableSet
  have hKU : K ⊆ U := by
    exact (Metric.cthickening_mono (by linarith) S).trans hδU
  obtain ⟨ε, C, hε, hC, -, -, -, hbound⟩ :=
    IsCompact.exists_spatialDifferenceQuotient_bound_of_contDiffOn_one hKcompact hU hKU
      hφ.contDiffOn
  have hIntK : IntegrableOn u K sharedTerm_70d83bb77d :=
    hu.integrableOn_compact_subset hKU hKcompact
  have hsmall : ∀ᶠ h : ℝ in 𝓝[≠] 0, |h| ≤ δ / 2 ∧ |h| ≤ ε := by


    filter_upwards [(show ∀ᶠ h : ℝ in 𝓝 0, |h| < min (δ / 2) ε by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (show 0 < min (δ / 2) ε from lt_min (by linarith) hε)] with h hh
        simpa [Real.dist_eq] using hh).filter_mono nhdsWithin_le_nhds] with h hh
    exact ⟨le_trans (le_of_lt hh) (min_le_left _ _),
      le_trans (le_of_lt hh) (min_le_right _ _)⟩
  let q  := fun h z =>
    (φ (spatialShift k (-h) z) - φ z) / h


  have hDCT : Tendsto
      (fun h  => ∫ z, u z * q h z ∂(volume.restrict K))
      (𝓝[≠] 0)
      (𝓝 (∫ z, u z * (-velocityGradient φ z k) ∂(volume.restrict K))) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun z => C * |u z|)
    · filter_upwards with h

      exact hIntK.aestronglyMeasurable.mul
        (Continuous.aestronglyMeasurable (show Continuous (q h) by
            change Continuous (fun z => (φ (spatialShift k (-h) z) - φ z) / h)
            convert (ContDiff.spatialDifferenceQuotient hφ (k := k) (h := -h)).continuous.neg
              using 1
            ext z
            simp only [spatialDifferenceQuotient_apply, spatialTranslate_apply,
              Pi.neg_apply]
            ring))
    · filter_upwards [(show ∀ᶠ h : ℝ in 𝓝[≠] 0,
      ∀ z ∈ K, |q h z| ≤ C by
        filter_upwards [hsmall] with h hh z hz
        have hq : q h z = -spatialDifferenceQuotient k (-h) φ z := by
          simp only [q, spatialDifferenceQuotient_apply, spatialTranslate_apply]
          ring
        rw [hq, abs_neg]
        exact hbound k (-h) z (by simpa only [abs_neg] using hh.2) hz)] with h hh
      filter_upwards [ae_restrict_mem hKmeas] with z hz
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul_of_nonneg_left (hh z hz) (abs_nonneg _)).trans_eq (by ring)
    · exact (hIntK.abs.const_mul C)
    · filter_upwards with z
      exact tendsto_const_nhds.mul
        (tendsto_backwardSpatialDifferenceQuotient φ hφ k z)
  have hsource :
      (fun h  => ∫ z, u z * q h z ∂(volume.restrict K)) =ᶠ[𝓝[≠] 0]
        fun h  => ∫ z in U, u z * q h z ∂sharedTerm_70d83bb77d := by
    filter_upwards [(show ∀ᶠ h : ℝ in 𝓝[≠] 0, tsupport (q h) ⊆ K by
        filter_upwards [hsmall] with h hh
        exact tsupport_backwardSpatialDifferenceQuotient_subset_cthickening k h (δ / 2)
          (by linarith) hh.1)] with h hsupp
    symm
    exact setIntegral_eq_of_subset_of_forall_diff_eq_zero hU.measurableSet hKU (fun z hz => by
      have hqzero : q h z = 0 := by
        apply _root_.HypoellipticAleksandrov.Parabolic.value_eq_zero_of_not_mem_tsupport
        intro hzts
        exact hz.2 (hsupp hzts)
      simp only [hqzero, mul_zero])
  have hvelocity_zero {z : TimeVelocity d} (hz : z ∉ K) : velocityGradient φ z k = 0 := by
    have hzS : z ∉ S := by
      intro hzS
      apply hz
      exact Metric.mem_cthickening_of_dist_le z z (δ / 2) S hzS
        (by simpa using (show 0 ≤ δ / 2 by linarith))
    have hzderiv  := fun hzderiv =>
      hzS ((tsupport_fderiv_subset ℝ) hzderiv)
    have hzero  := _root_.HypoellipticAleksandrov.Parabolic.value_eq_zero_of_not_mem_tsupport hzderiv
    change fderiv ℝ φ z (0, Pi.single k 1) = 0
    rw [hzero]
    rfl
  have hlimit :
      (∫ z, u z * (-velocityGradient φ z k) ∂(volume.restrict K)) =
        -∫ z in U, u z * velocityGradient φ z k ∂sharedTerm_70d83bb77d := by
    calc
      (∫ z, u z * (-velocityGradient φ z k) ∂(volume.restrict K)) =
          ∫ z in K, u z * (-velocityGradient φ z k) ∂sharedTerm_70d83bb77d := rfl
      _ = ∫ z in U, u z * (-velocityGradient φ z k) ∂sharedTerm_70d83bb77d := by
        symm
        exact setIntegral_eq_of_subset_of_forall_diff_eq_zero hU.measurableSet hKU (fun z hz => by
          rw [hvelocity_zero hz.2]
          simp)
      _ = -∫ z in U, u z * velocityGradient φ z k ∂sharedTerm_70d83bb77d := by
        rw [← integral_neg]
        congr with z
        ring
  rw [hlimit] at hDCT
  exact hDCT.congr' hsource

end HypoellipticAleksandrov.Parabolic
