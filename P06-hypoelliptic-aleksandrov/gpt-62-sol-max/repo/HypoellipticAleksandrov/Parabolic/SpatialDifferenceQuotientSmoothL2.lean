module

public import PDEFoundation.Sobolev.Inequalities.SmoothSegment
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Measure

/-!
# Global `L²` control of smooth spatial difference quotients

This file proves the constant-one whole-space estimate needed before local
cutoffs are introduced.
-/

@[expose] public section

open MeasureTheory

section
variable {d : ℕ} (φ : PDE.Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
include hφ

private theorem integrable_sq_classicalGradient
    (hφcompact : HasCompactSupport φ) :
    Integrable (fun y => PDE.vecEuclideanNorm (PDE.classicalGradient φ y) ^ 2)
      (volume : Measure (PDE.Vec d)) := by
  have hcomponent : ∀ i : Fin d,
      Integrable (fun y => ((fderiv ℝ φ y) (PDE.basisVec i)) ^ 2)
      (volume : Measure (PDE.Vec d)) := by
    intro i
    have hc : Continuous (fun y => ((fderiv ℝ φ y) (PDE.basisVec i)) ^ 2) :=
      ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2
    have hs : HasCompactSupport (fun y => ((fderiv ℝ φ y) (PDE.basisVec i)) ^ 2) :=
      (hφcompact.fderiv_apply ℝ (PDE.basisVec i)).comp_left
        (g := fun x : ℝ => x ^ 2) (by norm_num)
    exact hc.integrable_of_hasCompactSupport hs
  simp_rw [PDE.vecEuclideanNorm_sq, PDE.vecNormSq_eq_sum_sq,
    PDE.classicalGradient_apply]
  exact integrable_finsetSum _ fun i _ => hcomponent i

private theorem spatialDifferenceQuotient_sq_le_segmentIntegral
    (k : Fin d) (h : ℝ) (hh : h ≠ 0) (y : PDE.Vec d) :
    ((φ (y + h • PDE.basisVec k) - φ y) / h) ^ 2 ≤
      ∫ t in (0 : ℝ)..1,
        PDE.vecEuclideanNorm (PDE.classicalGradient φ (y + t • (h • PDE.basisVec k))) ^ 2 := by
  have hn : PDE.vecEuclideanNorm (h • PDE.basisVec k) = |h| := by
    simp [PDE.vecEuclideanNorm_smul, PDE.vecEuclideanNorm_basisVec]
  have H := PDE.abs_sub_rpow_le_integral_euclideanGradient_mul_distance_rpow
    (p := (2 : ℝ)) (by norm_num) hφ (y + h • PDE.basisVec k) y
  rw [div_pow, div_le_iff₀ (sq_pos_of_ne_zero hh)]
  simpa only [PDE.segmentBlend_eq_add_smul_sub, add_sub_cancel_left, hn,
    Real.rpow_two, sq_abs, mul_pow, intervalIntegral.integral_mul_const] using H

private theorem integrable_sq_spatialDifferenceQuotient
    (hφcompact : HasCompactSupport φ)
    (k : Fin d) (h : ℝ) :
    Integrable (fun y => ((φ (y + h • PDE.basisVec k) - φ y) / h) ^ 2)
      (volume : Measure (PDE.Vec d)) := by
  let z : PDE.Vec d := h • PDE.basisVec k
  have htranslate : HasCompactSupport (fun y => φ (y + z)) :=
    hφcompact.comp_homeomorph (Homeomorph.addRight z)
  have hs : HasCompactSupport (fun y => φ (y + z) - φ y) := htranslate.sub hφcompact
  apply Continuous.integrable_of_hasCompactSupport
  · change Continuous (fun y => ((φ (y + z) - φ y) / h) ^ 2)
    have := hφ.continuous
    fun_prop
  · exact hs.comp_left (g := fun x : ℝ => (x / h) ^ 2) (by simp)

end

section
variable {d : ℕ} (g : PDE.Vec d → ℝ) (hg : Integrable g (volume : Measure (PDE.Vec d)))
  (z : PDE.Vec d)
include hg

private theorem integrable_translate_segment :
    Integrable (fun p : ℝ × PDE.Vec d => g (p.2 + p.1 • z))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume : Measure (PDE.Vec d))) := by
  have hshear : MeasurePreserving
      (fun p : ℝ × PDE.Vec d => (p.1, p.2 + p.1 • z))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume : Measure (PDE.Vec d)))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume : Measure (PDE.Vec d))) := by
    refine MeasurePreserving.skew_product (g := fun t y => y + t • z)
      (MeasurePreserving.id _) ?_ ?_
    · exact measurable_snd.add (measurable_fst.smul measurable_const)
    · filter_upwards [] with t
      exact (measurePreserving_add_right volume (t • z)).map_eq
  exact hshear.integrable_comp_of_integrable (hg.comp_snd _)

private theorem integrable_translate_segmentAverage :
    Integrable (fun y => ∫ t in (0 : ℝ)..1, g (y + t • z)) volume := by
  have hright := (integrable_translate_segment g hg z).integral_prod_right
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    Function.uncurry] using hright

private theorem integral_translate_segmentAverage :
    (∫ y, ∫ t in (0 : ℝ)..1, g (y + t • z)) = ∫ y, g y := by
  have hcomposed' : Integrable (Function.uncurry fun t y => g (y + t • z))
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
        (volume : Measure (PDE.Vec d))) := by
    simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), Function.uncurry_def]
      using integrable_translate_segment g hg z
  have hswap : (∫ t in (0 : ℝ)..1, ∫ y, g (y + t • z)) =
      ∫ y, ∫ t in (0 : ℝ)..1, g (y + t • z) := by
    exact intervalIntegral_integral_swap hcomposed'
  rw [← hswap]
  simp_rw [show (fun t : ℝ => ∫ y, g (y + t • z)) = fun _ => ∫ y, g y by
    funext t
    exact (measurePreserving_add_right volume (t • z)).integral_comp
      (Homeomorph.addRight _).measurableEmbedding g]
  simp

end

/-- A signed coordinate difference quotient of a smooth compactly supported
function is controlled in global `L²` by its Euclidean classical gradient.
The quotient is totalized at `h = 0`. -/
theorem integral_sq_spatialDifferenceQuotient_le_integral_sq_classicalGradient
    {d : ℕ} (φ : PDE.Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcompact : HasCompactSupport φ)
    (k : Fin d) (h : ℝ) :
    (∫ y, ((φ (y + h • PDE.basisVec k) - φ y) / h) ^ 2
      ∂(volume : Measure (PDE.Vec d))) ≤
      ∫ y, PDE.vecEuclideanNorm (PDE.classicalGradient φ y) ^ 2
        ∂(volume : Measure (PDE.Vec d)) := by
  by_cases hh : h = 0
  · simpa [hh] using (integral_nonneg (fun y => sq_nonneg (PDE.vecEuclideanNorm (PDE.classicalGradient φ y))))
  let g (y : PDE.Vec d) := PDE.vecEuclideanNorm (PDE.classicalGradient φ y) ^ 2
  have hg : Integrable g := integrable_sq_classicalGradient φ hφ hφcompact
  rw [← integral_translate_segmentAverage g hg (h • PDE.basisVec k)]
  exact integral_mono (integrable_sq_spatialDifferenceQuotient φ hφ hφcompact k h)
    (integrable_translate_segmentAverage g hg _) (spatialDifferenceQuotient_sq_le_segmentIntegral φ hφ k h hh)

