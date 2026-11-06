module

public import PDEFoundation.Geometry.ConvexSegment
public import PDEFoundation.Measure.IntervalJensen
public import PDEFoundation.Sobolev.ClassicalGradient
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Smooth Euclidean estimates along affine segments

These are the domain-independent fundamental-theorem-of-calculus estimates
used by the diameter-only convex-domain Poincaré proof. Directional
derivatives are paired with `classicalGradient` through the explicit
Euclidean dot product, so no norm from the inherited finite-product metric
enters the estimate.
-/

@[expose] public section

namespace PDE

private theorem hasDerivAt_segmentBlend {d }
    (x y : Vec d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => segmentBlend x s y)
      (x - y) t := by
  have hsmul :
      HasDerivAt (fun s : ℝ => s • (x - y))
        (x - y) t := by
    simpa using
      (hasDerivAt_id t).smul_const (x - y)
  convert (hsmul.const_add y) using 1
  funext s
  exact segmentBlend_eq_add_smul_sub x y s

/- Fundamental theorem of calculus along the segment from `y` to `x`. -/
theorem sub_eq_integral_vecDot_classicalGradient_along_segment
    {d u}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x y : Vec d) :
    u x - u y =
      ∫ t in (0 : ℝ)..1,
        vecDot (classicalGradient u (segmentBlend x t y))
          (x - y) := by
  have _h_inl_12 : u x - u y =
      ∫ t in (0 : ℝ)..1,
        (fderiv ℝ u (segmentBlend x t y)) (x - y) := by
      let γ : ℝ → Vec d := fun t => segmentBlend x t y
      have hγ : ∀ t : ℝ, HasDerivAt γ (x - y) t := by
        intro t
        simpa [γ] using hasDerivAt_segmentBlend x y t
      have huγ :
          ∀ t : ℝ,
            HasDerivAt (u ∘ γ)
              ((fderiv ℝ u (γ t)) (x - y)) t := by
        intro t
        exact
          ((hu.differentiable (by norm_num)).differentiableAt).hasFDerivAt
            |>.comp_hasDerivAt t (hγ t)
      have hγCont : Continuous γ :=
        continuous_iff_continuousAt.2 fun t =>
          (hγ t).continuousAt
      have hfderivCont : Continuous (fderiv ℝ u) := by
        have h1 : ContDiff ℝ 1 u :=
          hu.of_le (by norm_num)
        exact h1.continuous_fderiv (by norm_num)
      have hint :
          IntervalIntegrable
            (fun t => (fderiv ℝ u (γ t)) (x - y))
            MeasureTheory.volume 0 1 := by
        exact
          ((hfderivCont.comp hγCont).clm_apply continuous_const)
            |>.intervalIntegrable _ _
      have hftc :
          ∫ t in (0 : ℝ)..1,
              (fderiv ℝ u (γ t)) (x - y) =
            u x - u y := by
        simpa [Function.comp, γ, segmentBlend] using
          (intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun t _ht => huγ t) hint)
      exact hftc.symm

    /- Exact Euclidean-gradient form of the segment fundamental theorem. -/
  simpa only [fderiv_apply_eq_vecDot_classicalGradient] using _h_inl_12

/- Jensen along the unit segment followed by Euclidean Cauchy--Schwarz. -/
theorem abs_sub_rpow_le_integral_euclideanGradient_mul_distance_rpow
    {d : ℕ} {p : ℝ} (hp : 1 ≤ p)
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (x y : Vec d) :
    |u x - u y| ^ p ≤
      ∫ t in (0 : ℝ)..1,
        (vecEuclideanNorm
            (classicalGradient u (segmentBlend x t y)) *
          vecEuclideanNorm (x - y)) ^ p := by
  have hpNonneg : 0 ≤ p :=
    zero_le_one.trans hp
  let γ : ℝ → Vec d :=
    fun t => segmentBlend x t y
  have hγCont : Continuous γ := by
    refine continuous_iff_continuousAt.2 ?_
    intro t
    exact (hasDerivAt_segmentBlend x y t).continuousAt
  have hgradCont :
      Continuous (classicalGradient u) :=
    PDE.ContDiff.continuous_classicalGradient
      (hu.of_le (by norm_num) : ContDiff ℝ 1 u)
  have hdotCont :
      Continuous
        (fun t =>
          vecDot (classicalGradient u (γ t)) (x - y)) := by
    unfold vecDot
    refine continuous_finsetSum Finset.univ ?_
    intro i _hi
    exact
      ((continuous_apply i).comp
        (hgradCont.comp hγCont)).mul continuous_const
  have hdotPowCont :
      Continuous
        (fun t =>
          |vecDot (classicalGradient u (γ t)) (x - y)| ^ p) :=
    (Real.continuous_rpow_const hpNonneg).comp hdotCont.abs
  have hboundCont :
      Continuous
        (fun t =>
          (vecEuclideanNorm
              (classicalGradient u (γ t)) *
            vecEuclideanNorm (x - y)) ^ p) := by
    exact
      Real.continuous_rpow_const hpNonneg
        |>.comp
          ((continuous_vecEuclideanNorm.comp
            (hgradCont.comp hγCont)).mul continuous_const)
  calc
    |u x - u y| ^ p =
        |∫ t in (0 : ℝ)..1,
          vecDot (classicalGradient u (γ t))
            (x - y)| ^ p := by
      rw [show u x - u y =
        ∫ t in (0 : ℝ)..1,
          vecDot (classicalGradient u (γ t))
            (x - y) by
          simpa [γ] using
            sub_eq_integral_vecDot_classicalGradient_along_segment
              hu x y]
    _ ≤ ∫ t in (0 : ℝ)..1,
        |vecDot (classicalGradient u (γ t))
          (x - y)| ^ p :=
      abs_intervalIntegral_rpow_le_intervalIntegral_abs_rpow
        hp (hdotCont.intervalIntegrable _ _)
          (hdotPowCont.intervalIntegrable _ _)
    _ ≤ ∫ t in (0 : ℝ)..1,
        (vecEuclideanNorm
            (classicalGradient u (γ t)) *
          vecEuclideanNorm (x - y)) ^ p := by
      refine intervalIntegral.integral_mono_on
        zero_le_one
        (hdotPowCont.intervalIntegrable _ _)
        (hboundCont.intervalIntegrable _ _) ?_
      intro t _ht
      exact Real.rpow_le_rpow (abs_nonneg _)
        (abs_vecDot_le_vecEuclideanNorm_mul
          (classicalGradient u (γ t)) (x - y))
        hpNonneg

/- Diameter form of the segment estimate at every finite real exponent. -/
theorem abs_sub_rpow_le_diameter_rpow_mul_integral_euclideanGradient_rpow
    {d : ℕ} {p : ℝ} (hp : 1 ≤ p)
    {U : Set (Vec d)} {D : ℝ}
    (hUDiameter : HasEuclideanDiameterLE U D)
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {x y : Vec d} (hx : x ∈ U) (hy : y ∈ U) :
    |u x - u y| ^ p ≤
      D ^ p *
        ∫ t in (0 : ℝ)..1,
          vecEuclideanNorm
            (classicalGradient u (segmentBlend x t y)) ^ p := by
  have hpNonneg : 0 ≤ p :=
    zero_le_one.trans hp
  have hD : 0 ≤ D :=
    (vecEuclideanNorm_nonneg (x - y)).trans
      (hUDiameter hx hy)
  have hgradCont :
      Continuous
        (fun t : ℝ =>
          vecEuclideanNorm
            (classicalGradient u (segmentBlend x t y))) := by
    exact
      continuous_vecEuclideanNorm.comp
        ((PDE.ContDiff.continuous_classicalGradient
          (hu.of_le (by norm_num) : ContDiff ℝ 1 u)).comp
            (continuous_iff_continuousAt.2 fun t =>
              (hasDerivAt_segmentBlend x y t).continuousAt))
  have hleftCont :
      Continuous
        (fun t : ℝ =>
          (vecEuclideanNorm
              (classicalGradient u (segmentBlend x t y)) *
            vecEuclideanNorm (x - y)) ^ p) :=
    (Real.continuous_rpow_const hpNonneg).comp
      (hgradCont.mul continuous_const)
  have hrightCont :
      Continuous
        (fun t : ℝ =>
          vecEuclideanNorm
              (classicalGradient u (segmentBlend x t y)) ^ p *
            D ^ p) :=
    ((Real.continuous_rpow_const hpNonneg).comp hgradCont)
      |>.mul continuous_const
  calc
    |u x - u y| ^ p ≤
        ∫ t in (0 : ℝ)..1,
          (vecEuclideanNorm
              (classicalGradient u (segmentBlend x t y)) *
            vecEuclideanNorm (x - y)) ^ p :=
      abs_sub_rpow_le_integral_euclideanGradient_mul_distance_rpow
        hp hu x y
    _ ≤ ∫ t in (0 : ℝ)..1,
        vecEuclideanNorm
            (classicalGradient u (segmentBlend x t y)) ^ p *
          D ^ p := by
      refine intervalIntegral.integral_mono_on
        zero_le_one
        (hleftCont.intervalIntegrable _ _)
        (hrightCont.intervalIntegrable _ _) ?_
      intro t _ht
      rw [Real.mul_rpow
        (vecEuclideanNorm_nonneg _) (vecEuclideanNorm_nonneg _)]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (vecEuclideanNorm_nonneg _)
          (hUDiameter hx hy) hpNonneg)
        (Real.rpow_nonneg (vecEuclideanNorm_nonneg _) p)
    _ = D ^ p *
        ∫ t in (0 : ℝ)..1,
          vecEuclideanNorm
            (classicalGradient u (segmentBlend x t y)) ^ p := by
      rw [intervalIntegral.integral_mul_const]
      ring

end PDE
