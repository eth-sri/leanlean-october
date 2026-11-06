module

public import PDEFoundation.Measure.AffineVolume
public import PDEFoundation.Sobolev.W1p.ConvexApprox.Geometry
public import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Convex-domain smoothing kernels

This file defines the normalized smooth kernel and the affine
convex-approximation operator. It also records the exact positive-dilation
Jacobian formulas and the convolution representation used by later smoothness,
weak-derivative, and convergence modules.
-/

@[expose] public section

open scoped Pointwise Convolution

namespace PDE

/-- Cache smooth-bump existence on native vectors for this module and its
transitive importers. -/
private instance instHasContDiffBumpVec (d : ℕ) :
    HasContDiffBump (Vec d) :=
  inferInstance

/-- A nonnegative smooth unit-mass kernel supported in the closed unit ball
for the inherited native-vector norm. -/
structure IsConvexApproxKernel {d : ℕ} (ρ : Vec d → ℝ) : Prop where
  smooth : ContDiff ℝ PDE.smoothOrder ρ
  compactSupport : HasCompactSupport ρ
  support_subset_closedBall :
    tsupport ρ ⊆ Metric.closedBall (0 ) 1
  nonneg : ∀ z, 0 ≤ ρ z
  setIntegral_one : ∫ z in tsupport ρ, ρ z = 1

namespace IsConvexApproxKernel

theorem continuous {d : ℕ} {ρ : Vec d → ℝ}
    (hρ : IsConvexApproxKernel ρ) :
    Continuous ρ :=
  hρ.smooth.continuous

end IsConvexApproxKernel

namespace ContDiffBump

theorem isConvexApproxKernel_normed {d : ℕ}
    (φ : ContDiffBump (0 : Vec d)) (hφ : φ.rOut ≤ 1) :
    IsConvexApproxKernel (φ.normed MeasureTheory.volume) := by
  refine
    { smooth := (ContDiffBump.contDiff_normed φ)
      compactSupport := (ContDiffBump.hasCompactSupport_normed φ)
      support_subset_closedBall := by
        rw [φ.tsupport_normed_eq (μ := MeasureTheory.volume)]
        exact Metric.closedBall_subset_closedBall hφ
      nonneg := (ContDiffBump.nonneg_normed φ)
      setIntegral_one := (Trans.trans
  (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => image_eq_zero_of_notMem_tsupport hz)
  (ContDiffBump.integral_normed φ)) }

end ContDiffBump

/-- A concrete smooth bump centered at the origin with outer radius `1`. -/
noncomputable def unitContDiffBump {d : ℕ} :
    ContDiffBump (0 : Vec d) :=
  ⟨(1 / 2 : ℝ), 1, by positivity, by norm_num⟩

variable {d : ℕ}

/-- The normalized kernel associated with `unitContDiffBump`. -/
noncomputable def unitConvexApproxKernel  :
    Vec d → ℝ :=
  (unitContDiffBump (d := d)).normed MeasureTheory.volume

theorem isConvexApproxKernel_unitConvexApproxKernel  :
    IsConvexApproxKernel
      (unitConvexApproxKernel (d := d)) := by
  simp_all [unitConvexApproxKernel, unitContDiffBump, ContDiffBump.isConvexApproxKernel_normed]

variable (n : ℕ)

/-- The standard positive scale sequence for convex approximation. -/
noncomputable def unitConvexApproxScale  : ℝ :=
  1 / ((n : ℝ) + 1)

theorem unitConvexApproxScale_pos  :
    0 < unitConvexApproxScale n := by
  dsimp only [unitConvexApproxScale]
  positivity

theorem tendsto_unitConvexApproxScale_zero :
    Filter.Tendsto unitConvexApproxScale
      Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat

variable {d : ℕ}

variable (ρ u : Vec d → ℝ) (x0 : Vec d) (r ε : ℝ)

variable (x z : Vec d)

/-- The integrand defining convex approximation at a point. -/
def convexApproxIntegrand

     : ℝ :=
  ρ z * u (convexApproxSample x0 z r ε x)

@[simp]
theorem convexApproxIntegrand_apply

     :
    convexApproxIntegrand ρ u x0 r ε x z =
      ρ z * u (convexApproxSample x0 z r ε x) :=
  rfl

variable (x : Vec d)

/-- The convex-domain smoothing operator attached to a kernel `ρ`. -/
noncomputable def convexApproxSmoothing

     : ℝ :=
  ∫ z in tsupport ρ, convexApproxIntegrand ρ u x0 r ε x z

@[simp]
theorem convexApproxSmoothing_apply

     :
    convexApproxSmoothing ρ u x0 r ε x =
      ∫ z in tsupport ρ,
        convexApproxIntegrand ρ u x0 r ε x z :=
  rfl

/-- The concrete convex smoothing sequence using the unit kernel and scale. -/
noncomputable def unitConvexApproxSequence
    (u : Vec d → ℝ) (x0 : Vec d) (r : ℝ) (n : ℕ) :
    Vec d → ℝ :=
  (convexApproxSmoothing (unitConvexApproxKernel ) u x0 r (unitConvexApproxScale n))

/-- Rescale a kernel by a positive length `a`, displaying the exact
dimension-`d` Jacobian factor. -/
noncomputable def scaledConvexApproxKernel
    (ρ : Vec d → ℝ) (a : ℝ) : Vec d → ℝ :=
  fun y => (a ^ d)⁻¹ * ρ (a⁻¹ • y)

variable {ρ : Vec d → ℝ}

theorem continuous_scaledConvexApproxKernel
     (hρ : Continuous ρ) (a : ℝ) :
    Continuous (scaledConvexApproxKernel ρ a) := by
  unfold scaledConvexApproxKernel
  fun_prop

theorem contDiff_scaledConvexApproxKernel
     (hρ : IsConvexApproxKernel ρ)
    (a : ℝ) :
    ContDiff ℝ PDE.smoothOrder
      (scaledConvexApproxKernel ρ a) := (ContDiff.mul contDiff_const (ContDiff.comp hρ.smooth (contDiff_const_smul a⁻¹)))

theorem measurable_scaledConvexApproxKernel
     (hρ : Continuous ρ) (a : ℝ) :
    Measurable (scaledConvexApproxKernel ρ a) :=
  (continuous_scaledConvexApproxKernel hρ a).measurable

theorem hasCompactSupport_scaledConvexApproxKernel
     (hρ : HasCompactSupport ρ)
    {a : ℝ} (ha : 0 < a) :
    HasCompactSupport (scaledConvexApproxKernel ρ a) := (HasCompactSupport.mul_left (HasCompactSupport.comp_smul hρ (inv_ne_zero (LT.lt.ne' ha))))

section
variable (hρ : IsConvexApproxKernel ρ) {a : ℝ}

include hρ
theorem integrable_scaledConvexApproxKernel
      (ha : 0 < a) :
    MeasureTheory.Integrable
      (scaledConvexApproxKernel ρ a) := (continuous_scaledConvexApproxKernel hρ.continuous a).integrable_of_hasCompactSupport
      (hasCompactSupport_scaledConvexApproxKernel
        hρ.compactSupport ha)

theorem scaledConvexApproxKernel_nonneg
      (_ha : 0 < a) (y : Vec d) :
    0 ≤ scaledConvexApproxKernel ρ a y := mul_nonneg (by
      positivity) (hρ.nonneg _)

theorem integral_scaledConvexApproxKernel
      (ha : 0 < a) :
    ∫ y, scaledConvexApproxKernel ρ a y = 1 := by
  have haNe  :=
    ha.ne'

  rw [←
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (by
          intro y hy

          simp only [scaledConvexApproxKernel,
            image_eq_zero_of_notMem_tsupport (show a⁻¹ • y ∉ tsupport ρ by
                intro hmem
                apply hy
                exact Set.mem_smul_set.mpr
                  ⟨a⁻¹ • y, hmem, by
                    rw [smul_smul, mul_inv_cancel₀ haNe, one_smul]⟩), mul_zero])]
  calc
    ∫ y in a • tsupport ρ,
        scaledConvexApproxKernel ρ a y
        ∂MeasureTheory.volume =
        (a ^ d)⁻¹ *
          ∫ y in a • tsupport ρ, ρ (a⁻¹ • y)
            ∂MeasureTheory.volume := by
      simp only [scaledConvexApproxKernel,
        MeasureTheory.integral_const_mul]
    _ = ∫ z in tsupport ρ, ρ z
          ∂MeasureTheory.volume := by
      simpa [smul_eq_mul, smul_smul,
        inv_mul_cancel₀ haNe, mul_inv_cancel₀ haNe] using
        (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
          (μ := MeasureTheory.volume)
          (f := fun y  => ρ (a⁻¹ • y))
          (s := tsupport ρ) ha).symm
    _ = 1 :=
      hρ.setIntegral_one
end


theorem translateSet_smul_subset_of_convexApproxSample_mapsTo
     {U : Set (Vec d)}
    {x0 z : Vec d} {r ε : ℝ}
    (hmap :
      Set.MapsTo (convexApproxSample x0 z r ε) U U) :
    translateSet (ε • (x0 - r • z)) ((1 - ε) • U) ⊆
      U := by
  intro y hy
  rcases hy with ⟨w, hw, hyw⟩
  rcases Set.mem_smul_set.mp hw with ⟨x, hx, rfl⟩

  rw [hyw]
  exact (hmap hx)

theorem setIntegral_comp_smul_add_of_pos
     {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a : ℝ} (ha : 0 < a) (b : Vec d) (U : Set (Vec d))
    (f : Vec d → E) :
    ∫ x in U, f (a • x + b) ∂MeasureTheory.volume =
      (a ^ d)⁻¹ •
        ∫ y in translateSet b (a • U), f y
          ∂MeasureTheory.volume := by
  calc
    ∫ x in U, f (a • x + b) ∂MeasureTheory.volume =
        (a ^ d)⁻¹ •
          ∫ z in a • U, f (z + b)
            ∂MeasureTheory.volume := by
      simpa [Vec] using
        (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
          (μ := MeasureTheory.volume)
          (f := fun z  => f (z + b))
          (s := U) ha)
    _ = (a ^ d)⁻¹ •
          ∫ y in translateSet b (a • U), f y
            ∂MeasureTheory.volume := by
      rw [setIntegral_comp_addRight_translateSet
          b (a • U) f]

variable {ρ u : Vec d → ℝ} {U : Set (Vec d)}

theorem convolution_scaledConvexApproxKernel_indicator_eq_setIntegral

    {x0 x : Vec d} {r ε : ℝ}
    (hr : 0 < r) (hε0 : 0 < ε) :
    (scaledConvexApproxKernel ρ (ε * r) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, MeasureTheory.volume]
      Set.indicator U u) ((1 - ε) • x + ε • x0) =
      ∫ z in tsupport ρ,
        ρ z * Set.indicator U u
          (((1 - ε) • x + ε • x0) - (ε * r) • z)
          ∂MeasureTheory.volume := by
  let a : ℝ :=
    ε * r
  let A : Vec d :=
    (1 - ε) • x + ε • x0
  have ha : 0 < a := by
    dsimp only [a]
    positivity
  have haNe  :=
    ha.ne'
  change
    ∫ t, scaledConvexApproxKernel ρ a t *
        Set.indicator U u (A - t) ∂MeasureTheory.volume =
      ∫ z in tsupport ρ,
        ρ z * Set.indicator U u (A - a • z)
          ∂MeasureTheory.volume
  simp only [scaledConvexApproxKernel]

  rw [←
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (by
          intro y hy

          simp only [image_eq_zero_of_notMem_tsupport (show a⁻¹ • y ∉ tsupport ρ by
              intro hmem
              apply hy
              exact Set.mem_smul_set.mpr
                ⟨a⁻¹ • y, hmem, by
                  rw [smul_smul, mul_inv_cancel₀ haNe, one_smul]⟩),
            zero_mul, mul_zero])]
  have hmul :
      (fun y  =>
        ((a ^ d)⁻¹ * ρ (a⁻¹ • y)) *
          Set.indicator U u (A - y)) =
        fun y  =>
          (a ^ d)⁻¹ *
            (ρ (a⁻¹ • y) * Set.indicator U u (A - y)) := by
    funext y
    ring
  calc
    ∫ y in a • tsupport ρ,
        ((a ^ d)⁻¹ * ρ (a⁻¹ • y)) *
          Set.indicator U u (A - y) ∂MeasureTheory.volume =
        (a ^ d)⁻¹ *
          ∫ y in a • tsupport ρ,
            ρ (a⁻¹ • y) * Set.indicator U u (A - y)
              ∂MeasureTheory.volume := by
      rw [hmul, MeasureTheory.integral_const_mul]
    _ = ∫ z in tsupport ρ,
          ρ z * Set.indicator U u (A - a • z)
            ∂MeasureTheory.volume := by
      simpa [smul_eq_mul, mul_assoc, mul_left_comm,
        mul_comm, sub_eq_add_neg, smul_smul,
        inv_mul_cancel₀ haNe, mul_inv_cancel₀ haNe,
        zero_smul, add_zero] using
        (setIntegral_comp_smul_add_of_pos
          (d := d) (E := ℝ) (a := a) ha (b := 0)
          (U := tsupport ρ)
          (f := fun y  =>
            ρ (a⁻¹ • y) * Set.indicator U u (A - y))).symm

theorem
    convexApproxSmoothing_eq_convolution_scaledConvexApproxKernel_indicator

    (hU : IsOpenBoundedConvexDomain U)
    (hρ : IsConvexApproxKernel ρ)
    {x0 x : Vec d} {r ε : ℝ} (hx : x ∈ U)
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε0 : 0 < ε) (hε1 : ε < 1) :
    convexApproxSmoothing ρ u x0 r ε x =
      (scaledConvexApproxKernel ρ (ε * r) ⋆[
          ContinuousLinearMap.lsmul ℝ ℝ,
          MeasureTheory.volume]
        Set.indicator U u) ((1 - ε) • x + ε • x0) := by
  rw [
    convolution_scaledConvexApproxKernel_indicator_eq_setIntegral
      hr hε0,
    convexApproxSmoothing]

  apply MeasureTheory.integral_congr_ae
  change
    ∀ᵐ z ∂MeasureTheory.volume.restrict (tsupport ρ),
      convexApproxIntegrand ρ u x0 r ε x z =
        ρ z * Set.indicator U u
          (((1 - ε) • x + ε • x0) - (ε * r) • z)
  rw [MeasureTheory.ae_restrict_iff' ((isClosed_tsupport (f := ρ)).measurableSet)]
  filter_upwards with z hz

  have hsampleMem  :=
    convexApproxSample_mem_of_isOpenBoundedConvexDomain
      hU hx hball hr.le (by
          simpa only [Metric.mem_closedBall, dist_zero_right] using
            hρ.support_subset_closedBall hz) hε0.le (le_of_lt hε1)
  have hsampleEq :
      ((1 - ε) • x + ε • x0) - (ε * r) • z =
        convexApproxSample x0 z r ε x := by
    simp [convexApproxSample, sub_eq_add_neg, smul_smul,
      add_assoc, add_left_comm, add_comm]
  simp_all

end PDE
