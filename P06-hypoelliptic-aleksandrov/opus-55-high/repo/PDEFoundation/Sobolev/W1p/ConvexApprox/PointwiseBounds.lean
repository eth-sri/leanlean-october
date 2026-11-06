module

public import PDEFoundation.Sobolev.W1p.ConvexApprox.Continuity

/-!
# Pointwise bounds for convex-domain smoothing

This file proves constant and zero-scale identities for convex approximation,
the weighted-difference representation of its error, and pointwise bounds in
terms of oscillation and a modulus of continuity. It then upgrades the bounds
to uniform-on-domain convergence along arbitrary admissible scale sequences
and the canonical unit sequence.

## Main results

* `PDE.abs_convexApproxSmoothing_sub_le_of_modulus` controls the error by a
  supplied modulus on the bounded convex domain.
* `PDE.eventually_forall_abs_convexApproxSmoothing_sub_le_of_continuous`
  gives uniform-on-domain convergence along any admissible scale sequence.
* `PDE.eventually_forall_abs_unitConvexApproxSequence_sub_le_of_continuous`
  specializes the uniform bound to the canonical unit sequence.
* `PDE.tendsto_unitConvexApproxSequence_of_continuous` gives pointwise
  convergence at every point of the domain.
-/

@[expose] public section

open scoped Pointwise Convolution

namespace PDE

variable {d : ℕ} {U : Set (Vec d)} {ρ u : Vec d → ℝ} (hU : IsOpenBoundedConvexDomain U)

/-- Membership in the closed unit ball centered at zero gives the expected
norm bound. -/
theorem norm_le_one_of_mem_closedBall_zero_one
     {z : Vec d}
    (hz : z ∈ Metric.closedBall (0 : Vec d) 1) :
    ‖z‖ ≤ 1 := by
  simp_all

/-- Kernel support points produce samples that remain in the convex domain. -/
theorem convexApproxSample_mem_of_tsupport_subset_closedBall
    
    (hU : IsOpenBoundedConvexDomain U)
    {ρ : Vec d → ℝ} {x x0 z : Vec d} {r ε : ℝ}
    (hx : x ∈ U)
    (hball : Metric.closedBall x0 r ⊆ U)
    (hρSub :
      tsupport ρ ⊆ Metric.closedBall (0 : Vec d) 1)
    (hz : z ∈ tsupport ρ)
    (hr : 0 ≤ r) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    convexApproxSample x0 z r ε x ∈ U := by
  exact
    convexApproxSample_mem_of_isOpenBoundedConvexDomain
      hU hx hball hr
      (norm_le_one_of_mem_closedBall_zero_one (hρSub hz))
      hε0 hε1

/-- The smoothing error is the kernel-weighted average of pointwise
differences. -/
theorem convexApproxSmoothing_sub_eq_setIntegral_weightedDiff
    
    (hρ : IsConvexApproxKernel ρ) (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    convexApproxSmoothing ρ u x0 r ε x - u x =
      ∫ z in tsupport ρ,
        ρ z *
          (u (convexApproxSample x0 z r ε x) - u x) := by
  have hInt1 :
      MeasureTheory.IntegrableOn
        _
        (tsupport ρ) :=
    (integrable_convexApproxIntegrand
      hρ.continuous hρ.compactSupport hu
      x0 r ε x).integrableOn
  have hInt2 :
      MeasureTheory.IntegrableOn
        _ (tsupport ρ) :=
    (integrable_convexApproxKernelMulConst
      hρ.continuous hρ.compactSupport (u x)).integrableOn
  have hconst :
      (∫ z in tsupport ρ, ρ z * u x) = u x := by
    rw [MeasureTheory.integral_mul_const,
      hρ.setIntegral_one, one_mul]
  calc
    convexApproxSmoothing ρ u x0 r ε x - u x =
        (∫ z in tsupport ρ,
            convexApproxIntegrand ρ u x0 r ε x z) -
          ∫ z in tsupport ρ, ρ z * u x := by
      simp_all
    _ = ∫ z in tsupport ρ,
          convexApproxIntegrand ρ u x0 r ε x z -
            ρ z * u x := by
      rw [MeasureTheory.integral_sub hInt1 hInt2]
    _ = ∫ z in tsupport ρ,
          ρ z *
            (u _ - u x) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      simp only [convexApproxIntegrand]
      ring

/-- The absolute smoothing error is bounded by the weighted average of the
pointwise oscillation. -/
theorem
    abs_convexApproxSmoothing_sub_le_setIntegral_weightedOscillation
    
    (hρ : IsConvexApproxKernel ρ) (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    |convexApproxSmoothing ρ u x0 r ε x - u x| ≤
      ∫ z in tsupport ρ,
        ρ z *
          |u (convexApproxSample x0 z r ε x) - u x| := by
  rw [
    convexApproxSmoothing_sub_eq_setIntegral_weightedDiff
      hρ hu]
  calc
    |∫ z in tsupport ρ,
        ρ z *
          (u _ - u x)| ≤
        ∫ z in tsupport ρ,
          |ρ z *
            (u _ - u x)| := by
      simpa only using
        (MeasureTheory.abs_integral_le_integral_abs
          (μ :=
            MeasureTheory.volume.restrict _)
          (f := fun z =>
            ρ z *
              (u _ - u x)))
    _ = ∫ z in tsupport ρ,
          ρ z *
            |u _ - u x| := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      rw [abs_mul, abs_of_nonneg (hρ.nonneg z)]

/-- A pointwise oscillation bound on every kernel sample controls the
smoothing error with the same constant. -/
theorem abs_convexApproxSmoothing_sub_le_of_pointwiseOscillation
    
    (hρ : IsConvexApproxKernel ρ) (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) {δ : ℝ}
    (hosc :
      ∀ z ∈ tsupport ρ,
        |u (convexApproxSample x0 z r ε x) - u x| ≤ δ) :
    |convexApproxSmoothing ρ u x0 r ε x - u x| ≤ δ := by
  have hIntLeft :
      MeasureTheory.IntegrableOn
        _
        (tsupport ρ) :=
    (integrable_convexApproxWeightedOscillation
      hρ.continuous hρ.compactSupport hu
      x0 r ε x).integrableOn
  have hIntRight :
      MeasureTheory.IntegrableOn
        _ (tsupport ρ) :=
    (integrable_convexApproxKernelMulConst
      hρ.continuous hρ.compactSupport δ).integrableOn
  calc
    |convexApproxSmoothing ρ u x0 r ε x - u x| ≤
        ∫ z in tsupport ρ,
          ρ z *
            |u _ - u x| :=
      abs_convexApproxSmoothing_sub_le_setIntegral_weightedOscillation
        hρ hu x0 r ε x
    _ ≤ ∫ z in tsupport ρ, ρ z * δ := by
      refine MeasureTheory.setIntegral_mono_on
        hIntLeft hIntRight
        (isClosed_tsupport ρ).measurableSet ?_
      intro z hz
      exact
        mul_le_mul_of_nonneg_left
          (hosc z hz) (hρ.nonneg z)
    _ = δ := by
      rw [MeasureTheory.integral_mul_const,
        hρ.setIntegral_one, one_mul]

/-- A modulus bound at the explicit domain scale
`ε * (2 * Classical.choose hU.isBoundedDomain)` controls the smoothing
error. -/
theorem abs_convexApproxSmoothing_sub_le_of_modulus
    
    (hρ : IsConvexApproxKernel ρ) (hu : Continuous u)
    {x x0 : Vec d} {r ε : ℝ}
    (hx : x ∈ U)
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) {δ : ℝ}
    (hmod :
      ∀ y ∈ U,
        ‖y - x‖ ≤
            ε *
              (2 *
                Classical.choose hU.isBoundedDomain) →
          |u y - u x| ≤ δ) :
    |convexApproxSmoothing ρ u x0 r ε x - u x| ≤ δ := by
  apply
    abs_convexApproxSmoothing_sub_le_of_pointwiseOscillation
      hρ hu x0 r ε x
  intro z hz
  have hy  :=
    convexApproxSample_mem_of_tsupport_subset_closedBall
      hU hx hball hρ.support_subset_closedBall hz
      hr hε0 hε1
  have hdist  :=
    norm_convexApproxSample_sub_le_two_mul_choose_of_isOpenBoundedConvexDomain
      hU hx hball hr
      (norm_le_one_of_mem_closedBall_zero_one
        (hρ.support_subset_closedBall hz))
      hε0
  simp_all

/-- Uniform continuity on the closure supplies a positive scale that controls
the smoothing error uniformly over the whole domain. -/
theorem
    exists_pos_forall_abs_convexApproxSmoothing_sub_le_of_continuous
    
    (hρ : IsConvexApproxKernel ρ) (hu : Continuous u)
    {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > 0,
      ∀ ⦃x : Vec d⦄, x ∈ U →
        ∀ ⦃ε : ℝ⦄,
          0 ≤ ε →
            ε ≤ 1 →
              ε *
                  (2 *
                    Classical.choose hU.isBoundedDomain) ≤
                η →
                |convexApproxSmoothing
                    ρ u x0 r ε x - u x| ≤
                  δ := by
  have hcompact :
      IsCompact (closure U) :=
    hU.isBoundedDomain.isBounded.isCompact_closure
  have huc  :=
    hcompact.uniformContinuousOn_of_continuous
      hu.continuousOn
  rcases
      (Metric.uniformContinuousOn_iff_le.mp huc) δ hδ with
    ⟨η, hηpos, hη⟩
  refine ⟨η, hηpos, ?_⟩
  intro x hx ε hε0 hε1 hεη
  apply
    abs_convexApproxSmoothing_sub_le_of_modulus
      hU hρ hu hx hball hr hε0 hε1
  intro y hy hyx
  have hxcl  :=
    subset_closure hx
  have hycl  :=
    subset_closure hy
  have hdist :
      dist (u y) (u x) ≤ δ := by
    apply hη y hycl x hxcl
    calc
      dist y x = ‖y - x‖ := by
        aesop
      _ ≤ ε *
          (2 *
            Classical.choose hU.isBoundedDomain) :=
        hyx
      _ ≤ η :=
        hεη
  omega

/-- Along any nonnegative scale sequence tending to zero and eventually at
most one, convex approximation converges uniformly on the domain. -/
theorem
    eventually_forall_abs_convexApproxSmoothing_sub_le_of_continuous
    
    (hU : IsOpenBoundedConvexDomain U)
    (hρ : IsConvexApproxKernel ρ) (hu : Continuous u)
    {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r)
    {ε : ℕ → ℝ}
    (hε :
      Filter.Tendsto ε Filter.atTop (nhds 0))
    (hεNonneg :
      ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ ε n)
    (hεLeOne :
      ∀ᶠ n : ℕ in Filter.atTop, ε n ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ ⦃x : Vec d⦄, x ∈ U →
        |convexApproxSmoothing
            ρ u x0 r (ε n) x - u x| ≤
          δ := by
  obtain ⟨η, hηpos, hη⟩ :=
    exists_pos_forall_abs_convexApproxSmoothing_sub_le_of_continuous
      hU hρ hu hball hr hδ
  let C  :=
    2 * Classical.choose hU.isBoundedDomain
  have hCnonneg : 0 ≤ C := by
    grind
  have hscaled :
      Filter.Tendsto
        (fun n : ℕ => ε n * C)
        Filter.atTop (nhds 0) := by
    simpa using hε.mul_const C
  filter_upwards
      [Metric.tendsto_nhds.mp hscaled η hηpos,
        hεNonneg, hεLeOne] with
    n hn hε0 hε1 x hx
  have hlt : ε n * C < η := by
    have hn' :
        |ε n| * |C| < η := by
      simp_all
    simpa only [abs_of_nonneg hε0,
      abs_of_nonneg hCnonneg] using hn'
  grind

end PDE
