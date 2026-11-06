module

public import PDEFoundation.Sobolev.W1p.ConvexApprox.Continuity
import Lean.Elab.Tactic.Grind



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

 public section

open scoped Pointwise Convolution

namespace PDE

/-- Membership in the closed unit ball centered at zero gives the expected
norm bound. -/
theorem norm_le_one_of_mem_closedBall_zero_one
    {d : ℕ} {z : Vec d}
    (hz : z ∈ Metric.closedBall (0 : Vec d) 1) :
    ‖z‖ ≤ 1 := by
  simpa only [Metric.mem_closedBall, dist_zero_right] using hz

variable {d : ℕ}

/-- Kernel support points produce samples that remain in the convex domain. -/
theorem convexApproxSample_mem_of_tsupport_subset_closedBall
     {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {ρ : Vec d → ℝ} {x x0 z : Vec d} {r ε : ℝ}
    (hx : x ∈ U)
    (hball : Metric.closedBall x0 r ⊆ U)
    (hρSub :
      tsupport ρ ⊆ Metric.closedBall (0 ) 1)
    (hz : z ∈ tsupport ρ)
    (hr : 0 ≤ r) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    convexApproxSample x0 z r ε x ∈ U := convexApproxSample_mem_of_isOpenBoundedConvexDomain
      hU hx hball hr
      (norm_le_one_of_mem_closedBall_zero_one (hρSub hz))
      hε0 hε1

section
variable {ρ u : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ) (hu : Continuous u) (x0 : Vec d) (r ε : ℝ) (x : Vec d)

include hρ hu
/-- The smoothing error is the kernel-weighted average of pointwise
differences. -/
theorem convexApproxSmoothing_sub_eq_setIntegral_weightedDiff
      :
    convexApproxSmoothing ρ u x0 r ε x - u x =
      ∫ z in tsupport ρ,
        ρ z *
          (u (convexApproxSample x0 z r ε x) - u x) := by
  have hInt1 :
      MeasureTheory.IntegrableOn
        ((convexApproxIntegrand ρ u x0 r ε x))
        (tsupport ρ) :=
    (integrable_convexApproxIntegrand
      hρ.continuous hρ.compactSupport hu
      x0 r ε x).integrableOn
  have hInt2 :
      MeasureTheory.IntegrableOn
        (fun z => ρ z * u x) (tsupport ρ) :=
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
      rw [convexApproxSmoothing]
      conv_lhs => rw [← hconst]
    _ = ∫ z in tsupport ρ,
          convexApproxIntegrand ρ u x0 r ε x z -
            ρ z * u x := by
      rw [MeasureTheory.integral_sub hInt1 hInt2]
    _ = ∫ z in tsupport ρ,
          ρ z *
            (u (convexApproxSample x0 z r ε x) - u x) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      simp only [convexApproxIntegrand]
      ring

/-- The absolute smoothing error is bounded by the weighted average of the
pointwise oscillation. -/
theorem
    abs_convexApproxSmoothing_sub_le_setIntegral_weightedOscillation
      :
    |convexApproxSmoothing ρ u x0 r ε x - u x| ≤
      ∫ z in tsupport ρ,
        ρ z *
          |u (convexApproxSample x0 z r ε x) - u x| := by
  rw [
    convexApproxSmoothing_sub_eq_setIntegral_weightedDiff
      hρ hu x0 r ε x]
  calc
    |∫ z in tsupport ρ,
        ρ z *
          (u (convexApproxSample x0 z r ε x) - u x)| ≤
        ∫ z in tsupport ρ,
          |ρ z *
            (u (convexApproxSample x0 z r ε x) - u x)| := MeasureTheory.abs_integral_le_integral_abs
    _ = ∫ z in tsupport ρ,
          ρ z *
            |u (convexApproxSample x0 z r ε x) - u x| := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      rw [abs_mul, abs_of_nonneg (hρ.nonneg z)]

/-- A pointwise oscillation bound on every kernel sample controls the
smoothing error with the same constant. -/
theorem abs_convexApproxSmoothing_sub_le_of_pointwiseOscillation
      {δ : ℝ}
    (hosc :
      ∀ z ∈ tsupport ρ,
        |u (convexApproxSample x0 z r ε x) - u x| ≤ δ) :
    |convexApproxSmoothing ρ u x0 r ε x - u x| ≤ δ := (Trans.trans
  (Trans.trans (abs_convexApproxSmoothing_sub_le_setIntegral_weightedOscillation hρ hu x0 r ε x)
    (MeasureTheory.setIntegral_mono_on
      (MeasureTheory.Integrable.integrableOn
        (integrable_convexApproxWeightedOscillation (IsConvexApproxKernel.continuous hρ) hρ.compactSupport hu x0 r ε x))
      (MeasureTheory.Integrable.integrableOn
        (integrable_convexApproxKernelMulConst (IsConvexApproxKernel.continuous hρ) hρ.compactSupport δ))
      (IsClosed.measurableSet (isClosed_tsupport ρ)) fun z hz => mul_le_mul_of_nonneg_left (hosc z hz) (hρ.nonneg z)))
  (Eq.mpr (id (congrArg (fun _a => _a = δ) (MeasureTheory.integral_mul_const δ ρ)))
    (Eq.mpr (id (congrArg (fun _a => _a * δ = δ) hρ.setIntegral_one))
      (Eq.mpr (id (congrArg (fun _a => _a = δ) (one_mul δ))) (Eq.refl δ)))))
end


variable {U : Set (Vec d)}

section
variable {ρ u : Vec d → ℝ} (hU : IsOpenBoundedConvexDomain U) (hρ : IsConvexApproxKernel ρ) (hu : Continuous u)

include hρ hu
/-- A modulus bound at the explicit domain scale
`ε * (2 * Classical.choose hU.isBoundedDomain)` controls the smoothing
error. -/
theorem abs_convexApproxSmoothing_sub_le_of_modulus


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
  exact hmod _ hy hdist

/-- Uniform continuity on the closure supplies a positive scale that controls
the smoothing error uniformly over the whole domain. -/
theorem
    exists_pos_forall_abs_convexApproxSmoothing_sub_le_of_continuous


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
                  δ := (Exists.casesOn
  (Metric.uniformContinuousOn_iff_le.mp
    (IsCompact.uniformContinuousOn_of_continuous
      (Bornology.IsBounded.isCompact_closure (IsBoundedDomain.isBounded (IsOpenBoundedConvexDomain.isBoundedDomain hU)))
      (Continuous.continuousOn hu))
    δ hδ)
  fun η h =>
  And.casesOn h fun hηpos hη =>
    Exists.intro η
      ⟨hηpos, fun ⦃x⦄ hx ⦃ε⦄ hε0 hε1 hεη =>
        abs_convexApproxSmoothing_sub_le_of_modulus hU hρ hu hx hball hr hε0 hε1 fun y hy hyx =>
          hη y (subset_closure hy) x (subset_closure hx) (Trans.trans (Trans.trans (Eq.refl (dist y x)) hyx) hεη)⟩)
end


/-- The explicit diameter surrogate used in the modulus bound is
nonnegative. -/
theorem two_mul_choose_isBoundedDomain_nonneg

    (hU : IsBoundedDomain U) :
    0 ≤ 2 * Classical.choose hU := by
  grind

/-- Along any nonnegative scale sequence tending to zero and eventually at
most one, convex approximation converges uniformly on the domain. -/
theorem
    eventually_forall_abs_convexApproxSmoothing_sub_le_of_continuous

    {ρ u : Vec d → ℝ}
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
  let C : ℝ :=
    2 * Classical.choose hU.isBoundedDomain


  filter_upwards
      [Metric.tendsto_nhds.mp (by
          simpa only [zero_mul] using hε.mul_const C) η hηpos,
        hεNonneg, hεLeOne] with
    n hn hε0 hε1 x hx

  exact hη hx hε0 hε1 (show ε n * C < η by
      have hn' :
          |ε n| * |C| < η := by
        simpa only [Real.dist_eq, sub_zero, abs_mul] using hn
      simpa only [abs_of_nonneg hε0,
        abs_of_nonneg (show 0 ≤ C by
            exact two_mul_choose_isBoundedDomain_nonneg
                hU.isBoundedDomain)] using hn').le

end PDE
