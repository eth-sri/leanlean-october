module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Tactic
public import RequestProject.TraceH1

/-!
# The H¹ trace in a nonconstant-speed boundary parameter

For `γ = β ∘ τ`, the ordinary `dθ` trace estimate follows from the actual
one-dimensional Jacobian identity and the lower bound `τ' ≥ c > 0`.
We use a C¹ change of parameter in this auxiliary bridge so that the
continuous-derivative change-of-variables theorem applies. Its hypotheses
must be proved for any eventual conformal parameterization; this file does
not construct a conformal map or assume such a map's derivative bounds.

The trace is then extended from the same dense smooth restrictions used
by `TraceH1`, into boundary L² with ordinary coordinate measure.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Topology
open scoped Real

/-- An orientation-preserving C¹ change of the boundary parameter, with a
positive lower Jacobian bound on the cut interval. -/
structure IsC1TraceReparam (τ : RealMap) (c : ℝ) : Prop where
  monotone : Monotone τ
  lipschitz : ∃ K : NNReal, LipschitzWith K τ
  contDiff : ContDiff ℝ 1 τ
  zero : τ 0 = 0
  endpoint : τ circlePeriod = 2 * π
  lower_pos : 0 < c
  lower_ae : ∀ᵐ θ ∂volume.restrict boundaryInterval, c ≤ deriv τ θ

section
variable {τ } {c } (hτ : IsC1TraceReparam τ c)
include τ c hτ

lemma IsC1TraceReparam.continuous : Continuous τ := by
  obtain ⟨K, hK⟩ := hτ.lipschitz
  exact hK.continuous

lemma IsC1TraceReparam.mapsTo : MapsTo τ boundaryInterval boundaryInterval := by
  intro θ hθ
  exact ⟨hτ.zero ▸ hτ.monotone hθ.1, hτ.endpoint ▸ hτ.monotone hθ.2⟩

/-- The actual Jacobian controls ordinary coordinate integration after
composition by `τ`; the factor is precisely the reciprocal lower Jacobian. -/
theorem integral_sq_comp_traceReparam_le {q : ComplexCurve} (hq : Continuous q) :
    (∫ θ in (0 : ℝ)..circlePeriod, ‖q (τ θ)‖ ^ 2) ≤
      (1 / c) * ∫ s in (0 : ℝ)..circlePeriod, ‖q s‖ ^ 2 := by
  have hQ : Continuous (fun s => ‖q s‖ ^ 2) := hq.norm.pow 2
  have hQt  := hQ.comp hτ.continuous
  have hd  := hτ.contDiff.continuous_deriv_one
  have hJ : (∫ θ in (0 : ℝ)..circlePeriod, ‖q (τ θ)‖ ^ 2 * deriv τ θ) =
      ∫ s in (0 : ℝ)..circlePeriod, ‖q s‖ ^ 2 := by
    have h := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := 2 * π)
      (fun θ _ => (hτ.contDiff.differentiable_one θ).hasDerivAt)
      hd.continuousOn hQ
    simpa  [hτ.zero, hτ.endpoint] using h
  have hle : c * (∫ θ in (0 : ℝ)..circlePeriod, ‖q (τ θ)‖ ^ 2) ≤
      ∫ θ in (0 : ℝ)..circlePeriod, ‖q (τ θ)‖ ^ 2 * deriv τ θ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_ae_restrict (by positivity)
      ((continuous_const.mul hQt).intervalIntegrable _ _)
      ((hQt.mul hd).intervalIntegrable _ _) ?_
    filter_upwards [hτ.lower_ae] with θ hθ
    nlinarith
  rw [hJ] at hle
  calc
    _ ≤ (∫ s in (0)..circlePeriod, ‖q s‖ ^ 2) / c :=
      (le_div_iff₀ hτ.lower_pos).mpr (by simpa  [mul_comm] using hle)
    _ = _ := by ring

end


section
variable {Ω } (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {β } (hβ : IsBoundaryParam Ω β) {τ } {c } (hτ : IsC1TraceReparam τ c)

include Ω hb hL β hβ τ c hτ in
/-- The geometric trace constant for `β` becomes `C / c` for `β ∘ τ`.
Both integrals use ordinary coordinate measure. -/
theorem trace_sq_le_reparam :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : smoothTraceTests,
      (∫ θ in (0 : ℝ)..circlePeriod, ‖f (β (τ θ))‖ ^ 2) ≤
        (C / c) * ((∫ z in Ω, ‖f z‖ ^ 2) + ∫ z in Ω, gradSq (f : PlaneMap) z) := by
  obtain ⟨C, hC, hbound⟩ := trace_sq_le hb hL hβ
  obtain ⟨Kβ, hKβ⟩ := hβ.lipschitz
  refine ⟨C, hC, fun f => ?_⟩
  obtain ⟨Kf, hKf⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    f.property.2.1 f.property.1 (by simp)
  obtain ⟨B, hB⟩ := f.property.2.1.exists_bound_of_continuous f.property.1.continuous
  have hs := hbound f Kf hKf B hB
  calc
    _ ≤ (1 / c) * ∫ s in (0)..circlePeriod, ‖f (β s)‖ ^ 2 :=
      integral_sq_comp_traceReparam_le hτ (f.property.1.continuous.comp hKβ.continuous)
    _ ≤ (1 / c) * (C * ((∫ z in Ω, ‖f z‖ ^ 2) +
        ∫ z in Ω, gradSq f z)) :=
      mul_le_mul_of_nonneg_left hs (one_div_nonneg.mpr hτ.lower_pos.le)
    _ = _ := by ring

lemma smoothReparamBoundary_memLp  
    (hβ : IsBoundaryParam Ω β)  
    (hτ : IsC1TraceReparam τ c) (f : smoothTraceTests) :
    MemLp (fun θ => f (β (τ θ))) 2 (volume.restrict boundaryHalfOpenInterval) := by
  obtain ⟨Kβ, hKβ⟩ := hβ.lipschitz
  obtain ⟨B, hB⟩ := f.property.2.1.exists_bound_of_continuous f.property.1.continuous
  exact MemLp.of_bound
    (f.property.1.continuous.comp (hKβ.continuous.comp hτ.continuous)).aestronglyMeasurable
    B (Eventually.of_forall fun θ => hB (β (τ θ)))

/-- Smooth boundary values in the new parameter, in ordinary `dθ` L². -/
def smoothReparamBoundaryLin {Ω : PlanarSet} {β : ComplexCurve} (hβ : IsBoundaryParam Ω β)
    {τ : RealMap} {c : ℝ} (hτ : IsC1TraceReparam τ c) :
    smoothTraceTests →ₗ[ℂ] BoundaryL2 where
  toFun f := (smoothReparamBoundary_memLp hβ hτ f).toLp (fun θ => f (β (τ θ)))
  map_add' f g :=
    MemLp.toLp_add (smoothReparamBoundary_memLp hβ hτ f)
      (smoothReparamBoundary_memLp hβ hτ g)
  map_smul' a f := MemLp.toLp_const_smul a (smoothReparamBoundary_memLp hβ hτ f)

private lemma norm_sq_traceReparam_toLp {f : ComplexCurve}
    (hf : MemLp f 2 (volume.restrict boundaryHalfOpenInterval)) :
    ‖hf.toLp f‖ ^ 2 = ∫ θ in (0 : ℝ)..circlePeriod, ‖f θ‖ ^ 2 := by
  let u := hf.toLp f
  have h := congrArg RCLike.re (L2.inner_def (𝕜 := ℂ) u u)
  rw [inner_self_eq_norm_sq, ← integral_re (L2.integrable_inner u u)] at h
  simp_rw [inner_self_eq_norm_sq] at h
  rw [intervalIntegral.integral_of_le (by positivity), h]
  exact integral_congr_ae (hf.coeFn_toLp.fun_comp (fun z : ℂ => ‖z‖ ^ 2))

theorem norm_sq_smoothReparamBoundary  
    (hβ : IsBoundaryParam Ω β)  
    (hτ : IsC1TraceReparam τ c) f :
    ‖smoothReparamBoundaryLin hβ hτ f‖ ^ 2 =
      ∫ θ in (0 : ℝ)..circlePeriod, ‖f (β (τ θ))‖ ^ 2 :=
  norm_sq_traceReparam_toLp (smoothReparamBoundary_memLp hβ hτ f)

include Ω hb hL β hβ τ c hτ in
theorem exists_bound_smoothReparamBoundary :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : smoothTraceTests,
      ‖smoothReparamBoundaryLin hβ hτ f‖ ≤ C * ‖smoothTraceH1Lin hL.1.1 f‖ := by
  obtain ⟨C, hC, hbound⟩ := trace_sq_le_reparam hb hL hβ hτ
  have hCc  := div_nonneg hC hτ.lower_pos.le
  refine ⟨Real.sqrt (C / c), Real.sqrt_nonneg _, fun f => ?_⟩
  have hs := hbound f
  rw [← norm_sq_smoothReparamBoundary hβ hτ f, ← norm_sq_smoothTraceH1 Ω f] at hs
  have heq : (Real.sqrt (C / c) * ‖smoothTraceH1 Ω f‖) ^ 2 =
      (C / c) * ‖smoothTraceH1 Ω f‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hCc]
  have hn : 0 ≤ Real.sqrt (C / c) * ‖smoothTraceH1 Ω f‖ := by positivity
  change ‖smoothReparamBoundaryLin hβ hτ f‖ ≤ Real.sqrt (C / c) * ‖smoothTraceH1 Ω f‖
  nlinarith

/-- The actual H¹ trace in the new parameter, by bounded extension of
smooth boundary values from the established dense H¹ restrictions. -/
def h1ReparamBoundaryTrace {Ω : PlanarSet}
    (hL : IsLipschitzDomain Ω) {β : ComplexCurve} (hβ : IsBoundaryParam Ω β)
    {τ : RealMap} {c : ℝ} (hτ : IsC1TraceReparam τ c) :
    NeumannH1 Ω →L[ℂ] BoundaryL2 :=
  (smoothReparamBoundaryLin hβ hτ).extendOfNorm (smoothTraceH1Lin hL.1.1)

section
include Ω hb hL β hβ τ c hτ

theorem h1ReparamBoundaryTrace_smooth f :
    h1ReparamBoundaryTrace hL hβ hτ (smoothTraceH1 Ω f) =
      smoothReparamBoundaryLin hβ hτ f := by
  obtain ⟨C, _, hC⟩ := exists_bound_smoothReparamBoundary hb hL hβ hτ
  exact LinearMap.extendOfNorm_eq (denseRange_smoothTraceH1Lin hb hL) ⟨C, hC⟩ f

theorem h1ReparamBoundaryTrace_smooth_ae f :
    (h1ReparamBoundaryTrace hL hβ hτ (smoothTraceH1 Ω f) : ComplexCurve)
      =ᵐ[volume.restrict boundaryHalfOpenInterval] fun θ => f (β (τ θ)) := by
  rw [h1ReparamBoundaryTrace_smooth hb hL hβ hτ f]
  exact (smoothReparamBoundary_memLp hβ hτ f).coeFn_toLp

/-- Actual agreement on smooth boundary values characterizes the trace,
so its definition is independent of the smooth approximation. -/
theorem h1ReparamBoundaryTrace_unique
    T
    (hT : ∀ f : smoothTraceTests, T (smoothTraceH1 Ω f) = smoothReparamBoundaryLin hβ hτ f) :
    h1ReparamBoundaryTrace hL hβ hτ = T := by
  obtain ⟨C, _, hC⟩ := exists_bound_smoothReparamBoundary hb hL hβ hτ
  apply LinearMap.extendOfNorm_unique (denseRange_smoothTraceH1Lin hb hL) C hC T
  apply LinearMap.ext
  intro f
  exact hT f

end


end


end PolyaNeumann

end
