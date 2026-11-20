module

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
open scoped Real InnerProductSpace ComplexConjugate

/-- An orientation-preserving C¹ change of the boundary parameter, with a
positive lower Jacobian bound on the cut interval. -/
structure IsC1TraceReparam (τ : ℝ → ℝ) (c : ℝ) : Prop where
  monotone : Monotone τ
  lipschitz : ∃ K : NNReal, LipschitzWith K τ
  contDiff : ContDiff ℝ 1 τ
  zero : τ 0 = 0
  endpoint : τ (2 * π) = 2 * π
  lower_pos : 0 < c
  lower_ae : ∀ᵐ θ ∂volume.restrict (Icc (0 : ℝ) (2 * π)), c ≤ deriv τ θ

section

variable {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
include τ c hτ

lemma IsC1TraceReparam.continuous  : Continuous τ := Exists.casesOn hτ.lipschitz fun K hK => LipschitzWith.continuous hK

lemma IsC1TraceReparam.mapsTo  : MapsTo τ (Icc 0 (2 * π)) (Icc 0 (2 * π)) := by
  intro θ hθ
  exact ⟨hτ.zero ▸ hτ.monotone hθ.1, hτ.endpoint ▸ hτ.monotone hθ.2⟩

end

/-- The actual Jacobian controls ordinary coordinate integration after
composition by `τ`; the factor is precisely the reciprocal lower Jacobian. -/
theorem integral_sq_comp_traceReparam_le {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) {q : ℝ → ℂ} (hq : Continuous q) :
    (∫ θ in (0 : ℝ)..(2 * π), ‖q (τ θ)‖ ^ 2) ≤
      (1 / c) * ∫ s in (0 : ℝ)..(2 * π), ‖q s‖ ^ 2 := by
  have hQ := hq.norm.pow 2
  have hQt := hQ.comp hτ.continuous
  have hd := hτ.contDiff.continuous_deriv_one
  have hJ : (∫ θ in (0 : ℝ)..(2 * π), ‖q (τ θ)‖ ^ 2 * deriv τ θ) =
      ∫ s in (0 : ℝ)..(2 * π), ‖q s‖ ^ 2 := by
    have h := intervalIntegral.integral_comp_mul_deriv (a := (0 : ℝ)) (b := 2 * π)
      (fun θ _ => (hτ.contDiff.differentiable_one θ).hasDerivAt)
      hd.continuousOn hQ
    simp_all [hτ.zero, hτ.endpoint]
  have hle : c * (∫ θ in (0 : ℝ)..(2 * π), ‖q (τ θ)‖ ^ 2) ≤
      ∫ θ in (0 : ℝ)..(2 * π), ‖q (τ θ)‖ ^ 2 * deriv τ θ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_ae_restrict (by positivity : (0 : ℝ) ≤ 2 * π)
      ((continuous_const.mul hQt).intervalIntegrable _ _)
      ((hQt.mul hd).intervalIntegrable _ _) ?_
    filter_upwards [hτ.lower_ae] with θ hθ
    nlinarith
  rw [hJ] at hle
  calc
    _ ≤ (∫ s in (0 : ℝ)..(2 * π), ‖q s‖ ^ 2) / c :=
      (le_div_iff₀ hτ.lower_pos).mpr (by linarith)
    _ = _ := by ring

/-- Smooth boundary values in the new parameter, in ordinary `dθ` L². -/
def smoothReparamBoundaryLin {Ω : Set ℂ} {β : ℝ → ℂ} (hβ : IsBoundaryParam Ω β)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c) :
    smoothTraceTests →ₗ[ℂ] BoundaryL2 := smoothBoundaryLin (hβ.continuous.comp hτ.continuous)

section

variable {Ω : Set ℂ}
include Ω

theorem exists_bound_smoothReparamBoundary  (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {β : ℝ → ℂ} (hβ : IsBoundaryParam Ω β)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : smoothTraceTests,
      ‖smoothReparamBoundaryLin hβ hτ f‖ ≤ C * ‖smoothTraceH1Lin hL.1.1 f‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_smoothTraceBoundary hb hL hβ
  have hc := hτ.lower_pos
  refine ⟨C / Real.sqrt c, by positivity, fun f => le_of_sq_le_sq ?_ (by positivity)⟩
  have h := integral_sq_comp_traceReparam_le hτ (q := fun θ => f (β θ))
    (f.property.1.continuous.comp hβ.continuous)
  rw [← norm_sq_smoothBoundary (γ := fun θ => β (τ θ)) (hβ.continuous.comp hτ.continuous) f,
    ← norm_sq_smoothTraceBoundary hβ f] at h
  refine h.trans ?_
  rw [mul_pow, div_pow, Real.sq_sqrt hc.le, one_div_mul_eq_div, div_mul_eq_mul_div]
  gcongr
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hbound f) 2

/-- The actual H¹ trace in the new parameter, by bounded extension of
smooth boundary values from the established dense H¹ restrictions. -/
def h1ReparamBoundaryTrace 
    (hL : IsLipschitzDomain Ω) {β : ℝ → ℂ} (hβ : IsBoundaryParam Ω β)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c) :
    NeumannH1 Ω →L[ℂ] BoundaryL2 :=
  (smoothReparamBoundaryLin hβ hτ).extendOfNorm (smoothTraceH1Lin hL.1.1)

end

section

variable {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {β : ℝ → ℂ} (hβ : IsBoundaryParam Ω β) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
include Ω hb hL β hβ τ c hτ

theorem h1ReparamBoundaryTrace_smooth  (f : smoothTraceTests) :
    h1ReparamBoundaryTrace hL hβ hτ (smoothTraceH1 Ω f) =
      smoothReparamBoundaryLin hβ hτ f := by
  obtain ⟨C, _, hC⟩ := exists_bound_smoothReparamBoundary hb hL hβ hτ
  exact LinearMap.extendOfNorm_eq (denseRange_smoothTraceH1Lin hb hL) ⟨C, hC⟩ f

theorem h1ReparamBoundaryTrace_smooth_ae  (f : smoothTraceTests) :
    (h1ReparamBoundaryTrace hL hβ hτ (smoothTraceH1 Ω f) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * π))] fun θ => f (β (τ θ)) := by
  rw [h1ReparamBoundaryTrace_smooth hb hL hβ hτ f]
  exact (smoothBoundary_memLp (hβ.continuous.comp hτ.continuous) f).coeFn_toLp

/-- Actual agreement on smooth boundary values characterizes the trace,
so its definition is independent of the smooth approximation. -/
theorem h1ReparamBoundaryTrace_unique 
    (T : NeumannH1 Ω →L[ℂ] BoundaryL2)
    (hT : ∀ f : smoothTraceTests, T (smoothTraceH1 Ω f) = smoothReparamBoundaryLin hβ hτ f) :
    h1ReparamBoundaryTrace hL hβ hτ = T := by
  obtain ⟨C, _, hC⟩ := exists_bound_smoothReparamBoundary hb hL hβ hτ
  apply LinearMap.extendOfNorm_unique (denseRange_smoothTraceH1Lin hb hL) C hC T
  apply LinearMap.ext
  assumption

end

end PolyaNeumann

end
