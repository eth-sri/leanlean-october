module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinODE

/-!
# Reverse-time finite Galerkin weak form

This module extends an exact finite Galerkin basis-row equation to every test
vector in that same finite Galerkin space.  It makes no limiting or time-
integrated assertion.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open scoped BigOperators ENNReal Matrix Matrix.Norms.Elementwise RealInnerProductSpace

/-- The mass-inverted rate satisfies the equation against any finite Galerkin test. -/
theorem galerkinRate_weak {d : ℕ} {Ω : Set (PDE.Vec d)}
    {r₀ r₁ lam : ℝ} (P : ReverseTimeGalerkinProblem Ω r₀ r₁ lam)
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀)) (x : GalerkinCoordinates P.hΩ N)
    (v : galerkinSpace P.hΩ N) :
    let u := galerkinReconstruct P.hΩ N x
    let du := galerkinReconstruct P.hΩ N (galerkinRate P N τ x)
    inner ℝ (valueCLM P.hΩ du) (valueCLM P.hΩ v) + P.form τ u v = P.sourceRaw τ v := by
  let u := galerkinReconstruct P.hΩ N x
  let du := galerkinReconstruct P.hΩ N (galerkinRate P N τ x)
  let A := (innerSL ℝ (valueCLM P.hΩ du)).comp (valueCLM P.hΩ) +
    reverseTimeSpatialFormOperator r₀ r₁ P.h₀₁ P.hΩ P.hΩbounded P.a P.b P.c
      P.haSmooth P.hbSmooth P.hcSmooth τ u
  let i := (galerkinSpace P.hΩ N).subtype
  have h : A.toLinearMap.comp i = (P.sourceRaw τ).toLinearMap.comp i := by
    apply (galerkinSpaceBasis P.hΩ N).ext
    intro j
    simpa only [A, i, u, du, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      Submodule.subtype_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, reverseTimeSpatialFormOperator_apply, galerkinReconstructCLM_apply,
      ReverseTimeGalerkinProblem.sourceRaw, reverseTimeGalerkinSource] using galerkinRate_row P N τ x j
  simpa only [A, i, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, Submodule.subtype_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    reverseTimeSpatialFormOperator_apply, ReverseTimeGalerkinProblem.form] using LinearMap.congr_fun h v

end HypoellipticAleksandrov.Parabolic.Dirichlet
