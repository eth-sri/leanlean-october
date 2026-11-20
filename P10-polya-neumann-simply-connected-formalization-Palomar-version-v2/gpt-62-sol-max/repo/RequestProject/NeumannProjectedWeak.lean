module

public import RequestProject.NeumannNormalizedBoundary

/-!
# The actual weak equation for the projected Neumann resolvent

The fixed complement is invariant under the genuine mass and Helmholtz
operators. Consequently the regular resolvent solves the actual form
equation with exactly the resonant component of the load removed. The
removed component has its genuine physical mass pairing, with the factor
`E₀ + 1` from the shifted-energy H¹ inner product.

These identities use the actual variational resonance space and do not
assume any boundary principal-part or smoothing formula.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set
open scoped Real InnerProductSpace ComplexConjugate

/-- Actual resonant vectors satisfy the zero-load weak Neumann equation
against every genuine H¹ test vector. -/
theorem h1Resonant_weak_pairing {Ω : Set ℂ} {E₀ : ℝ}
    {w : NeumannH1 Ω} (hw : w ∈ h1ResonantSpace Ω E₀) (v : NeumannH1 Ω) :
    (∑ i, ⟪h1Gradient Ω i v, h1Gradient Ω i w⟫_ℂ) =
      (E₀ : ℂ) * ⟪h1Value Ω v, h1Value Ω w⟫_ℂ := by
  have hzero : h1HelmholtzForm Ω E₀ w = 0 := hw
  have h := h1HelmholtzForm_inner Ω E₀ v w
  rw [hzero, inner_zero_right] at h
  exact sub_eq_zero.mp h.symm

/-- The shifted H¹ pairing of an actual resonant vector is its physical
mass pairing multiplied by `E₀ + 1`. -/
theorem h1Resonant_inner_eq_mass {Ω : Set ℂ} {E₀ : ℝ}
    {w : NeumannH1 Ω} (hw : w ∈ h1ResonantSpace Ω E₀) (v : NeumannH1 Ω) :
    ⟪v, w⟫_ℂ = ((E₀ + 1 : ℝ) : ℂ) * ⟪h1Value Ω v, h1Value Ω w⟫_ℂ := by
  rw [h1_inner, h1Resonant_weak_pairing hw v]
  push_cast
  ring

/-- The all-test-vector weak equation for the genuine regular resolvent.
The removed resonant load contributes with a minus sign and the actual
shifted-energy factor `E₀ + 1`. -/
theorem h1RegularResolvent_weak_pairing {Ω : Set ℂ} {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {E : ℝ} (hunit : IsUnit (h1ComplementForm Ω E₀ E)) (x : NeumannH1 Ω) :
    ∀ v : NeumannH1 Ω,
      (∑ i, ⟪h1Gradient Ω i v,
        h1Gradient Ω i (h1RegularResolvent Ω E₀ E x)⟫_ℂ) -
          (E : ℂ) * ⟪h1Value Ω v,
            h1Value Ω (h1RegularResolvent Ω E₀ E x)⟫_ℂ =
        ⟪v, x⟫_ℂ - ((E₀ + 1 : ℝ) : ℂ) *
          ⟪h1Value Ω v, h1Value Ω ((h1ResonantSpace Ω E₀).starProjection x)⟫_ℂ := by
  intro v
  rw [← h1HelmholtzForm_inner, h1RegularResolvent_projected_solve hE₀ hunit,
    Submodule.starProjection_orthogonal_val, inner_sub_right,
    h1Resonant_inner_eq_mass (Submodule.starProjection_apply_mem _ _)]

/-- The actual regular solution with normalized boundary load `Q† b`
satisfies the projected weak Neumann equation against every H¹ vector. -/
theorem h1RegularResolvent_adjoint_weak_pairing {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {E : ℝ} (hunit : IsUnit (h1ComplementForm Ω E₀ E)) (b : L2Z) :
    ∀ v : NeumannH1 Ω,
      (∑ i, ⟪h1Gradient Ω i v,
        h1Gradient Ω i (h1RegularResolvent Ω E₀ E (ContinuousLinearMap.adjoint Q b))⟫_ℂ) -
          (E : ℂ) * ⟪h1Value Ω v,
            h1Value Ω (h1RegularResolvent Ω E₀ E (ContinuousLinearMap.adjoint Q b))⟫_ℂ =
        ⟪Q v, b⟫_ℂ - ((E₀ + 1 : ℝ) : ℂ) *
          ⟪h1Value Ω v, h1Value Ω ((h1ResonantSpace Ω E₀).starProjection
            (ContinuousLinearMap.adjoint Q b))⟫_ℂ := by
  intro v
  rw [h1RegularResolvent_weak_pairing hE₀ hunit, ContinuousLinearMap.adjoint_inner_right]

end PolyaNeumann

end
