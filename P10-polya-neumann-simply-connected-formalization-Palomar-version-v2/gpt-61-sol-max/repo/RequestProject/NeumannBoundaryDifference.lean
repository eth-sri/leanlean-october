module

public import RequestProject.NeumannBoundaryPole
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

/-!
# Energy comparison for the genuine Neumann boundary maps

The inverse difference identity is applied to the actual weak Helmholtz
form `B_E = I - (E + 1) J†J`. Compactness of `J†J` then proves compactness
of the differences of the actual H¹ solution maps and L² NtD maps.
At energy `-1` the form is the identity, so this reference energy requires
no nonnegative-energy or nonresonance assumption.

These are identities for the genuine ordinary-`dθ` boundary maps. They do
not assert a fractional trace estimate or a conformal principal symbol.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Set
open scoped InnerProductSpace

/-- At the coercive reference energy `-1`, the genuine weak form is exactly
the shifted H¹ inner product. -/
private theorem shifted_form_neg_one
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (M : X →L[ℂ] X) :
    1 - (((-1 : ℝ) + 1 : ℝ) : ℂ) • M = 1 := by
  simp

@[simp] theorem h1HelmholtzForm_neg_one (Ω : Set ℂ) :
    h1HelmholtzForm Ω (-1) = 1 :=
  shifted_form_neg_one (h1MassOperator Ω)

@[simp] theorem h1HelmholtzResolvent_neg_one (Ω : Set ℂ) :
    h1HelmholtzResolvent Ω (-1) = 1 := by
  rw [h1HelmholtzResolvent, h1HelmholtzForm_neg_one, Ring.inverse_one]

@[simp] theorem neumannBoundaryPoisson_neg_one {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) :
    neumannBoundaryPoisson hb hL hγ (-1) = h1BoundaryLoad hb hL hγ := by
  apply ContinuousLinearMap.ext
  intro g
  simp only [neumannBoundaryPoisson, h1HelmholtzResolvent_neg_one,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]

@[simp] theorem neumannToDirichletL2_neg_one {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) :
    neumannToDirichletL2 hb hL hγ (-1) =
      (h1BoundaryTrace hb hL hγ).comp (h1BoundaryLoad hb hL hγ) := by
  rw [neumannToDirichletL2, neumannBoundaryPoisson_neg_one]

end PolyaNeumann

end
