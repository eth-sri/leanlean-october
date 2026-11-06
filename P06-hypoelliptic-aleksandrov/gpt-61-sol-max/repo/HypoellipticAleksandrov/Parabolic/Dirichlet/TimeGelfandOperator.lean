module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTimeDerivative

/-!
# Bounded spatial operators on Gelfand weak time derivatives

This module transports a reverse-time Gelfand weak derivative through a bounded
spatial operator whose action is symmetric for the scalar `L²` pivot.  The
dual action is Banach-dual precomposition, not a Hilbert adjoint.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- Precompose an `H10` dual functional with a bounded spatial operator. -/
def h10HilbertGraphDualPrecompose
    {d : ℕ} {Ω : PDE.VelocityRegion d}
    (hΩ : IsOpen Ω)
    (S : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ) :
    H10HilbertGraphDual hΩ →L[ℝ] H10HilbertGraphDual hΩ :=
  (ContinuousLinearMap.compL ℝ (H10HilbertGraph hΩ) (H10HilbertGraph hΩ) ℝ).flip S

variable {d : ℕ} {Ω : PDE.VelocityRegion d}

section
variable (hΩ : IsOpen Ω)



variable (T : ℝ)

variable (S : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ)

private theorem ae_reverseTimeValueCLM_compLpL_apply



    (u : ReverseTimeL2V hΩ T) :
    reverseTimeValueCLM hΩ T
        (S.compLpL (2 ) (reverseTimeVolume T) u) =ᵐ[reverseTimeVolume T]
      fun τ => valueCLM hΩ (S (u τ)) := by
  filter_upwards [
    coeFn_reverseTimeValueCLM hΩ T
      (S.compLpL (2 ) (reverseTimeVolume T) u),
    ContinuousLinearMap.coeFn_compLpL S u
  ] with τ hvalue hS
  rw [hvalue, hS]

private theorem ae_h10HilbertGraphDualPrecompose_compLpL_apply



    (g : ReverseTimeL2VStar hΩ T) :
    (h10HilbertGraphDualPrecompose hΩ S).compLpL
        (2 ) (reverseTimeVolume T) g =ᵐ[reverseTimeVolume T]
      fun τ => h10HilbertGraphDualPrecompose hΩ S (g τ) :=
  ContinuousLinearMap.coeFn_compLpL (h10HilbertGraphDualPrecompose hΩ S) g

private theorem ae_pivot_symmetric_left_pairing


    (u : ReverseTimeL2V hΩ T)
    (S : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ)
    (hS : ∀ x y : H10HilbertGraph hΩ,
      inner ℝ (valueCLM hΩ x) (valueCLM hΩ (S y)) =
        inner ℝ (valueCLM hΩ (S x)) (valueCLM hΩ y))
    (v : H10HilbertGraph hΩ) (eta : ReverseTimeScalarTest T) :
    (fun τ =>
      inner ℝ (valueCLM hΩ v)
        (reverseTimeValueCLM hΩ T
          (S.compLpL (2 ) (reverseTimeVolume T) u) τ) * eta.deriv τ) =ᵐ[
        reverseTimeVolume T]
      fun τ => inner ℝ (valueCLM hΩ (S v))
        (reverseTimeValueCLM hΩ T u τ) * eta.deriv τ := by
  filter_upwards [
    ae_reverseTimeValueCLM_compLpL_apply hΩ T S u,
    coeFn_reverseTimeValueCLM hΩ T u
  ] with τ hSu hu
  rw [hSu, hu, hS]

private theorem ae_pivot_symmetric_right_pairing


    (g : ReverseTimeL2VStar hΩ T)
    (S : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ)
    (v : H10HilbertGraph hΩ) (eta : ReverseTimeScalarTest T) :
    (fun τ =>
      ((h10HilbertGraphDualPrecompose hΩ S).compLpL
        (2 ) (reverseTimeVolume T) g τ) v * eta τ) =ᵐ[
        reverseTimeVolume T]
      fun τ => (g τ) (S v) * eta τ := by
  filter_upwards [ae_h10HilbertGraphDualPrecompose_compLpL_apply hΩ T S g] with τ hg
  rw [hg]
  rfl
end


/-- A Gelfand weak derivative is preserved by a bounded spatial operator that
is symmetric for the scalar `L²` pivot. -/
theorem HasGelfandWeakTimeDerivative.comp_of_pivot_symmetric

    {hΩ : IsOpen Ω} {T : ℝ} {hT : 0 < T}
    {u : ReverseTimeL2V hΩ T} {g : ReverseTimeL2VStar hΩ T}
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (S : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ)
    (hS : ∀ x y : H10HilbertGraph hΩ,
      inner ℝ (valueCLM hΩ x) (valueCLM hΩ (S y)) =
        inner ℝ (valueCLM hΩ (S x)) (valueCLM hΩ y)) :
    HasGelfandWeakTimeDerivative hΩ T hT
      (S.compLpL (2 ) (reverseTimeVolume T) u)
      ((h10HilbertGraphDualPrecompose hΩ S).compLpL
        (2 ) (reverseTimeVolume T) g) := (fun v eta =>
  And.casesOn (hderiv (S v) eta) fun hleft right =>
    And.casesOn right fun hright hidentity =>
      ⟨Integrable.congr hleft (EventuallyEq.symm (ae_pivot_symmetric_left_pairing hΩ T u S hS v eta)),
        ⟨Integrable.congr hright (EventuallyEq.symm (ae_pivot_symmetric_right_pairing hΩ T g S v eta)),
          Trans.trans (Trans.trans (integral_congr_ae (ae_pivot_symmetric_left_pairing hΩ T u S hS v eta)) hidentity)
            (congrArg Neg.neg (Eq.symm (integral_congr_ae (ae_pivot_symmetric_right_pairing hΩ T g S v eta))))⟩⟩)

end HypoellipticAleksandrov.Parabolic.Dirichlet
