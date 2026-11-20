module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10ShiftedPositivePart

/-! # Unshifted positive parts in spatial `H¹₀` -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : Set (PDE.Vec d)}

private theorem shiftedPositivePartValue_zero (f : PDE.ScalarLp Ω 2) :
    shiftedPositivePartValue 0 f = Lp.posPart f := by
  apply Lp.ext
  filter_upwards [coeFn_shiftedPositivePartValue 0 f, Lp.coeFn_posPart f] with x hx hy
  simpa only [NNReal.coe_zero, sub_zero, hy] using hx

section
variable (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ)
include u

/-- The canonical positive part in the Hilbert realization of spatial `H¹₀`. -/
noncomputable def h10PositivePart : H10HilbertGraph hΩ :=
  h10ShiftedPositivePart hΩ u 0

/-- The value component of the canonical `H¹₀` positive part is the
`L²` positive part of the original value component. -/
@[simp]
theorem valueCLM_h10PositivePart :
    valueCLM hΩ (h10PositivePart hΩ u) =
      MeasureTheory.Lp.posPart (valueCLM hΩ u) :=
  (valueCLM_h10ShiftedPositivePart hΩ u 0).trans (shiftedPositivePartValue_zero _)

/-- The weak gradient of the positive part is the original gradient on its
strictly positive set and zero elsewhere. -/
theorem gradientCLM_h10PositivePart :
    ∀ᵐ x ∂(PDE.volumeOn Ω),
      gradientCLM hΩ (h10PositivePart hΩ u) x =
        {y | 0 < valueCLM hΩ u y}.indicator (gradientCLM hΩ u) x := by
  simpa only [h10PositivePart, NNReal.coe_zero] using gradientCLM_h10ShiftedPositivePart hΩ u 0

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
