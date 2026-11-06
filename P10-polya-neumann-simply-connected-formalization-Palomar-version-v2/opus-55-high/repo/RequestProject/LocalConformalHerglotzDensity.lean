module

public import RequestProject.LocalConformalRegularObservation
public import RequestProject.Reconstruction

set_option linter.privateModule false

/-!
# Actual Herglotz conormal span and the remaining density obligation

The compatibility space below is the orthogonal complement of the
actual normalized traces of the original Neumann resonant space. Every
actual Herglotz conormal belongs to it, and so does their closed span.
The exact full-density assertion is equivalent to the reverse Cauchy
annihilator statement: every normalized vector annihilating all actual
Herglotz conormals must lie in the closure of that resonant trace range.

The repository's genuine Cauchy reconstruction theorem applies to
`compatibleTraces`, whose definition explicitly requires a Lipschitz
representative and periodic endpoints. It gives an injective map into
the original Neumann eigenspace. It does not identify all H1/2
annihilators, and its stated conclusion does not identify the general
reconstructed trace with the supplied trace. Thus no full H-minus-1/2
Herglotz density theorem is asserted in this file. In particular the
reverse implication isolated below remains a mathematical obligation,
not a premise silently added to the original Main theorem.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric MeasureTheory
open scoped Real InnerProductSpace ComplexConjugate

section SuppliedCoordinates

variable {R C : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))

local notation "ΩF" => F '' ball (0 : ℂ) 1
local notation "QF" => localConformalDiskHalfTrace hR F hFs hL

end SuppliedCoordinates

end PolyaNeumann

end
