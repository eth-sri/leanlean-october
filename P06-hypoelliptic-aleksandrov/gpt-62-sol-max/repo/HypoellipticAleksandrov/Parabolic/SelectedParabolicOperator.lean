module

public import HypoellipticAleksandrov.Coefficients.Ellipticity
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily
public import HypoellipticAleksandrov.Parabolic.ParabolicLowOrderIndex

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily

open scoped BigOperators
open ParabolicDerivativeIndex

/-- The backward scalar operator evaluated on the selected parabolic jet. -/
noncomputable def backwardOperator {d L : ℕ} {U : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ} (D : ParabolicWeakDerivativeFamily d L U u) (h : 2 ≤ L)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ) (z : TimeVelocity d) : ℝ :=
  D.representative (castLE h (timeOne d)) z +
    (∑ i, ∑ j, a z.1 z.2 i j * D.representative (castLE h (velocityTwo j i)) z) +
    (∑ j, b z.1 z.2 j * D.representative (castLE h (velocityOne j)) z) +
    c z.1 z.2 * D.representative (castLE h (zeroTwo d)) z

end HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily
