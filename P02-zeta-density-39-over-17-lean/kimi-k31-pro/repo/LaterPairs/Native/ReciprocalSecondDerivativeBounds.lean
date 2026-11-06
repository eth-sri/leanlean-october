module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import MathCollab.Density.Stronger.Atkinson.ReciprocalSecondDerivativeBounds
public import TaoTrudgianYang2025.BProcessBaseline

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace TaoTrudgianYang2025

theorem iteratedDeriv_two_real_inv {g : ℝ → ℝ} {x : ℝ}
    (hg : ContDiffAt ℝ 2 g x) (hne : g x ≠ 0) :
    iteratedDeriv 2 (fun y => (g y)⁻¹) x =
      2 * (deriv g x) ^ 2 / (g x) ^ 3 - iteratedDeriv 2 g x / (g x) ^ 2 :=
  MathCollab.Density.Stronger.Atkinson.iteratedDeriv_two_real_inv hg hne

end TaoTrudgianYang2025
