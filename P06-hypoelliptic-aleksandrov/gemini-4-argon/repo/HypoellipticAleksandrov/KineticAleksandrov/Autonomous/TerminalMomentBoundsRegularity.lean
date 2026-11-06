module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FourthMomentsPolynomials
import Mathlib.Tactic

/-! # Regularity of the concrete polynomial supersolutions in evolution coordinates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic

/- Raw coordinate smoothness of the quadratic velocity barrier. -/
theorem terminal_raw_continuous (W : Point → ℝ)
    (hW : ContDiff ℝ (⊤ : ℕ∞) (rawLift W)) : Continuous W := by
  exact hW.continuous.comp (KineticPoint.homeomorphProd 1).continuous_toFun

/- Raw smoothness supplies all comparison slices. -/
theorem terminal_raw_regular (W : Point → ℝ)
    (hW : ContDiff ℝ (⊤ : ℕ∞) (rawLift W)) (p : Point) : IsSliceRegularAt W p := by
  apply IsSliceRegularAt.of_contDiffAt
  exact (hW.of_le (by norm_num)).contDiffAt

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
