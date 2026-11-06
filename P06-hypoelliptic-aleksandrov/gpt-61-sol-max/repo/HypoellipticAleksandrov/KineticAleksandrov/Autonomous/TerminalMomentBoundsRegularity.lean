module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FourthMomentsPolynomials
import Mathlib.Tactic
public import PDEFoundation.Calculus.RegularityOrder


/-! # Regularity of the concrete polynomial supersolutions in evolution coordinates -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous


/-- Raw coordinate smoothness of the quadratic velocity barrier. -/
theorem velocitySecondBarrier_raw_smooth (Lam v0 tau : ℝ) :
    ContDiff ℝ PDE.smoothOrder (rawLift (velocitySecondBarrier Lam v0 tau ∘ terminalPhysicalPoint)) := by
  change ContDiff ℝ PDE.smoothOrder (fun q : ℝ × (PDE.Vec 1 × PDE.Vec 1) =>
    (q.2.1 0-v0)^2+2*Lam*(tau-q.1))
  fun_prop

/-- Raw coordinate smoothness of the quadratic position barrier. -/
theorem positionSecondBarrier_raw_smooth (Lam X0 tau : ℝ) :
    ContDiff ℝ PDE.smoothOrder (rawLift (positionSecondBarrier Lam X0 tau ∘ terminalPhysicalPoint)) := by
  change ContDiff ℝ PDE.smoothOrder (fun q : ℝ × (PDE.Vec 1 × PDE.Vec 1) =>
    (q.2.2 0-X0+(tau-q.1)*q.2.1 0)^2+(2/3:ℝ)*Lam*(tau-q.1)^3)
  fun_prop

variable (W : Point → ℝ) (hW : ContDiff ℝ PDE.smoothOrder (rawLift W))

include hW
/-- Raw smoothness supplies global continuity on the native point carrier. -/
theorem terminal_raw_continuous  : Continuous W := hW.continuous.comp (KineticPoint.homeomorphProd 1).continuous_toFun

/-- Raw smoothness supplies all comparison slices. -/
theorem terminal_raw_regular  (p : Point) : IsSliceRegularAt W p := by
  apply IsSliceRegularAt.of_contDiffAt
  exact (hW.of_le (by norm_num)).contDiffAt

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
