module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftWindow
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftSmoothIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.BarrierFunctionSpace
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasure
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftCalculus

/-! # C² regularity of the actual homogeneous test lift -/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
namespace HypoellipticAleksandrov.KineticAleksandrov

/- The joint lift integrand on the ambient plane and positive real radius. -/
def bellmanLiftIntegrand (alpha : ℝ) (zeta : (ℝ × ℝ) → ℝ)
    (w : (ℝ × ℝ) × ℝ) : ℝ :=
  w.2 ^ (-1 - alpha) * zeta (bellmanPlaneDilation w.2 w.1)

/- The test gives joint regularity of the same order wherever the radius is positive. -/
theorem bellmanLiftIntegrand_contDiffOn_order (n : WithTop ℕ∞)
    (alpha : ℝ) (zeta ) (hz : ContDiff ℝ n zeta) :
    ContDiffOn ℝ n (bellmanLiftIntegrand alpha zeta) (univ ×ˢ Ioi 0) := by
  have hd : ContDiff ℝ n (fun w : (ℝ × ℝ) × ℝ => bellmanPlaneDilation w.2 w.1) := by
    exact ((contDiff_snd.pow 3).mul (contDiff_fst.fst)).prodMk
      (contDiff_snd.mul (contDiff_fst.snd))
  exact (contDiffOn_snd.rpow_const_of_ne (fun w hw => ne_of_gt hw.2)).mul
    (hz.comp hd).contDiffOn

/- The compact test gives joint C² regularity wherever the radial variable is positive. -/
end HypoellipticAleksandrov.KineticAleksandrov
