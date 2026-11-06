module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.RetentionCurve
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MinorantScaling
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonRadial
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierGeometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped Topology MatrixOrder

/-- The stationary scalar retention barrier gives the normalized mass-floor rate. -/
theorem minorant_scalar_barrier_floor {d N : ℕ} (hN : 3 ≤ N)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hc : 0 < barrierC d N lam Lam) (B : CoefficientField d)
    (hB : IsSectionTwoCoefficient lam Lam B)
    (F : BoundedBorel (PDE.Vec d)) (V : TimeVelocity d → ℝ)
    (hV : ParabolicProbe.IsClassicalScalarTerminalSolution (PDE.euclideanBall 0 4)
      stationary (zIndependentCoefficient B) 0 F V)
    (hF : ∀ y, barrier N 3 y ≤ F y) :
    Real.exp (-(2 * N * d * Lam) / 9) ≤ V (-1, 0) := by
  let r : Fin (0 + 2) → ℝ := ![-1, 0]
  have hr : StrictMono r := by
    intro i j hij
    have hijv : i.val < j.val := hij
    have hi : i = 0 := by apply Fin.ext; change i.val = 0; omega
    have hj : j = 1 := by apply Fin.ext; change j.val = 1; omega
    subst i j
    norm_num [r]
  have hpieces : ∀ i : Fin (0 + 1), ContDiffOn ℝ 1
      (stationary : ℝ → PDE.Vec d) (Icc (r i.castSucc) (r i.succ)) :=
    fun _ => contDiffOn_const
  have hspd : HasCurveSpeedOn 0 (stationary : ℝ → PDE.Vec d) (r 0)
      (r (Fin.last (0 + 1))) := by
    intro t _ _
    change PDE.vecEuclideanNorm (deriv (fun _ : ℝ => (0 : PDE.Vec d)) t) ≤ 0
    rw [deriv_const]
    simp [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot]
  have h := comparison_at_center hN lam Lam 3 0 4 (by norm_num) (by norm_num)
    hlam hlamLam hc B hB stationary continuous_const 0 r hr hpieces hspd F V hV
    (by simpa only [stationary, sub_zero] using hF)
  change Real.exp (-barrierRate d N lam Lam 3 0 * (0 - (-1))) ≤ V (-1, 0) at h
  norm_num [barrierRate, neg_div] at h ⊢
  exact h

end HypoellipticAleksandrov.KineticAleksandrov.Decay
