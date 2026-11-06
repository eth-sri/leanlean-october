module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.Retention
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MinorantScaling
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonRadial
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierGeometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.KineticAleksandrov.Decay.RetentionCurve

open private HypoellipticAleksandrov.KineticAleksandrov.Decay.comparison_at_center from HypoellipticAleksandrov.KineticAleksandrov.Decay.RetentionCurve
open private HypoellipticAleksandrov.KineticAleksandrov.Decay.scalar_difference_operator from HypoellipticAleksandrov.KineticAleksandrov.Decay.RetentionCurve
open private HypoellipticAleksandrov.KineticAleksandrov.Decay.hessian_translate from HypoellipticAleksandrov.KineticAleksandrov.Decay.RetentionCurve
open private HypoellipticAleksandrov.KineticAleksandrov.Decay.lifted_difference_subsolution from HypoellipticAleksandrov.KineticAleksandrov.Decay.RetentionCurve
open private HypoellipticAleksandrov.KineticAleksandrov.Decay.gradient_translate from HypoellipticAleksandrov.KineticAleksandrov.Decay.RetentionCurve
open private HypoellipticAleksandrov.KineticAleksandrov.Decay.lifted_operator from HypoellipticAleksandrov.KineticAleksandrov.Decay.RetentionCurve
section
open private HypoellipticAleksandrov.KineticAleksandrov.Decay.movingBarrier_time_derivative from HypoellipticAleksandrov.KineticAleksandrov.Decay.RetentionCurve
private alias _sharedProof_202_0 := HypoellipticAleksandrov.KineticAleksandrov.Decay.movingBarrier_time_derivative
end
section
open private HypoellipticAleksandrov.KineticAleksandrov.Decay.movingBarrier_subsolution from HypoellipticAleksandrov.KineticAleksandrov.Decay.RetentionCurve
private alias _sharedProof_37_0 := HypoellipticAleksandrov.KineticAleksandrov.Decay.movingBarrier_subsolution
end
section
open private HypoellipticAleksandrov.KineticAleksandrov.Decay.movingBarrier_hessian from HypoellipticAleksandrov.KineticAleksandrov.Decay.RetentionCurve
private alias _sharedProof_203_0 := HypoellipticAleksandrov.KineticAleksandrov.Decay.movingBarrier_hessian
end


/-!
# Scalar polynomial comparison for the minorant mass floor

The retention barrier is compared directly to the supplied scalar solution.
This avoids assuming existence of a separate normalized joint evolution.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped MatrixOrder

variable {d : ℕ}









section
variable {d N : ℕ} (hN : 3 ≤ N)

include hN









end












variable {d N : ℕ} (hN : 3 ≤ N)





include hN in
/-- The stationary scalar retention barrier gives the normalized mass-floor rate. -/
theorem minorant_scalar_barrier_floor
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hc : 0 < barrierC d N lam Lam) (B : CoefficientField d)
    (hB : IsSectionTwoCoefficient lam Lam B)
    (F : BoundedBorel (PDE.Vec d)) (V : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hV : ParabolicProbe.IsClassicalScalarTerminalSolution (PDE.euclideanBall 0 4)
      stationary (zIndependentCoefficient B) 0 F V)
    (hF : ∀ y, barrier N 3 y ≤ F y) :
    Real.exp (-(2 * N * d * Lam) / 9) ≤ V (-1, 0) := by
  let r : Fin (0 + 2) → ℝ := ![-1, 0]



  have h := _root_.HypoellipticAleksandrov.KineticAleksandrov.Decay.comparison_at_center hN lam Lam 3 0 4 (by norm_num) (by norm_num)
    hlam hlamLam hc B hB stationary continuous_const 0 r (by
        intro i j hij
        have hijv  := hij
        have hi : i = 0 := by apply Fin.ext; change i.val = 0; omega
        have hj : j = 1 := by apply Fin.ext; change j.val = 1; omega
        subst i j
        norm_num [r]) (fun _ => contDiffOn_const) (by
        intro t _ _
        change PDE.vecEuclideanNorm (deriv (fun _ : ℝ => (0 : PDE.Vec d)) t) ≤ 0
        rw [deriv_const]
        simp [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot]) F V hV
    (by simpa only [stationary, sub_zero] using hF)
  change Real.exp (-barrierRate d N lam Lam 3 0 * (0 - (-1))) ≤ V (-1, 0) at h
  norm_num [barrierRate, neg_div] at h ⊢
  exact h

end HypoellipticAleksandrov.KineticAleksandrov.Decay
