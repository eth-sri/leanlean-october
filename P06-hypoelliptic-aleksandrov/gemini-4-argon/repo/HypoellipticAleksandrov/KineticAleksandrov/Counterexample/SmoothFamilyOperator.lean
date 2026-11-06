module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SmoothFamilyError
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifySource
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! # Positive sources under a fixed-function change of autonomous coefficients -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory HypoellipticAleksandrov.Parabolic
open scoped ENNReal Matrix.Norms.Elementwise

/- Entrywise measurable autonomous coefficients and genuine smooth jets
give a measurable operator. -/
theorem measurable_backwardOperator_of_joint_smooth {d }
    (A : XV d → PDE.Mat d) (hA : ∀ i k, Measurable (fun q => A q i k))
    (u : KineticPoint d → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × XV d =>
      u ((KineticPoint.equivProd d).symm q))) :
    Measurable (backwardOperator (fun _t x v => A (x, v)) u) := by
  have hr := isKineticC112On_univ_of_joint_smooth u hu
  have ht := (continuousOn_univ.mp hr.continuousOn_kineticTimeDerivative).measurable
  have hx := (continuousOn_univ.mp hr.continuousOn_kineticPositionGradient).measurable
  have hv i k : Measurable (fun P => kineticVelocityHessian u P i k) :=
    ((continuous_apply k).comp ((continuous_apply i).comp
      (continuousOn_univ.mp hr.continuousOn_kineticVelocityHessian))).measurable
  have hsp : Measurable (fun P : KineticPoint d => (P.position, P.velocity)) :=
    (continuous_position.prodMk continuous_velocity).measurable
  have hT : Measurable (fun P => PDE.vecDot P.velocity (kineticPositionGradient u P)) := by
    unfold PDE.vecDot
    exact Finset.measurable_sum _ (fun i _ =>
      ((measurable_pi_apply i).comp continuous_velocity.measurable).mul
        ((measurable_pi_apply i).comp hx))
  have hC : Measurable (fun P => matrixContraction (A (P.position, P.velocity))
      (kineticVelocityHessian u P)) := by
    unfold matrixContraction
    exact Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun k _ =>
      ((hA i k).comp hsp).mul
        (hv i k)))
  exact (ht.add hT).sub hC

/- The full backward-operator change is minus the exact coefficient Hessian error. -/
theorem backwardOperator_coefficient_change {d } (A B : XV d → PDE.Mat d)
    (u : KineticPoint d → ℝ) (P : KineticPoint d) :
    backwardOperator (fun _t x v => B (x, v)) u P =
      backwardOperator (fun _t x v => A (x, v)) u P -
        matrixContraction (B (P.position, P.velocity) - A (P.position, P.velocity))
          (kineticVelocityHessian u P) := by
  unfold backwardOperator fullKineticCoefficientAt matrixContraction
  simp only [Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
  ring

/- The positive source norm increases by at most the full contraction-error norm. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
