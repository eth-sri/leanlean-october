module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftCalculus
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.BarrierFunctionSpaceLinear
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic

/-! # Operator homogeneity for propagating the positive sphere bound -/

@[expose] public section
noncomputable section
open Set Filter Topology
namespace HypoellipticAleksandrov.KineticAleksandrov

/- Equality on a neighborhood identifies the complete Bellman expression. -/
theorem bellman_operator_germ_eq {phi psi : (ℝ × ℝ) → ℝ} {q : ℝ × ℝ}
    (h : phi =ᶠ[𝓝 q] psi) (b : ℝ) : bellmanOperator b phi q = bellmanOperator b psi q := by
  have hv : bellmanDv phi =ᶠ[𝓝 q] bellmanDv psi :=
    (h.fderiv (𝕜 := ℝ)).mono (fun x hx => congrArg (fun L => L (0, 1)) hx)
  unfold bellmanOperator bellmanDx bellmanDvv
  rw [h.fderiv_eq, hv.fderiv_eq]

/- Constant multiplication scales the complete Bellman expression. -/
theorem bellman_operator_mul (c b : ℝ) (phi : (ℝ × ℝ) → ℝ) (q : ℝ × ℝ) :
    bellmanOperator b (fun z => c * phi z) q = c * bellmanOperator b phi q := by
  change bellmanOperator b (c • phi) q = _
  rw [bellmanOperator, bellmanDx, fderiv_const_smul_field, bellmanDvv_smul]
  simp only [Pi.smul_apply, smul_apply, smul_eq_mul, bellmanOperator, bellmanDx]
  ring

/- The Bellman operator has degree alpha minus two on a C² homogeneous function. -/
end HypoellipticAleksandrov.KineticAleksandrov
