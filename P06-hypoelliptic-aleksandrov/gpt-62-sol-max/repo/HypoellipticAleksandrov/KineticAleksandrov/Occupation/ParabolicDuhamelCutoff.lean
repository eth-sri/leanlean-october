module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.WeakCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelJets

/-!
# Time cutoffs and the transported adjoint

For a smooth function `χ` of the time coordinate alone,
`Lop^*(χ(σ) ψ) = χ(σ) Lop^* ψ - χ'(σ) ψ`, and `Lop^* ψ` vanishes off the topological support of
`ψ`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set Filter
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.Evolution
open scoped Topology

variable {d : ℕ}

/-- Product rule for a time cutoff. -/
theorem fderiv_cutoff_mul {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) {f : EvolutionVec d → ℝ}
    {x : EvolutionVec d} (hf : DifferentiableAt ℝ f x) (v : EvolutionVec d) :
    fderiv ℝ (fun y => χ (Evolution.timeCoord d y) * f y) x v =
      χ (Evolution.timeCoord d x) * fderiv ℝ f x v +
        deriv χ (Evolution.timeCoord d x) * Evolution.timeCoord d v * f x := by
  have hc : HasFDerivAt (fun y => χ (Evolution.timeCoord d y))
      (deriv χ (Evolution.timeCoord d x) • Evolution.timeCoord d) x :=
    (hχ _).hasDerivAt.comp_hasFDerivAt x (Evolution.timeCoord d).hasFDerivAt
  rw [(hc.fun_mul hf.hasFDerivAt).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The cutoff commutation formula for the transported adjoint. -/
theorem transportedAdjoint_cutoff_mul {B : FullKineticCoefficient d} {b : PDE.Vec d → PDE.Vec d}
    (hB : IsSmoothFullKineticCoefficient B) {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (x : EvolutionVec d) :
    transportedAdjoint B b (fun y => χ (Evolution.timeCoord d y) * ψ y) x =
      χ (Evolution.timeCoord d x) * transportedAdjoint B b ψ x -
        deriv χ (Evolution.timeCoord d x) * ψ x := by
  have hχd := hχ.differentiable (by simp)
  let c (i j : Fin d) (w : EvolutionVec d) :=
    B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j
  have hcut (v : EvolutionVec d) (hv : Evolution.timeCoord d v = 0)
      {φ : EvolutionVec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (y : EvolutionVec d) :
      fderiv ℝ (fun w => χ (Evolution.timeCoord d w) * φ w) y v =
        χ (Evolution.timeCoord d y) * fderiv ℝ φ y v := by
    rw [fderiv_cutoff_mul hχd (differentiableAt_of_contDiff hφ y), hv, mul_zero, zero_mul, add_zero]
  have hV (i j : Fin d) :
      fderiv ℝ (fun y => fderiv ℝ (fun w => c i j w * (χ (Evolution.timeCoord d w) * ψ w))
        y (basisV j)) x (basisV i) =
      χ (Evolution.timeCoord d x) * fderiv ℝ (fun y =>
        fderiv ℝ (fun w => c i j w * ψ w) y (basisV j)) x (basisV i) := by
    have he : (fun w => c i j w * (χ (Evolution.timeCoord d w) * ψ w)) =
        fun w => χ (Evolution.timeCoord d w) * (c i j w * ψ w) := by
      funext w; ring
    have hs : ContDiff ℝ (⊤ : ℕ∞) (fun w => c i j w * ψ w) :=
      (contDiff_coeffAt_entry hB i j).mul hψ
    rw [he]
    simp_rw [hcut (basisV j) (timeCoord_basisV j) hs]
    exact hcut (basisV i) (timeCoord_basisV i) (contDiff_fderiv_apply hs _) x
  simp only [c] at hV
  unfold transportedAdjoint
  simp only [hV, fun l => hcut (basisZ l) (timeCoord_basisZ l) hψ x,
    fderiv_cutoff_mul hχd (differentiableAt_of_contDiff hψ x) basisT, timeCoord_basisT]
  simp only [mul_left_comm _ (χ (Evolution.timeCoord d x)), ← Finset.mul_sum]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
