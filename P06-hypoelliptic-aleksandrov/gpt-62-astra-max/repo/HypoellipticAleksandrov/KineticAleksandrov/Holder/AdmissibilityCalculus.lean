module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Admissibility
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonConstant
import Mathlib.Analysis.Calculus.Deriv.Mul
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonLinear
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
import Mathlib.Tactic

/-! # Smooth source tests and affine backward-operator identities -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set Parabolic

variable {d : ℕ} (A : FullKineticCoefficient d) {psi : KineticPoint d → ℝ}
    {E : Set (KineticPoint d)} (h : IsSmoothNear psi E) (hpsi : IsSmoothNear psi E)
    {P : KineticPoint d} (hP : P ∈ E) (a b : ℝ)

include h in
/-- Positive rescaling and constant shifting preserve source-near smoothness. -/
theorem IsSmoothNear.affine :
    IsSmoothNear (fun P => a * psi P + b) E := by
  obtain ⟨U, hU, hEU, hpsi⟩ := h
  exact ⟨U, hU, hEU, contDiffOn_const.mul hpsi |>.add contDiffOn_const⟩

include h hP in
/-- Near smoothness gives smoothness of each physical coordinate slice. -/
theorem IsSmoothNear.slices :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun t => psi ⟨t, P.position, P.velocity⟩) P.time ∧
    ContDiffAt ℝ (⊤ : ℕ∞) (fun x => psi ⟨P.time, x, P.velocity⟩) P.position ∧
    ContDiffAt ℝ (⊤ : ℕ∞) (fun v => psi ⟨P.time, P.position, v⟩) P.velocity := by
  obtain ⟨U, hU, hEU, hpsi⟩ := h
  have hg := hpsi.contDiffAt (((KineticPoint.homeomorphProd d).isOpenMap _ hU).mem_nhds (mem_image_of_mem _ (hEU hP)))
  have hv : ContDiff ℝ (⊤ : ℕ∞)
      (fun v : PDE.Vec d => (P.time, (P.position, v))) :=
    contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
  have htime := hg.comp P.time (contDiff_id.prodMk contDiff_const).contDiffAt
  have hposition := hg.comp P.position (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const)).contDiffAt
  have hvelocity := hg.comp P.velocity hv.contDiffAt
  exact ⟨htime, hposition, hvelocity⟩

include hpsi hP in
/-- The source backward operator is affine-linear on every smooth-near test. -/
theorem backwardOperator_affine :
    backwardOperator A (fun Q => a * psi Q + b) P = a * backwardOperator A psi P := by
  obtain ⟨ht, hx, hv⟩ := hpsi.slices hP
  have htd := ht.differentiableAt (by simp)
  have hxd := hx.differentiableAt (by simp)
  have hv2 := hv.of_le (show (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)
  have hf := comparison_const_formulas b P
  rw [backwardOperator_apply]
  rw [comparison_time_add (htd.const_mul a) (differentiableAt_const b),
    show kineticTimeDerivative (fun Q => a * psi Q) P =
      a * kineticTimeDerivative psi P from deriv_const_mul a htd, hf.1]
  rw [show kineticPositionGradient (fun Q => a * psi Q + b) P =
      a • kineticPositionGradient psi P + 0 by
    rw [show kineticPositionGradient (fun Q => a * psi Q + b) P =
        kineticPositionGradient (fun Q => a * psi Q) P +
          kineticPositionGradient (fun _ => b) P from
      classicalGradient_add ((differentiableAt_const a).mul hxd) (differentiableAt_const b)]
    rw [show kineticPositionGradient (fun Q => a * psi Q) P =
      a • kineticPositionGradient psi P from classicalGradient_const_mul a hxd, hf.2.1]]
  rw [comparison_hessian_add (contDiffAt_const.mul hv2) contDiffAt_const,
    hf.2.2.2, kineticVelocityHessian_eq_sliceHessian,
    sliceHessian_const_mul a hv2]
  simp only [add_zero, matrixContraction_smul_right, backwardOperator_apply,
    kineticVelocityHessian_eq_sliceHessian]
  unfold PDE.vecDot
  simp only [Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm (P.velocity _) a]
  rw [← Finset.mul_sum]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Holder
