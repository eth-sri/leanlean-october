module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonConstant
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Mul
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonLinear
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder
open Set MeasureTheory Parabolic


/-- Smooth-near functions are continuous on the indicated set. -/
theorem IsSmoothNear.continuousOn {d : ℕ} {psi : KineticPoint d → ℝ}
    {E : Set (KineticPoint d)} (h : IsSmoothNear psi E) : ContinuousOn psi E := by
  obtain ⟨U, _, hEU, hpsi⟩ := h
  exact ((hpsi.continuousOn.comp (KineticPoint.homeomorphProd d).continuous.continuousOn (fun P hP => mem_image_of_mem _ hP)).mono hEU).congr (fun P _ =>
    congrArg psi ((KineticPoint.equivProd d).symm_apply_apply P))

/-- Restriction preserves source admissibility without changing the constants. -/
theorem IsAdmissibleSupersolution.mono {d : ℕ} {A : FullKineticCoefficient d}
    {O U : Set (KineticPoint d)} {p C_A : ℝ} {u : KineticPoint d → ℝ}
    (hu : IsAdmissibleSupersolution A O p C_A u) (hUO : U ⊆ O) :
    IsAdmissibleSupersolution A U p C_A u :=
  ⟨hu.1.mono hUO, fun P R hR hQU psi hpsi =>
    hu.2 P R hR (hQU.trans hUO) psi hpsi⟩

/-- Increasing the comparison constant preserves the source inequality. -/
theorem IsAdmissibleSupersolution.mono_constant {d : ℕ} {A : FullKineticCoefficient d}
    {O : Set (KineticPoint d)} {p C_A C_B : ℝ} {u : KineticPoint d → ℝ}
    (hu : IsAdmissibleSupersolution A O p C_A u) (hAB : C_A ≤ C_B) :
    IsAdmissibleSupersolution A O p C_B u := by
  refine ⟨hu.1, fun P R hR hQ psi hpsi => (hu.2 P R hR hQ psi hpsi).trans ?_⟩
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg hR.le _)) ENNReal.toReal_nonneg

/-- The source norm may use a nonnegative majorant even for signed comparison data. -/
theorem IsAdmissibleSupersolution.nonnegative_constant {d : ℕ}
    {A : FullKineticCoefficient d} {O : Set (KineticPoint d)} {p C_A : ℝ}
    {u : KineticPoint d → ℝ} (hu : IsAdmissibleSupersolution A O p C_A u) :
    IsAdmissibleSupersolution A O p (max C_A 0) u :=
  hu.mono_constant (le_max_left _ _)



/-- Positive rescaling and constant shifting preserve source-near smoothness. -/
theorem IsSmoothNear.affine {d : ℕ} {psi : KineticPoint d → ℝ}
    {E : Set (KineticPoint d)} (h : IsSmoothNear psi E) (a b : ℝ) :
    IsSmoothNear (fun P => a * psi P + b) E := by
  obtain ⟨U, hU, hEU, hpsi⟩ := h
  exact ⟨U, hU, hEU, contDiffOn_const.mul hpsi |>.add contDiffOn_const⟩

/-- Near smoothness gives smoothness of each physical coordinate slice. -/
theorem IsSmoothNear.slices {d : ℕ} {psi : KineticPoint d → ℝ}
    {E : Set (KineticPoint d)} (h : IsSmoothNear psi E) {P : KineticPoint d}
    (hP : P ∈ E) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun t => psi ⟨t, P.position, P.velocity⟩) P.time ∧
    ContDiffAt ℝ (⊤ : ℕ∞) (fun x => psi ⟨P.time, x, P.velocity⟩) P.position ∧
    ContDiffAt ℝ (⊤ : ℕ∞) (fun v => psi ⟨P.time, P.position, v⟩) P.velocity := by
  obtain ⟨U, hU, hEU, hpsi⟩ := h
  have hg := hpsi.contDiffAt (((KineticPoint.homeomorphProd d).isOpenMap _ hU).mem_nhds (mem_image_of_mem _ (hEU hP)))
  have ht : ContDiff ℝ (⊤ : ℕ∞)
      (fun t : ℝ => (t, (P.position, P.velocity))) :=
    contDiff_id.prodMk contDiff_const
  have hx : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : PDE.Vec d => (P.time, (x, P.velocity))) :=
    contDiff_const.prodMk (contDiff_id.prodMk contDiff_const)
  have hv : ContDiff ℝ (⊤ : ℕ∞)
      (fun v : PDE.Vec d => (P.time, (P.position, v))) :=
    contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
  have htime := hg.comp P.time ht.contDiffAt
  have hposition := hg.comp P.position hx.contDiffAt
  have hvelocity := hg.comp P.velocity hv.contDiffAt
  exact ⟨htime, hposition, hvelocity⟩

/-- The source backward operator is affine-linear on every smooth-near test. -/
theorem backwardOperator_affine {d : ℕ} (A : FullKineticCoefficient d)
    {psi : KineticPoint d → ℝ} {E : Set (KineticPoint d)}
    (hpsi : IsSmoothNear psi E) {P : KineticPoint d} (hP : P ∈ E) (a b : ℝ) :
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
  simp [matrixContraction_smul_right, backwardOperator_apply, kineticVelocityHessian_eq_sliceHessian]
  unfold PDE.vecDot
  simp
  simp_rw [mul_left_comm (P.velocity _) a]
  rw [← Finset.mul_sum]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Holder

