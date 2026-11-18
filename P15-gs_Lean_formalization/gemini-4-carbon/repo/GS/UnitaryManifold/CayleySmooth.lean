module

public import GS.UnitaryManifold.CayleyModel

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix
namespace GS.UnitaryManifold
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem smooth_mul_at {A B : E → Matrix (Fin n) (Fin n) 𝕂} {x : E}
    (hA : ContDiffAt ℝ ⊤ A x) (hB : ContDiffAt ℝ ⊤ B x) :
    ContDiffAt ℝ ⊤ (fun y => A y * B y) x := by
  refine contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun k _ =>
    (contDiffAt_pi.mp (contDiffAt_pi.mp hA i) k).mul (contDiffAt_pi.mp (contDiffAt_pi.mp hB k) j)

theorem smooth_conjTranspose_at {A : E → Matrix (Fin n) (Fin n) 𝕂} {x : E}
    (hA : ContDiffAt ℝ ⊤ A x) : ContDiffAt ℝ ⊤ (fun y => (A y)ᴴ) x :=
  contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j =>
    (RCLike.conjCLE (K := 𝕂)).contDiff.contDiffAt.comp x (contDiffAt_pi.mp (contDiffAt_pi.mp hA j) i)

theorem smooth_det : ContDiff ℝ ⊤ (fun A : Matrix (Fin n) (Fin n) 𝕂 => A.det) := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun σ _ => ContDiff.mul contDiff_const <|
    contDiff_prod fun i _ => contDiff_apply_apply ℝ 𝕂 (σ i) i

theorem smooth_adjugate : ContDiff ℝ ⊤ (fun A : Matrix (Fin n) (Fin n) 𝕂 => A.adjugate) := by
  refine contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => ?_
  simp only [Matrix.adjugate_apply]
  refine smooth_det.comp (contDiff_pi.mpr fun a => contDiff_pi.mpr fun b => ?_)
  by_cases ha : a = j
  · subst a; simp only [Matrix.updateRow, Matrix.of_apply, Function.update_self]; exact contDiff_const
  · simpa only [Matrix.updateRow, Matrix.of_apply, Function.update_of_ne ha, id_eq] using
      (contDiff_pi.mp (contDiff_pi.mp (contDiff_id : ContDiff ℝ ⊤ (id : Matrix (Fin n) (Fin n) 𝕂 → _)) a) b)

theorem smooth_inverse_at (A : Matrix (Fin n) (Fin n) 𝕂) (hA : A.det ≠ 0) :
    ContDiffAt ℝ ⊤ (fun B : Matrix (Fin n) (Fin n) 𝕂 => B⁻¹) A := by
  have h : ContDiffAt ℝ ⊤ (fun B : Matrix (Fin n) (Fin n) 𝕂 => B.det⁻¹ • B.adjugate) A :=
    contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j =>
      (smooth_det.contDiffAt.inv hA).mul
        (contDiffAt_pi.mp (contDiffAt_pi.mp smooth_adjugate.contDiffAt i) j)
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv] using h

theorem smooth_inverse_comp_at {A : E → Matrix (Fin n) (Fin n) 𝕂} {x : E}
    (hA : ContDiffAt ℝ ⊤ A x) (hd : (A x).det ≠ 0) : ContDiffAt ℝ ⊤ (fun y => (A y)⁻¹) x :=
  (smooth_inverse_at (A x) hd).comp x hA

theorem smooth_cayley_at (A : Matrix (Fin n) (Fin n) 𝕂) (hA : admissible A) :
    ContDiffAt ℝ ⊤ cayley A :=
  smooth_mul_at (contDiffAt_const.sub contDiffAt_id)
    (smooth_inverse_comp_at (contDiffAt_const.add contDiffAt_id) hA)

theorem smooth_cayley_comp_at {A : E → Matrix (Fin n) (Fin n) 𝕂} {x : E}
    (hA : ContDiffAt ℝ ⊤ A x) (hd : admissible (A x)) :
    ContDiffAt ℝ ⊤ (fun y => cayley (A y)) x :=
  (smooth_cayley_at (A x) hd).comp x hA

theorem admissible_open : IsOpen {A : Matrix (Fin n) (Fin n) 𝕂 | admissible A} :=
  isOpen_ne.preimage (smooth_det.continuous.comp (continuous_const.add continuous_id))

end GS.UnitaryManifold
