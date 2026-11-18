module

public import GS.UnitaryManifold.CayleyDifferential

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS Matrix GS.UnitaryGeometry
namespace GS.UnitaryManifold
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ}

def unitCayley (A : Matrix (Fin n) (Fin n) 𝕂) : Matrix (Fin n) (Fin n) 𝕂 :=
  cayley ((-1 / 2 : ℝ) • A)

@[simp] theorem unitCayley_zero : unitCayley (0 : Matrix (Fin n) (Fin n) 𝕂) = 1 := by
  simp [unitCayley]

theorem unitCayley_smooth_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E → Matrix (Fin n) (Fin n) 𝕂) (hs : ContDiff ℝ ⊤ A)
    (hk : ∀ x, IsSkewHermitian (A x)) : ContDiff ℝ ⊤ (fun x => unitCayley (A x)) :=
  contDiff_iff_contDiffAt.mpr fun x =>
    smooth_cayley_comp_at (hs.contDiffAt.const_smul (-1 / 2 : ℝ))
      (admissible_of_isSkew _ (skewHermitian_real_smul _ (hk x)))

theorem cayley_line_derivative (A : Matrix (Fin n) (Fin n) 𝕂) (hk : IsSkewHermitian A) :
    HasDerivAt (fun t : ℝ => cayley (t • A)) ((-2 : ℝ) • A) 0 := by
  let u : KModel 𝕂 (fun _ : Fin n => 0) := ⟨A, fun _ _ hij => (hij rfl).elim, hk⟩
  simpa only [chartInv, blockU_one_val, Matrix.one_mul, Submodule.coe_smul] using
    chartInv_line_hasDerivAt_zero (1 : KBlockU 𝕂 (fun _ : Fin n => 0)) u

theorem unitCayley_line_derivative (A : Matrix (Fin n) (Fin n) 𝕂) (hk : IsSkewHermitian A) :
    HasDerivAt (fun t : ℝ => unitCayley (t • A)) A 0 := by
  have hd := cayley_line_derivative ((-1 / 2 : ℝ) • A) (skewHermitian_real_smul _ hk)
  have hf : (fun t : ℝ => unitCayley (t • A)) = fun t => cayley (t • ((-1 / 2 : ℝ) • A)) := by
    funext t; unfold unitCayley; rw [smul_comm]
  rw [hf]
  simpa only [smul_smul, show (-2 : ℝ) * (-1 / 2) = 1 by norm_num, one_smul] using hd

end GS.UnitaryManifold
