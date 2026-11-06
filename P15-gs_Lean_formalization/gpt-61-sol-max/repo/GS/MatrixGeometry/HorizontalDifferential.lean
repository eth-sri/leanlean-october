import Mathlib.Tactic
import GS.MatrixGeometry.Base

import GS.MatrixGeometry.ProjectedSlice


/-!
# The full differential image after removing the shared stabilizer

The complement has the same differential image as the complete factor model
at every translated centre.  It therefore represents every matrix direction,
including when shared blocks and cross-layer overlap occur simultaneously.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS.MatrixBase
namespace GS.MatrixGeometry
variable {𝕜 : Type} [RCLike 𝕜]
variable  {right left : Pattern 𝕜 n}
local instance horizontalDifferentialNormedSpace (P : KMat 𝕜 n) :
    NormedSpace ℝ (HorizontalModel right left P) := Submodule.normedSpace _

variable (P : KMat 𝕜 n)

variable (g : Factors right left)

theorem horizontalOrbit_fderiv_zero 
     (h : HorizontalModel right left P) :
    fderiv ℝ (fun h : HorizontalModel right left P => orbitParam g P h.val) 0 h =
      fderiv ℝ (orbitParam g P) 0 h.val := by
  have hh := ((orbitParam_smooth g P).differentiable (by simp) 0).hasFDerivAt
  have hd := hh.comp (f := fun h : HorizontalModel right left P => h.val) 0
    (HorizontalModel right left P).subtypeL.hasFDerivAt
  convert congrArg (fun D => D h) hd.fderiv using 1 <;> rfl

theorem horizontalOrbit_fderiv_zero_range 
     (Z : KMat 𝕜 n) :
    (∃ h : HorizontalModel right left P,
      fderiv ℝ (fun h : HorizontalModel right left P => orbitParam g P h.val) 0 h = Z) ↔
      Z ∈ pointDirections right left (g • P) := by
  rw [← orbitParam_fderiv_zero_range g P Z]
  constructor
  · grind [horizontalOrbit_fderiv_zero]
  · rintro ⟨v, hv⟩
    let z := (horizontalKernelEquiv right left P).symm v
    have hz : (z.1.val : PairGenerator right left) + z.2.val = v :=
      (horizontalKernelEquiv right left P).apply_symm_apply v
    have hk : fderiv ℝ (orbitParam g P) 0 z.2.val = 0 :=
      by
        have hi := orbitParam_intertwine_of_kernel P z.2.val z.2.property
        rw [orbitParam_fderiv_zero]
        simp only [GS.MatrixBase.tangentParam,Matrix.smul_mul,Matrix.mul_smul]
        have he : Factor.matrix g.1 * z.2.val.1.val * P * (Factor.matrix g.2)ᴴ =
            Factor.matrix g.1 * P * z.2.val.2.val * (Factor.matrix g.2)ᴴ := by grind
        rw [he,← add_smul]
        norm_num
    refine ⟨z.1, ?_⟩
    rw [horizontalOrbit_fderiv_zero, ← hv, ← hz, map_add, hk, add_zero]

end GS.MatrixGeometry
