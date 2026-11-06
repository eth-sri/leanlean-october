import GS.MatrixGeometry.Base

import GS.MatrixGeometry.HorizontalModel
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff


set_option backward.isDefEq.respectTransparency false
/-!
# Local horizontal--stabilizer product for shared factors

The derivative of multiplication in the actual shared Cayley coordinates is
addition.  The horizontal/kernel splitting makes this derivative invertible,
so the inverse function theorem supplies the needed local product chart.
No product decomposition of the image is assumed.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS.MatrixBase
namespace GS.MatrixGeometry
variable {𝕜 : Type} [RCLike 𝕜]
variable  {s right left : Pattern 𝕜 n}

variable (s right left : Pattern 𝕜 n)

variable (P : KMat 𝕜 n)

def blockProductCoordinates  (x : Generator s × Generator s) := factorCoordinates (1 : Factor s)
    (matrixReconstruct (1 : Factor s) x.1 * matrixReconstruct (1 : Factor s) x.2)



@[fun_prop] theorem blockProductCoordinates_smooth_zero  :
    ContDiffAt ℝ ⊤ (blockProductCoordinates s) 0 := by
  apply ContDiffAt.comp (f := fun x : Generator s × Generator s =>
    matrixReconstruct (1 : Factor s) x.1 * matrixReconstruct (1 : Factor s) x.2) 0
  · simpa using factorCoordinates_smooth_at (1 : Factor s) (1 : KMat 𝕜 n)
      (by aesop)
  · exact smooth_mul_at
      ((matrixReconstruct_smooth (1 : Factor s)).contDiffAt.comp 0 contDiffAt_fst)
      ((matrixReconstruct_smooth (1 : Factor s)).contDiffAt.comp 0 contDiffAt_snd)


def factorProductCoordinates 
    (x : PairGenerator right left × PairGenerator right left) := (blockProductCoordinates left (x.1.1, x.2.1),
    blockProductCoordinates right (x.1.2, x.2.2))





theorem blockProductCoordinates_hasFDerivAt_zero  :
    HasFDerivAt (blockProductCoordinates s)
      (ContinuousLinearMap.fst ℝ (Generator s) (Generator s) +
        ContinuousLinearMap.snd ℝ (Generator s) (Generator s)) 0 := by
  have h := ((blockProductCoordinates_smooth_zero s).differentiableAt (by simp)).hasFDerivAt
  convert h using 1
  apply ContinuousLinearMap.ext
  intro v
  symm
  change fderiv ℝ (blockProductCoordinates s) 0 v = v.1 + v.2
  have hp := hasDerivAt_matrix_mul
    (reconstruct_line_hasDerivAt_zero (1 : Factor s) v.1)
    (reconstruct_line_hasDerivAt_zero (1 : Factor s) v.2)
  have hc := (factorCoordinates_smooth_at (1 : Factor s) (1 : KMat 𝕜 n)
    (by aesop)).differentiableAt (by simp)
  have ha := hc.hasFDerivAt.comp_hasDerivAt_of_eq 0 hp (by simp)
  have hi := ((blockProductCoordinates_smooth_zero s).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).smul_const v) (by simp)
  simp only [one_smul] at hi
  refine (hi.unique ha).trans ?_
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    matrixReconstruct_fderiv_zero, matrixReconstruct_zero, Factor.matrix_one,
    Matrix.one_mul, Matrix.mul_one, zero_smul, reconstruct_zero,
    Submodule.coe_add, smul_add] using
      congrArg (fun D : Generator s →L[ℝ] Generator s => D (v.1 + v.2))
        (coordinateDerivative_reconstruct (1 : Factor s) 0)


def reorderLeft := ((ContinuousLinearMap.fst ℝ (Generator left) (Generator right)).comp
    (ContinuousLinearMap.fst ℝ _ _)).prod
  ((ContinuousLinearMap.fst ℝ (Generator left) (Generator right)).comp
    (ContinuousLinearMap.snd ℝ _ _))

def reorderRight := ((ContinuousLinearMap.snd ℝ (Generator left) (Generator right)).comp
    (ContinuousLinearMap.fst ℝ _ _)).prod
  ((ContinuousLinearMap.snd ℝ (Generator left) (Generator right)).comp
    (ContinuousLinearMap.snd ℝ _ _))

@[fun_prop] theorem factorProductCoordinates_smooth_zero  :
    ContDiffAt ℝ ⊤ (factorProductCoordinates right left) 0 := by
  fun_prop [factorProductCoordinates]

theorem factorProductCoordinates_hasFDerivAt_zero  :
    HasFDerivAt (factorProductCoordinates right left)
      (ContinuousLinearMap.fst ℝ (PairGenerator right left) (PairGenerator right left) +
        ContinuousLinearMap.snd ℝ (PairGenerator right left) (PairGenerator right left)) 0 := by
  have hl := (blockProductCoordinates_hasFDerivAt_zero left).comp (f := reorderLeft right left) 0
    (reorderLeft right left).hasFDerivAt
  have hr := (blockProductCoordinates_hasFDerivAt_zero right).comp (f := reorderRight right left) 0
    (reorderRight right left).hasFDerivAt
  convert hl.prodMk hr using 1 <;> rfl

def sliceProduct  
    (x : HorizontalModel right left P × OrbitKernel right left P) := factorProductCoordinates right left (x.1.val, x.2.val)

def sliceInclusion := ((HorizontalModel right left P).subtypeL.comp (ContinuousLinearMap.fst ℝ _ _)).prod
    ((OrbitKernel right left P).subtypeL.comp (ContinuousLinearMap.snd ℝ _ _))



theorem sliceProduct_smooth_zero   :
    ContDiffAt ℝ ⊤ (sliceProduct right left P) 0 := by
  fun_prop [sliceProduct]

theorem sliceProduct_hasFDerivAt_zero 
     :
    HasFDerivAt (sliceProduct right left P)
      (horizontalKernelEquiv right left P : _ →L[ℝ] _) 0 := by
  have hd := (factorProductCoordinates_hasFDerivAt_zero right left).comp (f := sliceInclusion right left P) 0
    (@ContinuousLinearMap.hasFDerivAt ℝ _ (HorizontalModel right left P × OrbitKernel right left P) _ _ _ (PairGenerator right left × PairGenerator right left) _ _ _ (sliceInclusion right left P) 0)
  convert hd using 1 <;> rfl

def sliceProductChart := (sliceProduct_smooth_zero right left P).toOpenPartialHomeomorph _
    (sliceProduct_hasFDerivAt_zero right left P) (by simp)



theorem sliceProductChart_zero_mem_source 
     : (0 : HorizontalModel right left P × OrbitKernel right left P)
      ∈ (sliceProductChart right left P).source :=
  (sliceProduct_smooth_zero right left P).mem_toOpenPartialHomeomorph_source _ (by simp)

end GS.MatrixGeometry
