
import GS.GeometryAlgebra
import Mathlib.Analysis.Real.Sqrt



/-!
# Exact m=4 example from the manuscript

Polynomial certificates are expressed as
Lean `linear_combination` proofs, not accepted as external numerical oracles.

The generic necessity proof and non-membership theorem are in M4Necessary.lean.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS.M4
set_option maxRecDepth 4096
set_option maxHeartbeats 0

def P : Mat 6 := !![1, 0, 0, 0, 0, 0;
  0, 0, 1, 0, 0, 0;
  0, 0, 0, 0, 1, 0;
  0, 1, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0;
  0, 0, 0, 0, 0, 1]

def blocks6 {α : Type*} [Zero α] (A : Fin 3 → Matrix (Fin 2) (Fin 2) α) :
    Matrix (Fin 6) (Fin 6) α := fun i j =>
  if i.val / 2 = j.val / 2 then A (i.divNat (n := 2)) (i.modNat (m := 3)) (j.modNat (m := 3)) else 0

theorem blocks6_supported (A : Fin 3 → Mat 2) : BlockDiagonal 2 (blocks6 A) := by
  intro i j hij
  exact if_neg hij

def B2 : Mat 6 := blocks6 ![!![1,1;1,-3], !![1,1;1,-1/3], !![1,1;1,1/3]]

def B3 : Mat 6 := blocks6 ![!![1,1;1,1/3], !![1,1;1,-1/3], !![1,1;1,-3]]

def C : Mat 6 := !![1, 1, 1, 0, 1, 0;
  1, 0, -3, 1, 0, 1;
  0, (-1/3 : ℝ), 0, 1, 1, (1/3 : ℝ);
  1, (1/3 : ℝ), 1, 0, (1/3 : ℝ), 0;
  (-1/3 : ℝ), 0, 1, 1, 0, 1;
  0, (-1/3 : ℝ), 0, -3, 1, -1]

def B1Param (s2 s3 s7 : ℝ) : Mat 6 := blocks6
  ![!![s7/2,0;-6/7*s7,1/14*s3*s7], !![1/2,0;2/3,1/6*s2], !![s3/2,0;-2/3*s3,1/6*s2*s3]]

def B4Param (s2 s3 s7 : ℝ) : Mat 6 := blocks6
  ![!![s2/2,0;2,3/2], !![s3/2,0;-s2*s3,3/2*s2*s3], !![3/14*s7,0;6/7*s3*s7,1/2*s3*s7]]

theorem core_identity : P*B3*P*B2*P = C := by
  ext i j
  fin_cases i,j <;>
    norm_num [B2, B3, C, P, blocks6, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.divNat, Fin.modNat, Fin.sum_univ_succ]

def B1 : Mat 6 := B1Param (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 7)
def B4 : Mat 6 := B4Param (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 7)
def Q : Mat 6 := B4*C*B1

theorem Q_orthogonal : Orthogonal Q := by
  apply Orthogonal.of_mul_transpose
  ext i j
  fin_cases i,j <;>
    norm_num [Q, B1, B4, B4Param, B1Param, C, blocks6, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.divNat, Fin.modNat, Fin.sum_univ_succ] <;> grind [Real.sq_sqrt]

theorem Q_mem_A4 : InA4 2 2 2 2 P P P Q := by
  refine ⟨B1,B2,B3,B4,blocks6_supported _,blocks6_supported _,
    blocks6_supported _,blocks6_supported _,?_⟩
  simp only [Q, product4, ← core_identity, Matrix.mul_assoc]

def cell (i : Fin 3) (a : Fin 2) : Fin 6 := ⟨2*i.val+a.val, by omega⟩
def detBlock {α : Type*} [CommRing α] (M : Matrix (Fin 6) (Fin 6) α) (i j : Fin 3) :=
  Matrix.det (M.submatrix (cell i) (cell j))

def detTable (s2 s3 : ℝ) : Mat 3 := !![((-3/16 : ℝ) * s2 * s3), (1/8 : ℝ), (3/8 : ℝ);
  ((3/16 : ℝ) * s2 * s3), (-3/8 : ℝ), (-1/8 : ℝ);
  (1/16 : ℝ), ((-3/16 : ℝ) * s2 * s3), ((-3/16 : ℝ) * s2 * s3)]

theorem detTable_Q : (fun i j => detBlock Q i j) = detTable (Real.sqrt 2) (Real.sqrt 3) := by
  ext i j
  fin_cases i,j <;>
    norm_num [Q, B1, B4, detBlock, Matrix.det_fin_two, Matrix.submatrix_apply, cell, B4Param, B1Param, C, detTable, blocks6,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.divNat, Fin.modNat, Fin.sum_univ_succ] <;> grind [Real.sq_sqrt]

end GS.M4
