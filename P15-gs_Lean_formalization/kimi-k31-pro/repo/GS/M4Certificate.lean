module

public import GS.GeometryAlgebra
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

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
set_option maxHeartbeats 4000000

def P : Mat 6 := !![1, 0, 0, 0, 0, 0;
  0, 0, 1, 0, 0, 0;
  0, 0, 0, 0, 1, 0;
  0, 1, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0;
  0, 0, 0, 0, 0, 1]

def B2 : Mat 6 := !![1, 1, 0, 0, 0, 0;
  1, -3, 0, 0, 0, 0;
  0, 0, 1, 1, 0, 0;
  0, 0, 1, (-1/3 : ℝ), 0, 0;
  0, 0, 0, 0, 1, 1;
  0, 0, 0, 0, 1, (1/3 : ℝ)]

def B3 : Mat 6 := !![1, 1, 0, 0, 0, 0;
  1, (1/3 : ℝ), 0, 0, 0, 0;
  0, 0, 1, 1, 0, 0;
  0, 0, 1, (-1/3 : ℝ), 0, 0;
  0, 0, 0, 0, 1, 1;
  0, 0, 0, 0, 1, -3]

def C : Mat 6 := !![1, 1, 1, 0, 1, 0;
  1, 0, -3, 1, 0, 1;
  0, (-1/3 : ℝ), 0, 1, 1, (1/3 : ℝ);
  1, (1/3 : ℝ), 1, 0, (1/3 : ℝ), 0;
  (-1/3 : ℝ), 0, 1, 1, 0, 1;
  0, (-1/3 : ℝ), 0, -3, 1, -1]

def H : Mat 6 := !![(7/4 : ℝ), -3, 0, 0, 0, 0;
  -3, (21/4 : ℝ), 0, 0, 0, 0;
  0, 0, (1/4 : ℝ), (1/3 : ℝ), 0, 0;
  0, 0, (1/3 : ℝ), (1/2 : ℝ), 0, 0;
  0, 0, 0, 0, (3/4 : ℝ), -1;
  0, 0, 0, 0, -1, (3/2 : ℝ)]

def G : Mat 6 := !![2, (-8/3 : ℝ), 0, 0, 0, 0;
  (-8/3 : ℝ), 4, 0, 0, 0, 0;
  0, 0, (4/3 : ℝ), (8/9 : ℝ), 0, 0;
  0, 0, (8/9 : ℝ), (2/3 : ℝ), 0, 0;
  0, 0, 0, 0, (28/9 : ℝ), (-16/3 : ℝ);
  0, 0, 0, 0, (-16/3 : ℝ), (28/3 : ℝ)]

def B1Param (s2 s3 s7 : ℝ) : Mat 6 := !![((1/2 : ℝ) * s7), 0, 0, 0, 0, 0;
  ((-6/7 : ℝ) * s7), ((1/14 : ℝ) * s3 * s7), 0, 0, 0, 0;
  0, 0, (1/2 : ℝ), 0, 0, 0;
  0, 0, (2/3 : ℝ), ((1/6 : ℝ) * s2), 0, 0;
  0, 0, 0, 0, ((1/2 : ℝ) * s3), 0;
  0, 0, 0, 0, ((-2/3 : ℝ) * s3), ((1/6 : ℝ) * s2 * s3)]

def B4Param (s2 s3 s7 : ℝ) : Mat 6 := !![((1/2 : ℝ) * s2), 0, 0, 0, 0, 0;
  2, (3/2 : ℝ), 0, 0, 0, 0;
  0, 0, ((1/2 : ℝ) * s3), 0, 0, 0;
  0, 0, (-1 * s2 * s3), ((3/2 : ℝ) * s2 * s3), 0, 0;
  0, 0, 0, 0, ((3/14 : ℝ) * s7), 0;
  0, 0, 0, 0, ((6/7 : ℝ) * s3 * s7), ((1/2 : ℝ) * s3 * s7)]

theorem core_identity : P*B3*P*B2*P = C := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P, B2, B3, C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Fin.sum_univ_succ] <;> ring <;> simp

theorem metric_identity : C*H*Cᵀ = G := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [C, H, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Fin.sum_univ_succ] <;> ring <;> simp

theorem gram_B1 (s2 s3 s7 : ℝ) (h2 : s2^2=2) (h3 : s3^2=3) (h7 : s7^2=7) : B1Param s2 s3 s7 * (B1Param s2 s3 s7)ᵀ = H := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [B1Param, H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Fin.sum_univ_succ] <;> ring_nf <;> simp [h2, h3, h7] <;> ring

theorem normalize_B4 (s2 s3 s7 : ℝ) (h2 : s2^2=2) (h3 : s3^2=3) (h7 : s7^2=7) : B4Param s2 s3 s7 * G * (B4Param s2 s3 s7)ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [B4Param, G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Fin.sum_univ_succ] <;> ring_nf <;> simp [h2, h3, h7] <;> ring

def B1 : Mat 6 := B1Param (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 7)
def B4 : Mat 6 := B4Param (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 7)
def Q : Mat 6 := B4*C*B1

theorem sqrt2_sq : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
theorem sqrt3_sq : (Real.sqrt 3)^2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
theorem sqrt7_sq : (Real.sqrt 7)^2 = (7 : ℝ) := Real.sq_sqrt (by norm_num)

theorem Q_orthogonal : Orthogonal Q := by
  exact gram_completion C H G B1 B4 metric_identity
    (gram_B1 _ _ _ sqrt2_sq sqrt3_sq sqrt7_sq)
    (normalize_B4 _ _ _ sqrt2_sq sqrt3_sq sqrt7_sq)

theorem B1_supported : BlockDiagonal 2 B1 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [B1,B1Param] at *
theorem B2_supported : BlockDiagonal 2 B2 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [B2] at *
theorem B3_supported : BlockDiagonal 2 B3 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [B3] at *
theorem B4_supported : BlockDiagonal 2 B4 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [B4,B4Param] at *

theorem Q_factorization : Q = product4 B4 P B3 P B2 P B1 := by
  unfold Q product4
  rw [← core_identity]
  simp only [Matrix.mul_assoc]

theorem Q_mem_A4 : InA4 2 2 2 2 P P P Q :=
  ⟨B1,B2,B3,B4,B1_supported,B2_supported,B3_supported,B4_supported,Q_factorization⟩

def cell (i : Fin 3) (a : Fin 2) : Fin 6 := ⟨2*i.val+a.val, by omega⟩
def detBlock (M : Mat 6) (i j : Fin 3) : ℝ :=
  M (cell i 0) (cell j 0) * M (cell i 1) (cell j 1) -
  M (cell i 0) (cell j 1) * M (cell i 1) (cell j 0)

theorem detBlock_eq_det (M : Mat 6) (i j : Fin 3) :
    detBlock M i j = Matrix.det (M.submatrix (cell i) (cell j)) := by
  rw [Matrix.det_fin_two]
  rfl

def detTable (s2 s3 : ℝ) : Mat 3 := !![((-3/16 : ℝ) * s2 * s3), (1/8 : ℝ), (3/8 : ℝ);
  ((3/16 : ℝ) * s2 * s3), (-3/8 : ℝ), (-1/8 : ℝ);
  (1/16 : ℝ), ((-3/16 : ℝ) * s2 * s3), ((-3/16 : ℝ) * s2 * s3)]

theorem detTable_param (s2 s3 s7 : ℝ) (h2 : s2^2=2) (h3 : s3^2=3) (h7 : s7^2=7) : (fun i j => detBlock (B4Param s2 s3 s7*C*B1Param s2 s3 s7) i j) = detTable s2 s3 := by
  have h3cube : s3^3 = 3*s3 := by calc
    s3^3 = s3*s3^2 := by ring
    _ = 3*s3 := by rw [h3]; ring
  have h3four : s3^4 = 9 := by calc
    s3^4 = (s3^2)^2 := by ring
    _ = 9 := by rw [h3]; norm_num
  have h7four : s7^4 = 49 := by calc
    s7^4 = (s7^2)^2 := by ring
    _ = 49 := by rw [h7]; norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [detBlock, cell, B4Param, B1Param, C, detTable, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp [h2, h3, h7, h3cube, h3four, h7four] <;> ring

theorem detTable_Q : (fun i j => detBlock Q i j) = detTable (Real.sqrt 2) (Real.sqrt 3) :=
  detTable_param _ _ _ sqrt2_sq sqrt3_sq sqrt7_sq

end GS.M4
