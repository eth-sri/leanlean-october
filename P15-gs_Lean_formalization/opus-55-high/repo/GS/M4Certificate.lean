module

public import GS.GeometryAlgebra
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section


/-!
# Exact m=4 example from the manuscript

Polynomial certificates are expressed as
Lean `linear_combination` proofs, not accepted as external numerical oracles.

The generic necessity proof and non-membership theorem are in M4Necessary.lean.
-/

noncomputable section
open Matrix
namespace GS.M4
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

def B1 : Mat 6 := !![((1/2 : ℝ) * √7), 0, 0, 0, 0, 0;
  ((-6/7 : ℝ) * √7), ((1/14 : ℝ) * √3 * √7), 0, 0, 0, 0;
  0, 0, (1/2 : ℝ), 0, 0, 0;
  0, 0, (2/3 : ℝ), ((1/6 : ℝ) * √2), 0, 0;
  0, 0, 0, 0, ((1/2 : ℝ) * √3), 0;
  0, 0, 0, 0, ((-2/3 : ℝ) * √3), ((1/6 : ℝ) * √2 * √3)]

def B4 : Mat 6 := !![((1/2 : ℝ) * √2), 0, 0, 0, 0, 0;
  2, (3/2 : ℝ), 0, 0, 0, 0;
  0, 0, ((1/2 : ℝ) * √3), 0, 0, 0;
  0, 0, (-1 * √2 * √3), ((3/2 : ℝ) * √2 * √3), 0, 0;
  0, 0, 0, 0, ((3/14 : ℝ) * √7), 0;
  0, 0, 0, 0, ((6/7 : ℝ) * √3 * √7), ((1/2 : ℝ) * √3 * √7)]


theorem core_identity : P*B3*P*B2*P = C := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [P, B2, B3, C, Matrix.mul_apply, Fin.sum_univ_succ]

theorem metric_identity : C*H*Cᵀ = G := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [C, H, G, Matrix.mul_apply, Fin.sum_univ_succ]

def Q : Mat 6 := B4*C*B1

theorem Q_orthogonal : Orthogonal Q := by
  refine gram_completion C H G B1 B4 metric_identity ?_ ?_ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [B1, B4, H, G, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp <;> ring_nf

theorem Q_mem_A4 : InA4 2 2 2 2 P P P Q := by
  refine ⟨B1,B2,B3,B4,?_,?_,?_,?_,?_⟩
  rotate_left 4
  · unfold Q product4
    rw [← core_identity]
    grind
  all_goals intro i j hij; fin_cases i <;> fin_cases j <;> norm_num [B1,B2,B3,B4] at *

def cell (i : Fin 3) (a : Fin 2) : Fin 6 := ⟨2*i.val+a.val, by omega⟩
def detBlock (M : Mat 6) (i j : Fin 3) : ℝ :=
  M (cell i 0) (cell j 0) * M (cell i 1) (cell j 1) -
  M (cell i 0) (cell j 1) * M (cell i 1) (cell j 0)


def detTable (s2 s3 : ℝ) : Mat 3 := !![((-3/16 : ℝ) * s2 * s3), (1/8 : ℝ), (3/8 : ℝ);
  ((3/16 : ℝ) * s2 * s3), (-3/8 : ℝ), (-1/8 : ℝ);
  (1/16 : ℝ), ((-3/16 : ℝ) * s2 * s3), ((-3/16 : ℝ) * s2 * s3)]

theorem detTable_Q : (fun i j => detBlock Q i j) = detTable (Real.sqrt 2) (Real.sqrt 3) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Q, B1, B4, detBlock, cell, C, detTable, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring_nf <;> simp [show √3^3 = 3*√3 by grind] <;> ring_nf <;> nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0:ℝ) ≤ 7 by norm_num)]

end GS.M4
