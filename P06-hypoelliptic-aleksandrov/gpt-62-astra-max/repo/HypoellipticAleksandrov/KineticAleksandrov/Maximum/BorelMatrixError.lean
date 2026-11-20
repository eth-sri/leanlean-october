module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelMatrixColumn
public import HypoellipticAleksandrov.Ambient.MatrixContraction
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Matrix.Normed

/-! # The exact Frobenius contraction bound for the source coefficient error -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open scoped MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ} {lam Lam : ℝ} (M : PDE.Mat d)

include M in
/-- Mathlib's Frobenius norm, named to make the Euclidean normalization explicit. -/
def borelFrobeniusNorm : ℝ := ‖M‖

/-- The Frobenius norm is the square root of the sum of squared entries. -/
theorem borelFrobeniusNorm_eq :
    borelFrobeniusNorm M = Real.sqrt (∑ i, ∑ j, (M i j) ^ 2) := by
  simp only [borelFrobeniusNorm,Matrix.frobenius_norm_def,Real.rpow_two,
    Real.norm_eq_abs,sq_abs,Real.sqrt_eq_rpow]

/-- The sharp ellipticity-to-Frobenius bound has the source factor sqrt d. -/
theorem borel_frobenius_norm_le {A : PDE.Mat d}
    (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hlo : lam • (1 : PDE.Mat d) ≤ A) (hhi : A ≤ Lam • (1 : PDE.Mat d)) :
    borelFrobeniusNorm A ≤ Real.sqrt d * Lam := by
  have hs : (∑ i, ∑ j, (A i j) ^ 2) ≤ d * Lam ^ 2 := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _j : Fin d, Lam ^ 2 := Finset.sum_le_sum fun j _ =>
        borel_matrix_column_sq_sum_le hlam hLam hlo hhi j
      _ = _ := by simp
  rw [borelFrobeniusNorm_eq]
  have hnon : 0 ≤ ∑ i : Fin d, ∑ j : Fin d, (A i j) ^ 2 := by positivity
  apply (sq_le_sq₀ (Real.sqrt_nonneg (∑ i, ∑ j, (A i j) ^ 2)) (mul_nonneg (Real.sqrt_nonneg (d : ℝ)) (hlam.le.trans hLam))).mp
  calc
    _ = _ := (Real.sq_sqrt hnon)
    _ ≤ _ := hs
    _ = _ := by rw [mul_pow,(Real.sq_sqrt (Nat.cast_nonneg d : (0 : ℝ) ≤ d))]

/-- Finite-dimensional Cauchy--Schwarz for the literal entrywise contraction. -/
theorem borel_matrix_contraction_le (M H : PDE.Mat d) :
    |matrixContraction M H| ≤ borelFrobeniusNorm M * borelFrobeniusNorm H := by
  have hplus := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun ij : Fin d × Fin d => M ij.1 ij.2) (fun ij => H ij.1 ij.2)
  have hminus := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun ij : Fin d × Fin d => -M ij.1 ij.2) (fun ij => H ij.1 ij.2)
  simp only [Fintype.sum_prod_type,neg_mul,Finset.sum_neg_distrib,neg_sq] at hplus hminus
  rw [borelFrobeniusNorm_eq,borelFrobeniusNorm_eq,abs_le]
  exact ⟨neg_le.mp hminus,hplus⟩

/-- The source error domination retains exactly 2 sqrt d times the upper bound. -/
theorem borel_coefficient_error_bound {A C : PDE.Mat d}
    (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hAl : lam • (1 : PDE.Mat d) ≤ A) (hAu : A ≤ Lam • (1 : PDE.Mat d))
    (hCl : lam • (1 : PDE.Mat d) ≤ C) (hCu : C ≤ Lam • (1 : PDE.Mat d))
    (H : PDE.Mat d) :
    |matrixContraction (C - A) H| ≤ 2 * Real.sqrt d * Lam * borelFrobeniusNorm H := by
  have hnorm : borelFrobeniusNorm (C - A) ≤ 2 * Real.sqrt d * Lam := by
    have ht := norm_sub_le C A
    change borelFrobeniusNorm (C - A) ≤ borelFrobeniusNorm C + borelFrobeniusNorm A at ht
    linarith only [(borel_frobenius_norm_le hlam hLam hAl hAu),(borel_frobenius_norm_le hlam hLam hCl hCu),ht]
  exact (borel_matrix_contraction_le (C - A) H).trans
    (mul_le_mul_of_nonneg_right hnorm (norm_nonneg H))

end HypoellipticAleksandrov.KineticAleksandrov
