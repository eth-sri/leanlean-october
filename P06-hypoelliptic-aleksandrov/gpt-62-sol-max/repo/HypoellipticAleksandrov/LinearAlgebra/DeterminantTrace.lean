module

public import HypoellipticAleksandrov.Ambient.Basic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.MeanInequalities

/-!
# Determinant--trace inequalities

This module proves the finite-dimensional determinant--trace estimate used in
the smooth parabolic ABP argument.  It is purely matrix algebra: no
ellipticity predicate or PDE estimate appears here.
-/

@[expose] public section

open scoped BigOperators MatrixOrder
open Matrix

namespace HypoellipticAleksandrov

private theorem finite_amgm_succ (d : ℕ) (s : ℝ) (x : Fin d → ℝ) (hs : 0 ≤ s)
    (hx : ∀ i, 0 ≤ x i) :
    s * (∏ i, x i) ≤ ((s + ∑ i, x i) / ((d : ℝ) + 1)) ^ (d + 1) := by
  let z : Fin (d + 1) → ℝ := Fin.cons s x
  have hz : ∀ i ∈ Finset.univ, 0 ≤ z i := by
    intro i _
    refine Fin.cases hs hx i
  have hgm := Real.geom_mean_le_arith_mean Finset.univ (fun _ : Fin (d + 1) => 1) z
    (by simp) (by positivity) hz
  have hgm' :
      (s * ∏ i, x i) ^ (((d : ℝ) + 1)⁻¹) ≤ (s + ∑ i, x i) / ((d : ℝ) + 1) := by
    simpa [z, Fin.sum_univ_succ, Fin.prod_univ_succ] using hgm
  have h := (Real.rpow_inv_le_iff_of_pos (mul_nonneg hs (Finset.prod_nonneg fun i _ => hx i))
    (div_nonneg (add_nonneg hs (Finset.sum_nonneg fun i _ => hx i)) (by positivity))
    (by positivity)).mp hgm'
  rw [show (d : ℝ) + 1 = ((d + 1 : ℕ) : ℝ) by simp, Real.rpow_natCast] at h
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- The symmetric square-root sandwich preserves the required determinant and trace. -/
private theorem exists_psd_sandwich {d : ℕ} (A H : PDE.Mat d)
    (hA : A.PosSemidef) (hH : H.PosSemidef) :
    ∃ B : PDE.Mat d, B.PosSemidef ∧ B.det = A.det * H.det ∧ B.trace = (A * H).trace := by
  have hs := CFC.sqrt_mul_sqrt_self A hA.nonneg
  refine ⟨CFC.sqrt A * H * CFC.sqrt A, ?_, ?_, ?_⟩
  · have hS : (CFC.sqrt A)ᴴ = CFC.sqrt A := (CFC.sqrt_nonneg A).isSelfAdjoint.star_eq
    simpa only [hS] using hH.conjTranspose_mul_mul_same (CFC.sqrt A)
  · calc
      _ = (CFC.sqrt A * CFC.sqrt A).det * H.det := by simp only [Matrix.det_mul]; ring
      _ = _ := by rw [hs]
  · rw [Matrix.trace_mul_cycle, hs]

/-- The trace of the product of two positive semidefinite matrices is nonnegative. -/
theorem trace_mul_nonneg_of_posSemidef {d : ℕ} (A H : PDE.Mat d)
    (hA : A.PosSemidef) (hH : H.PosSemidef) : 0 ≤ (A * H).trace := by
  obtain ⟨B, hB, _, ht⟩ := exists_psd_sandwich A H hA hH
  rw [← ht]
  exact hB.trace_nonneg

/--
For a positive-definite matrix `A`, a positive-semidefinite matrix `H`, and a
nonnegative scalar `s`, bounds `det A * s * det H` by the `(d + 1)`-st power
of the arithmetic mean of `s` and `trace (A * H)`.
-/
theorem det_mul_time_det_le_arith_mean_pow
    (d : ℕ) (A H : PDE.Mat d) (s : ℝ)
    (hA : A.PosDef) (hH : H.PosSemidef) (hs : 0 ≤ s) :
    A.det * s * H.det ≤
      ((s + (A * H).trace) / ((d : ℝ) + 1)) ^ (d + 1) := by
  obtain ⟨B, hB, hdet, htrace⟩ := exists_psd_sandwich A H hA.posSemidef hH
  calc
    A.det * s * H.det = s * B.det := by rw [hdet]; ring
    _ = s * ∏ i, hB.isHermitian.eigenvalues i := by
      rw [hB.isHermitian.det_eq_prod_eigenvalues]
      simp
    _ ≤ ((s + ∑ i, hB.isHermitian.eigenvalues i) / ((d : ℝ) + 1)) ^ (d + 1) :=
      finite_amgm_succ d s hB.isHermitian.eigenvalues hs hB.eigenvalues_nonneg
    _ = ((s + (A * H).trace) / ((d : ℝ) + 1)) ^ (d + 1) := by
      rw [← htrace, hB.isHermitian.trace_eq_sum_eigenvalues]
      simp

end HypoellipticAleksandrov
