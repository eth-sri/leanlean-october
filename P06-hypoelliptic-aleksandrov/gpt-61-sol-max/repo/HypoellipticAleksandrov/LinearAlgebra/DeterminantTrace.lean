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

 public section

open scoped BigOperators MatrixOrder
open Matrix

namespace HypoellipticAleksandrov

variable (d : ℕ)

private theorem finite_amgm_succ  (s : ℝ) (x : Fin d → ℝ) (hs : 0 ≤ s)
    (hx : ∀ i, 0 ≤ x i) :
    s * (∏ i, x i) ≤ ((s + ∑ i, x i) / ((d : ℝ) + 1)) ^ (d + 1) := by
  let sharedTerm_d68cd4a2e7 := ((s + ∑ i, x i) / ((d : ℝ) + 1))
  let sharedTerm_8c3cabff32 := (∏ i, x i)
  let z : Fin (d + 1) → ℝ := Fin.cons s x

  have hgm := Real.geom_mean_le_arith_mean Finset.univ (fun _ : Fin (d + 1) => 1) z
    (by simp) (by positivity) (by
        intro i _
        refine Fin.cases hs hx i)

  have hprod_nonneg : 0 ≤ s * sharedTerm_8c3cabff32 :=
    mul_nonneg hs (Finset.prod_nonneg fun i _ => hx i)
  have hn_pos : 0 < (d : ℝ) + 1 := by positivity
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hprod_nonneg _) (by
      simpa [z, Fin.sum_univ_succ, Fin.prod_univ_succ] using hgm) hn_pos.le

  calc
    s * sharedTerm_8c3cabff32 = (s * sharedTerm_8c3cabff32) ^ (((d : ℝ) + 1)⁻¹ * ((d : ℝ) + 1)) := by
      rw [inv_mul_cancel₀ (ne_of_gt hn_pos), Real.rpow_one]
    _ = ((s * sharedTerm_8c3cabff32) ^ (((d : ℝ) + 1)⁻¹)) ^ ((d : ℝ) + 1) := by
      rw [Real.rpow_mul hprod_nonneg]
    _ ≤ (sharedTerm_d68cd4a2e7) ^ ((d : ℝ) + 1) := hpow
    _ = (sharedTerm_d68cd4a2e7) ^ (d + 1) := by
      have hcast : (d : ℝ) + 1 = ((d + 1 : ℕ) : ℝ) := by norm_num
      rw [hcast, Real.rpow_natCast]

/--
For a positive-definite matrix `A`, a positive-semidefinite matrix `H`, and a
nonnegative scalar `s`, bounds `det A * s * det H` by the `(d + 1)`-st power
of the arithmetic mean of `s` and `trace (A * H)`.
-/
theorem det_mul_time_det_le_arith_mean_pow
     (A H : PDE.Mat d) (s : ℝ)
    (hA : A.PosDef) (hH : H.PosSemidef) (hs : 0 ≤ s) :
    A.det * s * H.det ≤
      ((s + (A * H).trace) / ((d : ℝ) + 1)) ^ (d + 1) := by
  let B : PDE.Mat d := CFC.sqrt A * H * CFC.sqrt A
  have hB : B.PosSemidef := by
    have hsqrt : (CFC.sqrt A)ᴴ = CFC.sqrt A :=
      (CFC.sqrt_nonneg A).isSelfAdjoint.star_eq
    simpa only [B, hsqrt] using hH.conjTranspose_mul_mul_same (CFC.sqrt A)
  have hdet : B.det = A.det * H.det := by
    calc
      B.det = (CFC.sqrt A).det * H.det * (CFC.sqrt A).det := by
        dsimp only [B]
        rw [Matrix.det_mul, Matrix.det_mul]
      _ = ((CFC.sqrt A).det * (CFC.sqrt A).det) * H.det := by ring
      _ = (CFC.sqrt A * CFC.sqrt A).det * H.det := by rw [Matrix.det_mul]
      _ = A.det * H.det := by rw [CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg]
  have htrace : B.trace = (A * H).trace := by
    calc
      B.trace = (H * CFC.sqrt A * CFC.sqrt A).trace := (id (Eq.symm (trace_mul_cycle H (CFC.sqrt A) (CFC.sqrt A))))
      _ = (H * (CFC.sqrt A * CFC.sqrt A)).trace := by rw [Matrix.mul_assoc]
      _ = (H * A).trace := by rw [CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg]
      _ = (A * H).trace := Matrix.trace_mul_comm _ _
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
