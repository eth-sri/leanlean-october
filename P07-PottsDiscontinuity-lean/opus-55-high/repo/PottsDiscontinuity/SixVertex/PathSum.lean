module

public import Mathlib

/-!
# Trace of a matrix power as a sum over closed chains

For a square matrix `A` indexed by a finite type `S` and `m ≥ 1`,
`tr (A ^ m) = ∑_{x : Fin m → S} ∏_{j : Fin m} A (x j) (x (j + 1 mod m))`.
-/

public section

open Finset Matrix

namespace PottsDiscontinuity.SixVertex

section
variable {S R : Type*} [Fintype S] [DecidableEq S] [CommSemiring R] (A : Matrix S S R) (m : ℕ)
/-- Matrix power entries as sums over chains `x₀ = a, x₁, …, x_m` ending in `b`. -/
theorem pow_succ_apply_chain (a b : S) :
    (A ^ (m + 1)) a b = ∑ x : Fin (m + 1) → S,
      if x 0 = a then (∏ j : Fin m, A (x j.castSucc) (x j.succ)) * A (x (Fin.last m)) b else 0 := by
  induction m generalizing b with
  | zero =>
    rw [← (Equiv.funUnique (Fin 1) S).symm.sum_comp]
    simp
  | succ m ih =>
    rw [pow_succ, Matrix.mul_apply]
    simp_rw [ih, Finset.sum_mul]
    rw [← Equiv.sum_comp (Fin.snocEquiv fun _ : Fin (m + 2) => S), Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun x _ => ?_
    have hx : ∀ i : Fin m, (Fin.snoc x c : Fin (m + 2) → S) i.castSucc.succ = x i.succ := by
      intro i
      rw [Fin.succ_castSucc, Fin.snoc_castSucc]
    have h0 : (Fin.snoc x c : Fin (m + 2) → S) 0 = x 0 :=
      by rfl
    simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.prod_univ_castSucc, Fin.snoc_castSucc,
      Fin.snoc_last, hx, h0]
    simp

/-- `tr (A ^ (m + 1))` as a sum over closed chains of length `m + 1`. -/
theorem trace_pow_succ_eq_sum_chain  :
    Matrix.trace (A ^ (m + 1)) = ∑ x : Fin (m + 1) → S,
      ∏ j : Fin (m + 1), A (x j) (x (finRotate (m + 1) j)) := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply, pow_succ_apply_chain]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fin.prod_univ_castSucc]
  simp
end

end PottsDiscontinuity.SixVertex
