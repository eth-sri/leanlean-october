/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousMonomials
public import CCDN.Hilbert.HomogeneousHilbert
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

/-! Exact evaluation rank identities for plane projective curves. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- Twice the dimension of ternary forms, without natural-number division. -/
lemma ternary_homogeneous_dimension (M : ℕ) :
    2 * (2 + M).choose M = (M + 2) * (M + 1) := by
  have h := Nat.add_one_mul_choose_eq (M + 1) 1
  simp only [Nat.choose_one_right] at h
  rw [← Nat.choose_symm_add]
  simpa only [show M + 1 + 1 = M + 2 by omega, show 1 + 1 = 2 from rfl,
    Nat.add_comm 2 M, Nat.mul_comm] using h.symm

/-- Closed form of the exact rank for plane projective curves. -/
lemma plane_homogeneous_rank_identity {s d M : ℕ} (hdM : d ≤ M)
    (hr : s + (2 + (M - d)).choose (M - d) = (2 + M).choose M) :
    2 * s + d ^ 2 = d * (2 * M + 3) := by
  have hM := ternary_homogeneous_dimension M
  have hMd := ternary_homogeneous_dimension (M - d)
  have hsub : M - d + d = M := Nat.sub_add_cancel hdM
  nlinarith

/-- Elementary rank bounds sufficient to compare the plane rank with d*M. -/
lemma plane_homogeneous_rank_bounds {s d M : ℕ} (hd : 0 < d) (hdM : d ≤ M)
    (hr : s + (2 + (M - d)).choose (M - d) = (2 + M).choose M) :
    0 < s ∧ d * M ≤ 2 * s ∧ s ≤ d * (M + 1) := by
  have he := plane_homogeneous_rank_identity hdM hr
  have hm : 0 < M := lt_of_lt_of_le hd hdM
  have hd2 : d ^ 2 ≤ d * M := by nlinarith
  have hd1 : d ≤ d ^ 2 := by nlinarith
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

end
end CCDN
