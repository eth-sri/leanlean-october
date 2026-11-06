/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Algebra.IntegerLinearForms
public import CCDN.Algebra.ProjectiveSection
public import CCDN.Height.ProjectiveZeroLocus
import CCDN.Algebra.ProjectiveFiniteFibers
import CCDN.Determinant.PolynomialMapDeterminant
import CCDN.Projection.BoundedLinearProjection

/-! Height and cardinality transport through an integer linear
projection with uniformly bounded affine fibers. -/

@[expose] public section
namespace CCDN
open MvPolynomial Matrix

variable {m n : ℕ}

private noncomputable def integerProjectiveLinearImage 
    (P : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ) (x : ProjectivePoint n)  :=
  if h : (P.map (Int.castRingHom ℚ)) *ᵥ x.rep ≠ 0 then
    Projectivization.mk ℚ ((P.map (Int.castRingHom ℚ)) *ᵥ x.rep) h
  else
    Projectivization.mk ℚ (fun _ : Fin (m + 1) => 1) (by
      solve_by_elim [congrFun, one_ne_zero])

/-- Let `P` be an integer matrix with entries of absolute value at most `H` whose linear forms
satisfy the homogeneous relation `f` modulo `I`. If every affine fiber of the induced map on the
zero locus of `I` has at most `M` points, then the projective rational points of height at most `B`
on the zero locus of `I` number at most `M` times those of height at most `(n + 1) * H * B` on the
projective hypersurface `f = 0`. -/
theorem projective_integer_linear_count_transfer
     (I : CCDN.CoordinateIdeal (n + 1))
    (P : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ)
    (f : CCDN.CoordinatePolynomial (m + 1)) (hf : f.IsHomogeneous f.totalDegree)
    (hrelation : aeval (fun i => integerLinearForm (P i)) f ∈ I)
    (M : ℕ)
    (hfinite : ∀ z : CCDN.RatPoint (m + 1), ∀ s : Finset (CCDN.RatPoint (n + 1)),
      (∀ x ∈ s, x ∈ idealZeroLocus I) →
      (∀ x ∈ s, ∀ i, eval x (integerLinearForm (P i)) = z i) → s.card ≤ M)
    (H B : ℝ) (hH : 0 ≤ H)
    (hP : ∀ i j, |(P i j : ℝ)| ≤ H) :
    projectiveCount (projectiveIdealZeroLocus I) B ≤
      M * projectiveCount (projectiveZeroLocus f) ((n + 1 : ℕ) * H * B) := by
  classical
  let L := (P.map (Int.castRingHom ℚ)).mulVecLin
  let π := integerProjectiveLinearImage P
  let s := projectivePoints (projectiveIdealZeroLocus I) B
  let t := projectivePoints (projectiveZeroLocus f) ((n + 1 : ℕ) * H * B)
  have hLapply (x : CCDN.RatPoint (n + 1)) (i) :
      L x i = eval x (integerLinearForm (P i)) := by
    aesop
  have hfiniteL (z : CCDN.RatPoint (m + 1)) (u : Finset (CCDN.RatPoint (n + 1)))
      (hu : ∀ x ∈ u, x ∈ idealZeroLocus I) (huz : ∀ x ∈ u, L x = z) :
      u.card ≤ M := by
    apply hfinite z u hu
    intro x hx i
    rw [← hLapply, huz x hx]
  have hnon (x : ProjectivePoint n) (hx : x ∈ projectiveIdealZeroLocus I) :
      L x.rep ≠ 0 :=
    projective_linear_image_ne_zero_of_finite_zero_fiber I L M (hfiniteL 0) x hx
  have hπ (x : ProjectivePoint n) (hx : x ∈ projectiveIdealZeroLocus I) :
      π x = Projectivization.mk ℚ (L x.rep) (hnon x hx) := dite_eq_left (hnon x hx)
  have himage : s.image π ⊆ t := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxB, hxI⟩ := mem_projectivePoints.mp hx
    rw [hπ x hxI]
    apply mem_projectivePoints.mpr
    constructor
    · exact (projective_linear_map_height P hH hP x (hnon x hxI)).trans
        (mul_le_mul_of_nonneg_left hxB (by positivity))
    · rw [mem_projectiveZeroLocus_mk hf]
      have hz := projectiveIdealZeroLocus_rep hxI _ hrelation
      rw [eval_polynomial_coordinate_map] at hz
      have hev :=
        funext (hLapply x.rep)
      rwa [hev]
  have hfib (y : ProjectivePoint m) :
      (s.filter (fun x => π x = y)).card ≤ M := by
    let u := s.filter (fun x => π x = y)
    have hu (x) (hx : x ∈ u) : x ∈ projectiveIdealZeroLocus I :=
      (mem_projectivePoints.mp (Finset.mem_filter.mp hx).1).2
    apply projective_linear_fiber_card_le I L u hu (fun x hx => hnon x (hu x hx))
      y _ M (hfiniteL y.rep)
    intro x hx
    rw [← hπ x (hu x hx)]
    exact (Finset.mem_filter.mp hx).2
  change s.card ≤ M * t.card
  rw [Finset.card_eq_sum_card_image π s]
  calc
    _ ≤ ∑ _y ∈ s.image π, M := Finset.sum_le_sum (fun y _ => hfib y)
    _ = M * (s.image π).card := by simp [Nat.mul_comm]
    _ ≤ M * t.card := Nat.mul_le_mul_left M (Finset.card_le_card himage)

end CCDN
