/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

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
noncomputable section
open MvPolynomial Matrix

/-- Let `P` be an integer matrix with entries of absolute value at most `H` whose linear forms
satisfy the homogeneous relation `f` modulo `I`. If every affine fiber of the induced map on the
zero locus of `I` has at most `M` points, then the projective rational points of height at most `B`
on the zero locus of `I` number at most `M` times those of height at most `(n + 1) * H * B` on the
projective hypersurface `f = 0`. -/
theorem projective_integer_linear_count_transfer
    {m n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (P : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ)
    (f : MvPolynomial (Fin (m + 1)) ℚ) (hf : f.IsHomogeneous f.totalDegree)
    (hrelation : aeval (fun i => integerLinearForm (P i)) f ∈ I)
    (M : ℕ)
    (hfinite : ∀ z : Fin (m + 1) → ℚ, ∀ s : Finset (Fin (n + 1) → ℚ),
      (∀ x ∈ s, x ∈ idealZeroLocus I) →
      (∀ x ∈ s, ∀ i, eval x (integerLinearForm (P i)) = z i) → s.card ≤ M)
    (H B : ℝ) (hH : 0 ≤ H)
    (hP : ∀ i j, |(P i j : ℝ)| ≤ H) :
    projectiveCount (projectiveIdealZeroLocus I) B ≤
      M * projectiveCount (projectiveZeroLocus f) ((n + 1 : ℕ) * H * B) := by
  classical
  let L := (P.map (Int.castRingHom ℚ)).mulVecLin
  let π (x : ProjectivePoint n) : ProjectivePoint m :=
    if h : L x.rep ≠ 0 then Projectivization.mk ℚ (L x.rep) h
    else Projectivization.mk ℚ (fun _ : Fin (m + 1) => 1) fun hz => one_ne_zero (congrFun hz 0)
  let s := projectivePoints (projectiveIdealZeroLocus I) B
  let t := projectivePoints (projectiveZeroLocus f) ((n + 1 : ℕ) * H * B)
  have hLapply (x : Fin (n + 1) → ℚ) (i) : L x i = eval x (integerLinearForm (P i)) := by
    simp only [L, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
      Int.coe_castRingHom, eval_linearForm]
  have hfiniteL (z : Fin (m + 1) → ℚ) (u : Finset (Fin (n + 1) → ℚ))
      (hu : ∀ x ∈ u, x ∈ idealZeroLocus I) (huz : ∀ x ∈ u, L x = z) : u.card ≤ M :=
    hfinite z u hu fun x hx i => by rw [← hLapply, huz x hx]
  have hnon (x : ProjectivePoint n) (hx : x ∈ projectiveIdealZeroLocus I) : L x.rep ≠ 0 :=
    projective_linear_image_ne_zero_of_finite_zero_fiber I L M (hfiniteL 0) x hx
  have hπ (x : ProjectivePoint n) (hx : x ∈ projectiveIdealZeroLocus I) :
      π x = Projectivization.mk ℚ (L x.rep) (hnon x hx) := dite_eq_left (hnon x hx)
  have himage : s.image π ⊆ t := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxB, hxI⟩ := mem_projectivePoints.mp hx
    rw [hπ x hxI]
    refine mem_projectivePoints.mpr
      ⟨(projective_linear_map_height P hH hP x (hnon x hxI)).trans
        (mul_le_mul_of_nonneg_left hxB (by positivity)), ?_⟩
    rw [mem_projectiveZeroLocus_mk hf, funext (hLapply x.rep)]
    have hz := projectiveIdealZeroLocus_rep hxI _ hrelation
    rwa [eval_polynomial_coordinate_map] at hz
  have hfib (y : ProjectivePoint m) : (s.filter (fun x => π x = y)).card ≤ M := by
    let u := s.filter (fun x => π x = y)
    have hu (x) (hx : x ∈ u) : x ∈ projectiveIdealZeroLocus I :=
      (mem_projectivePoints.mp (Finset.mem_filter.mp hx).1).2
    exact projective_linear_fiber_card_le I L u hu (fun x hx => hnon x (hu x hx))
      y (fun x hx => (hπ x (hu x hx)).symm.trans (Finset.mem_filter.mp hx).2) M (hfiniteL y.rep)
  change s.card ≤ M * t.card
  rw [Finset.card_eq_sum_card_image π s]
  exact (Finset.sum_le_sum fun y _ => hfib y).trans
    ((by simp [Nat.mul_comm] : (∑ _y ∈ s.image π, M) = M * (s.image π).card).trans_le
      (Nat.mul_le_mul_left M (Finset.card_le_card himage)))

end
end CCDN
