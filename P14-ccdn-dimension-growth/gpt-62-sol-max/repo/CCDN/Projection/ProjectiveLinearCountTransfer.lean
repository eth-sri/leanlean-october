/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.IntegerLinearForms
public import CCDN.Algebra.ProjectiveSection
public import CCDN.Height.ProjectiveZeroLocus
public import CCDN.Height.ProjectiveBox
import CCDN.Algebra.ProjectiveFiniteFibers
import CCDN.ForMathlib.MvPolynomial
import CCDN.Projection.BoundedLinearProjection

/-! Height and cardinality transport through an integer linear
projection with uniformly bounded affine fibers. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

private def integerProjectiveLinearImage {m n : ℕ}
    (P : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ) (x : ProjectivePoint n) :
    ProjectivePoint m :=
  if h : (P.map (Int.castRingHom ℚ)) *ᵥ x.rep ≠ 0 then
    Projectivization.mk ℚ ((P.map (Int.castRingHom ℚ)) *ᵥ x.rep) h
  else
    Projectivization.mk ℚ (fun _ : Fin (m + 1) => 1) (by
      intro hz
      have hh := congrFun hz 0
      exact one_ne_zero hh)

/-- Transfer the count of points away from a homogeneous section `g = 0` through an integer
linear matrix. A finite zero fiber excludes base points; fibers away from the section cost `M`. -/
theorem projective_integer_linear_count_transfer
    {m n e : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (P : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ)
    (f : MvPolynomial (Fin (m + 1)) ℚ) (hf : f.IsHomogeneous f.totalDegree)
    (hrelation : aeval (fun i => integerLinearForm (P i)) f ∈ I)
    (g : MvPolynomial (Fin (n + 1)) ℚ) (hg : g.IsHomogeneous e)
    (M₀ M : ℕ)
    (hzero : ∀ s : Finset (Fin (n + 1) → ℚ),
      (∀ x ∈ s, x ∈ idealZeroLocus I) →
      (∀ x ∈ s, ∀ i, eval x (integerLinearForm (P i)) = 0) → s.card ≤ M₀)
    (hfinite : ∀ z : Fin (m + 1) → ℚ, ∀ s : Finset (Fin (n + 1) → ℚ),
      (∀ x ∈ s, x ∈ idealZeroLocus I) →
      (∀ x ∈ s, eval x g ≠ 0) →
      (∀ x ∈ s, ∀ i, eval x (integerLinearForm (P i)) = z i) → s.card ≤ M)
    (H B : ℝ) (hH : 0 ≤ H)
    (hP : ∀ i j, |(P i j : ℝ)| ≤ H) :
    ((projectivePoints (projectiveIdealZeroLocus I) B).filter (fun x => eval x.rep g ≠ 0)).card ≤
      M * projectiveCount (projectiveZeroLocus f) ((n + 1 : ℕ) * H * B) := by
  classical
  let L := (P.map (Int.castRingHom ℚ)).mulVecLin
  let π := integerProjectiveLinearImage P
  let s := (projectivePoints (projectiveIdealZeroLocus I) B).filter (fun x => eval x.rep g ≠ 0)
  let t := projectivePoints (projectiveZeroLocus f) ((n + 1 : ℕ) * H * B)
  have hLapply (x : Fin (n + 1) → ℚ) (i) :
      L x i = eval x (integerLinearForm (P i)) := congrFun (integer_mulVec_eq_eval P x) i
  have hfiber (z : Fin (m + 1) → ℚ) (u : Finset (Fin (n + 1) → ℚ))
      (huz : ∀ x ∈ u, L x = z) (x) (hx : x ∈ u) (i) :
      eval x (integerLinearForm (P i)) = z i := by rw [← hLapply, huz x hx]
  have hnon (x : ProjectivePoint n) (hx : x ∈ projectiveIdealZeroLocus I) :=
    projective_linear_image_ne_zero_of_finite_zero_fiber I L M₀
      (fun u hu hz => hzero u hu (hfiber 0 u hz)) x hx
  have hπ (x : ProjectivePoint n) (hx : x ∈ projectiveIdealZeroLocus I) :
      π x = Projectivization.mk ℚ (L x.rep) (hnon x hx) := by
    exact dite_eq_left (hnon x hx)
  have himage (x) (hx : x ∈ s) : π x ∈ t := by
    obtain ⟨hxB, hxI⟩ := mem_projectivePoints.mp (Finset.mem_filter.mp hx).1
    rw [hπ x hxI]
    apply mem_projectivePoints.mpr
    constructor
    · exact (projective_linear_map_height P hH hP x (hnon x hxI)).trans
        (mul_le_mul_of_nonneg_left hxB (by positivity))
    · rw [mem_projectiveZeroLocus_mk hf]
      have hz := projectiveIdealZeroLocus_rep hxI _ hrelation
      rw [eval_polynomial_coordinate_map] at hz
      rwa [(funext (hLapply x.rep))]
  have hfib (y : ProjectivePoint m) :
      (s.filter (fun x => π x = y)).card ≤ M := by
    let u := s.filter (fun x => π x = y)
    have hsu (x) (hx : x ∈ u) := Finset.mem_filter.mp (Finset.mem_filter.mp hx).1
    have hu (x) (hx : x ∈ u) := (mem_projectivePoints.mp (hsu x hx).1).2
    apply projective_linear_fiber_card_le {v | v ∈ idealZeroLocus I ∧ eval v g ≠ 0}
      L u ?_ (fun x hx => hnon x (hu x hx)) y ?_ M
      (fun v hv hz => hfinite y.rep v (fun w hw => (hv w hw).1) (fun w hw => (hv w hw).2) (hfiber _ _ hz))
    · intro x hx v hv he
      exact ⟨hu x hx v hv he, fun hz => (hsu x hx).2
        ((homogeneous_eval_zero_iff_projective_eq hg hv x.rep_nonzero (he.trans x.mk_rep.symm)).mp hz)⟩
    · intro x hx
      rw [← hπ x (hu x hx)]
      exact (Finset.mem_filter.mp hx).2
  exact Finset.card_le_mul_card_image_of_maps_to himage M (fun y _ => hfib y)

end
end CCDN
