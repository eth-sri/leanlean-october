/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hypersurface.GraphHyperplaneRestriction
import CCDN.Algebra.IntegerPolynomialAvoidance
import CCDN.Noether.UniversalPlaneBadWitness
import CCDN.Plane.IntegerPlaneHeight
import CCDN.Determinant.PlaneMultiplicity
import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Cubic-height integral graph sections from the plane-section witness. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
local notation "K" => AlgebraicClosure ℚ

/-- The plane-parameter minor of the first three projected coordinates. -/
private def anchor (n : ℕ) : MvPolynomial (PlaneParameters (Option (Fin (3 + n)))) ℤ :=
  (Matrix.of fun j i : Fin 3 => X (some (i.castAdd n), j)).det

private lemma anchor_ne_zero (n : ℕ) : anchor n ≠ 0 := by
  let v : PlaneParameters (Option (Fin (3 + n))) → ℤ :=
    fun (i, j) => i.elim 0 fun k => if k.val = j.val then 1 else 0
  have hv : eval v (anchor n) = 1 := by
    rw [anchor, RingHom.map_det]
    simp only [Matrix.det_fin_three, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, eval_X, v, Option.elim_some, Fin.val_castAdd]
    norm_num
  aesop

/-- On a graph with variable slopes, fix the projected plane and solve for its missing row. -/
private def graphPlane {σ : Type*} [Fintype σ] (v : PlaneParameters (Option σ) → ℤ) :
    PlaneParameters (Option σ) → MvPolynomial σ ℤ
  | (none, j) => ∑ i, C (v (some i, j)) * X i
  | (some i, j) => C (v (some i, j))

private lemma graphPlane_degree {σ : Type*} [Fintype σ]
    (v : PlaneParameters (Option σ) → ℤ) (p : PlaneParameters (Option σ)) :
    (graphPlane v p).totalDegree ≤ 1 := by
  rcases p with ⟨_ | _, j⟩
  · exact totalDegree_finsetSum_le fun i _ =>
      (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X, zero_add])
  · exact (totalDegree_C _).le.trans (Nat.zero_le _)

private lemma graphPlane_specialize {σ R : Type*} [Fintype σ] [CommRing R]
    (v : PlaneParameters (Option σ) → ℤ) (a : σ → R)
    (W : MvPolynomial (PlaneParameters (Option σ)) ℤ) :
    eval₂Hom (Int.castRingHom R) a (eval₂Hom C (graphPlane v) W) =
      eval₂Hom (Int.castRingHom R) (fun p => Option.elim p.1
        (∑ i, a i * (v (some i, p.2) : R)) (fun i => v (some i, p.2))) W := by
  rw [map_eval₂Hom]
  congr 1
  apply MvPolynomial.ringHom_ext
  · simp
  · rintro ⟨_ | _, j⟩ <;>
      simp only [eval₂Hom_X', graphPlane, Option.elim_none, Option.elim_some,
        map_sum, map_mul, eval₂Hom_C, Int.coe_castRingHom, mul_comm]

private lemma exists_graph_of_anchor {n : ℕ}
    (v : PlaneParameters (Option (Fin (3 + n))) → ℤ) (hv : eval v (anchor n) ≠ 0) :
    ∃ a : Fin (3 + n) → K, ∀ j, (v (none, j) : K) = ∑ i, a i * (v (some i, j) : K) := by
  let M : Matrix (Fin 3) (Fin 3) K := Matrix.of fun j i => v (some (i.castAdd n), j)
  have hM : M.det ≠ 0 := by
    have h : ((Int.castRingHom K).comp (eval v)) (anchor n) ≠ 0 :=
      by simpa using (Int.cast_injective (α := K)).ne hv
    rw [anchor, RingHom.map_det] at h
    convert h using 2
    ext j i; simp [M]
  obtain ⟨b, hb⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hM)) (fun j => (v (none, j) : K))
  refine ⟨Fin.addCases b 0, fun j => ?_⟩
  rw [Fin.sum_univ_add]
  simpa only [Fin.addCases_left, Fin.addCases_right, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    add_zero, Matrix.mulVec, dotProduct, M, Matrix.of_apply, mul_comm] using (congrFun hb j).symm

/-- A cubic bound for the slopes of an integral graph with geometrically integral restriction.
Specialize a plane witness to the planes contained in the graphs. The anchor minor guarantees the
specialization is nonzero, since the anchored plane lies in a graph over the algebraic closure. -/
theorem exists_good_integer_graph {n : ℕ} (f : MvPolynomial (Option (Fin (3 + n))) ℤ)
    (hir : AbsolutelyIrreducible f) (hd : 0 < f.totalDegree) :
    ∃ a : Fin (3 + n) → ℤ, (∀ i, |a i| ≤ (2 * f.totalDegree ^ 3 : ℕ)) ∧
      AbsolutelyIrreducible (graphHyperplaneRestriction a f) := by
  obtain ⟨rows, cols, hW, hdeg⟩ := exists_universalPlane_badWitness f _ Int.cast_injective hir hd (.of_charZero _)
  let W := universalPlaneBadWitness f rows cols
  let P := W * anchor n
  obtain ⟨v, _, hv⟩ := exists_integer_grid_eval_ne_zero P (mul_ne_zero hW (anchor_ne_zero n)) _ le_rfl
  have hv' : eval v W ≠ 0 ∧ eval v (anchor n) ≠ 0 := by simpa [P] using hv
  obtain ⟨s, hs⟩ := exists_graph_of_anchor v hv'.2
  let H := eval₂Hom C (graphPlane v) W
  have hH : H ≠ 0 := by
    have he : eval₂Hom (Int.castRingHom K) s H = (eval v W : K) := by
      change _ = Int.castRingHom K (eval₂Hom (RingHom.id ℤ) v W)
      rw [graphPlane_specialize, map_eval₂Hom]
      simp only [RingHom.comp_id]
      congr 1
      apply MvPolynomial.ringHom_ext
      · simp
      · rintro ⟨_ | _, j⟩ <;> simp [← hs]
    intro hz
    rw [hz, map_zero] at he
    exact hv'.1 (by exact_mod_cast he.symm)
  obtain ⟨a, ha, hval⟩ := exists_integer_grid_eval_ne_zero H hH _ ((linear_eval₂_totalDegree_le (RingHom.id ℤ) _ (graphPlane_degree v) W).trans hdeg)
  let v' : PlaneParameters (Option (Fin (3 + n))) → ℤ := fun p => Option.elim p.1
    (∑ i, a i * v (some i, p.2)) (fun i => v (some i, p.2))
  have hv'W : eval v' W ≠ 0 := by
    have he := graphPlane_specialize v a W
    rw [Int.castRingHom_int] at he
    change eval a H = eval v' W at he
    exact he ▸ hval
  let φ := Int.castRingHom K
  have hgood := universalPlaneBadWitness_good_specialization f hd (.of_charZero _) rows cols
    (φ.comp (eval v')) (by simpa [φ] using (Int.cast_injective (α := K)).ne hv'W)
  have hplane : bivariateMap (φ.comp (eval v')) (universalPlanePolynomial f) =
      universalPlaneSection (map φ f) (φ ∘ v') := by
    rw [universalPlaneSection_map, universalPlaneSection, bivariateMap_comp_apply]
  rw [hplane] at hgood
  have hcontain (j : Fin 3) : (φ ∘ v') (none, j) = ∑ i, (φ ∘ a) i * (φ ∘ v') (some i, j) := by
    simp [v']
  refine ⟨a, fun i => by simpa [abs_of_nonneg (ha i).1] using (ha i).2, ?_⟩
  have hfdeg : (map φ f).totalDegree = f.totalDegree := totalDegree_map_of_injective (Int.cast_injective (α := K)) f
  have hh := graphHyperplaneRestriction_irreducible_of_plane (map φ f) (φ ∘ a) (φ ∘ v')
    hcontain hgood.2 (hgood.1.trans hfdeg.symm)
  simpa only [AbsolutelyIrreducible, graphHyperplaneRestriction_map] using hh.2

end
end CCDN
