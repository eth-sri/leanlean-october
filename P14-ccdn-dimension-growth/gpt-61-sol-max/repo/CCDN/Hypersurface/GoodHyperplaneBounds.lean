/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Hypersurface.GraphHyperplaneRestriction
import CCDN.ForMathlib.MvPolynomial
import CCDN.Plane.HyperplanePlaneAvoidance
import CCDN.Plane.IntegerPlaneHeight
import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-!
Constructing a geometrically good rational graph section.
An anchored integer plane and Cramer's rule give a containing rational
hyperplane; the section certifies that the universal avoidance polynomial
is nonzero.
-/

public section
namespace CCDN
open MvPolynomial
local notation "K" => AlgebraicClosure ℚ

/-- A geometrically integral rational graph section, used to certify that the
universal hyperplane avoidance polynomial is nonzero. -/
theorem exists_geometrically_good_graph {n : ℕ}
    (f : MvPolynomial (Option (Fin (3 + n))) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) :
    ∃ α : CCDN.RatPoint (3 + n),
      AbsolutelyIrreducibleRat (graphHyperplaneRestriction α (CCDN.rationalPolynomial f)) := by
  classical
  obtain ⟨v, hminor, hplanedegree, hplaneir⟩ :=
    exists_integer_good_plane_with_anchor f hir hd
  let M : Matrix (Fin 3) (Fin 3) ℤ :=
    Matrix.of (fun i j => v (some (i.castAdd n), j))
  let w : CCDN.IntPoint 3 := fun j => v (none, j)
  let b := M.transpose.cramer w
  have hrelation (j : Fin 3) : ∑ i, b i * M i j = M.det * w j := by
    have hh := Matrix.mulVec_cramer M.transpose w
    rw [Matrix.mulVec_transpose, Matrix.det_transpose] at hh
    simpa only [b, Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] using congrFun hh j
  let D := M.det
  let a : CCDN.IntPoint (3 + n) := Fin.addCases b (fun _ : Fin n => 0)
  have hrel (j : Fin 3) : D * v (none, j) = ∑ i, a i * v (some i, j) := by
    rw [Fin.sum_univ_add]
    simpa only [a, Fin.addCases_left, Fin.addCases_right, zero_mul,
      Finset.sum_const_zero, add_zero, M, w, D, Matrix.of_apply] using (hrelation j).symm
  let α : CCDN.RatPoint (3 + n) := fun i => (a i : ℚ) / D
  let αK : Fin (3 + n) → K := fun i => (a i : K) / D
  let vK : PlaneParameters (Option (Fin (3 + n))) → K := (Int.castRingHom K) ∘ v
  have hDK : (D : K) ≠ 0 := by exact_mod_cast hminor
  have hcontain (j : Fin 3) : vK (none, j) = ∑ i, αK i * vK (some i, j) := by
    have hh : (D : K) * (v (none, j) : K) = ∑ i, (a i : K) * (v (some i, j) : K) := by
      exact_mod_cast hrel j
    change (v (none, j) : K) = ∑ i, ((a i : K) / D) * (v (some i, j) : K)
    calc
      _ = ((D : K) * (v (none, j) : K)) / D := by field_simp [hDK]
      _ = (∑ i, (a i : K) * (v (some i, j) : K)) / D := by rw [hh]
      _ = _ := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hfdegree : (map (Int.castRingHom K) f).totalDegree = f.totalDegree :=
      totalDegree_map_of_injective Int.cast_injective _
  have hsection := universalPlaneSection_map (Int.castRingHom K) f v
  have hgood := graphHyperplaneRestriction_irreducible_of_plane
    (map (Int.castRingHom K) f) αK vK hcontain
    (by aesop)
    (by aesop)
  let φ : ℚ →+* K := algebraMap ℚ K
  have hmapf : map φ (CCDN.rationalPolynomial f) = map (Int.castRingHom K) f := by
    rw [map_map]
    congr 1
  have hα : φ ∘ α = αK := by
    funext i
    simp [φ, α, αK]
  have hmap : map φ (graphHyperplaneRestriction α (CCDN.rationalPolynomial f)) =
      graphHyperplaneRestriction αK (map (Int.castRingHom K) f) := by
    rw [graphHyperplaneRestriction_map, hα, hmapf]
  refine ⟨α, ?_⟩
  grind

end CCDN
