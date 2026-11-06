/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Hypersurface.GraphHyperplaneRestriction
import CCDN.ForMathlib.MvPolynomial
import CCDN.Plane.HyperplanePlaneAvoidance
import CCDN.Plane.IntegerPlaneHeight
import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-!
Constructing a good rational hyperplane with a bounded integer normal.
The degree-nine bound is a polynomial replacement for the precise avoidance
polynomial in corrected CCDN Lemma 4.3.7.

A bounded integral equation obtained from three independent rows.
Cramer's rule uses row-replacement determinants, so the same elementary
3! T³ bound controls both the coefficients and their common denominator.
-/

namespace CCDN
open MvPolynomial
local notation "K" => AlgebraicClosure ℚ

/-- In at least four variables there is a hyperplane
`D*x₀ = ∑ aᵢ*xᵢ` whose restriction is geometrically irreducible of full
degree. Its integer normal has height polynomial in the degree and is
independent of the coefficient height of the original equation. -/
theorem exists_bounded_geometrically_good_hyperplane {n : ℕ}
    (f : MvPolynomial (Option (Fin (3 + n))) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) :
    ∃ α : Fin (3 + n) → ℚ, AbsolutelyIrreducibleRat (graphHyperplaneRestriction α
        (map (Int.castRingHom ℚ) f)) := by
  obtain ⟨v, hminor, hplanedegree, hplaneir⟩ := exists_integer_geometrically_good_plane_avoiding
    f hir hd (planeAnchorMinor n) (show planeAnchorMinor n ≠ 0 by
        let v : PlaneParameters (Option (Fin (3 + n))) → ℤ :=
          fun p => Option.elim p.1 0 (fun i => if i.val = p.2.val then 1 else 0)
        have hv : eval v (planeAnchorMinor n) = 1 := by
          rw [planeAnchorMinor_eval]
          bound
        grind)
  rw [planeAnchorMinor_eval] at hminor
  let M : Matrix (Fin 3) (Fin 3) ℤ :=
    Matrix.of (fun i j => v (some (i.castAdd n), j))
  let w : Fin 3 → ℤ := fun j => v (none, j)
  let b := M.transpose.cramer w
  have hrelation (j) : ∑ i, b i * M i j = M.det * w j := by
    have hh := Matrix.mulVec_cramer M.transpose w
    rw [Matrix.mulVec_transpose, Matrix.det_transpose] at hh
    simpa [b, Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] using congrFun hh j
  let D := M.det
  let a : Fin (3 + n) → ℤ := Fin.addCases b (fun _ => 0)
  have hrel (j : Fin 3) : D * v (none, j) = ∑ i, a i * v (some i, j) := by
    rw [Fin.sum_univ_add]
    aesop
  let α : Fin (3 + n) → ℚ := fun i => (a i : ℚ) / D
  let αK : Fin (3 + n) → K := fun i => (a i : K) / D
  let vK : PlaneParameters (Option (Fin (3 + n))) → K := (Int.castRingHom K) ∘ v
  have hDK : (D : K) ≠ 0 := mod_cast hminor
  have hcontain (j : Fin 3) : vK (none, j) = ∑ i, αK i * vK (some i, j) := by
    have hh : D * (v (none, j) : K) = ∑ i, (a i : K) * (v (some i, j) : K) := by
      exact_mod_cast hrel j
    change (v (none, j) : K) = ∑ i, ((a i : K) / D) * (v (some i, j) : K)
    calc
      _ = (D * (v (none, j) : K)) / D := by grind
      _ = (∑ i, (a i : K) * (v (some i, j) : K)) / D := by grind
      _ = _ := by
        rw [Finset.sum_div]
        grind
  have hfdegree : (map (Int.castRingHom K) f).totalDegree = f.totalDegree :=
      totalDegree_map_of_injective Int.cast_injective _
  have hsection := universalPlaneSection_map (Int.castRingHom K) f v
  have hgood := graphHyperplaneRestriction_irreducible_of_plane
    (map (Int.castRingHom K) f) αK vK hcontain
    (by grind)
    (by grind)
  let φ : ℚ →+* K := algebraMap ℚ K
  have hmapf : map φ (map (Int.castRingHom ℚ) f) = map (Int.castRingHom K) f := by aesop
  have hα : φ ∘ α = αK := by aesop
  have hmap : map φ (graphHyperplaneRestriction α (map (Int.castRingHom ℚ) f)) =
      graphHyperplaneRestriction αK (map (Int.castRingHom K) f) := by
    rw [graphHyperplaneRestriction_map, hα, hmapf]
  have hmapdegree (g : MvPolynomial (Fin (3 + n)) ℚ) :
      (map φ g).totalDegree = g.totalDegree := totalDegree_map_of_injective φ.injective _
  exact ⟨α, by grind⟩

