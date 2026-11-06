/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hypersurface.GraphHyperplaneRestriction
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

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
local notation "K" => AlgebraicClosure ℚ

/-- The height bound `6 * (2 * d ^ 3 + 3) ^ 3` for the integer normal of a good hyperplane
section of a degree-`d` hypersurface. -/
def goodHyperplaneHeight (d : ℕ) : ℕ := 6 * (2 * d ^ 3 + 3) ^ 3

/-- In at least four variables there is a hyperplane
`D*x₀ = ∑ aᵢ*xᵢ` whose restriction is geometrically irreducible of full
degree. Its integer normal has height polynomial in the degree and is
independent of the coefficient height of the original equation. -/
theorem exists_bounded_geometrically_good_hyperplane {n : ℕ}
    (f : MvPolynomial (Option (Fin (3 + n))) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) :
    ∃ (D : ℤ) (a : Fin (3 + n) → ℤ),
      D ≠ 0 ∧ |D| ≤ (goodHyperplaneHeight f.totalDegree : ℤ) ∧
      (∀ i, |a i| ≤ (goodHyperplaneHeight f.totalDegree : ℤ)) ∧
      (graphHyperplaneRestriction (fun i => (a i : ℚ) / D)
        (map (Int.castRingHom ℚ) f)).totalDegree = f.totalDegree ∧
      AbsolutelyIrreducibleRat (graphHyperplaneRestriction (fun i => (a i : ℚ) / D)
        (map (Int.castRingHom ℚ) f)) := by
  classical
  let T := 2 * f.totalDegree ^ 3 + 3
  have hdet3 (A : Matrix (Fin 3) (Fin 3) ℤ) (hA : ∀ i j, |A i j| ≤ (T : ℤ)) :
      |A.det| ≤ (goodHyperplaneHeight f.totalDegree : ℤ) := by
    have hh := Matrix.det_le (abv := AbsoluteValue.abs) hA
    simpa only [goodHyperplaneHeight, T, AbsoluteValue.abs_apply, Fintype.card_fin,
      Nat.factorial_succ, Nat.factorial_zero, Nat.reduceAdd, Nat.reduceMul, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hh
  obtain ⟨v, hv, hD, _, hplanedegree, hplaneir⟩ :=
    exists_integer_good_plane_with_anchor f hir hd
  let M : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of fun i j => v (some (i.castAdd n), j)
  let w : Fin 3 → ℤ := fun j => v (none, j)
  have hvT (p : PlaneParameters (Option (Fin (3 + n)))) : |v p| ≤ (T : ℤ) := by
    rw [abs_of_nonneg (hv p).1]
    simpa only [T, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using (hv p).2
  let b := M.transpose.cramer w
  let D := M.det
  let a : Fin (3 + n) → ℤ := Fin.addCases b (fun _ : Fin n => 0)
  have hrel (j : Fin 3) : D * v (none, j) = ∑ i, a i * v (some i, j) := by
    have hh := Matrix.mulVec_cramer M.transpose w
    rw [Matrix.mulVec_transpose, Matrix.det_transpose] at hh
    rw [Fin.sum_univ_add]
    simpa only [a, b, Fin.addCases_left, Fin.addCases_right, zero_mul, Finset.sum_const_zero,
      add_zero, M, w, D, Matrix.of_apply, Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul]
      using (congrFun hh j).symm
  have haheight : ∀ i, |a i| ≤ (goodHyperplaneHeight f.totalDegree : ℤ) :=
    Fin.addCases
      (fun i => by
        simp only [a, b, Fin.addCases_left, Matrix.cramer_transpose_apply]
        refine hdet3 (M.updateRow i w) fun j k => ?_
        by_cases hji : j = i
        · subst j; simpa [w] using hvT (none, k)
        · rw [Matrix.updateRow_ne hji]; exact hvT _)
      (fun _ => by simp [a, Nat.cast_nonneg])
  let α : Fin (3 + n) → ℚ := fun i => (a i : ℚ) / D
  let αK : Fin (3 + n) → K := fun i => (a i : K) / D
  let vK : PlaneParameters (Option (Fin (3 + n))) → K := (Int.castRingHom K) ∘ v
  have hDK : (D : K) ≠ 0 := mod_cast hD
  have hcontain (j : Fin 3) : vK (none, j) = ∑ i, αK i * vK (some i, j) := by
    have hh : (D : K) * (v (none, j) : K) = ∑ i, (a i : K) * (v (some i, j) : K) :=
      mod_cast hrel j
    change (v (none, j) : K) = ∑ i, ((a i : K) / D) * (v (some i, j) : K)
    rw [show (v (none, j) : K) = ((D : K) * (v (none, j) : K)) / D by field_simp [hDK],
      hh, Finset.sum_div]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hfdegree : (map (Int.castRingHom K) f).totalDegree = f.totalDegree :=
    totalDegree_map_of_injective Int.cast_injective _
  have hsection := universalPlaneSection_map (Int.castRingHom K) f v
  have hgood := graphHyperplaneRestriction_irreducible_of_plane
    (map (Int.castRingHom K) f) αK vK hcontain
    (by simpa only [vK, hsection] using hplaneir)
    (by simpa only [vK, hsection, hfdegree] using hplanedegree)
  let φ : ℚ →+* K := algebraMap ℚ K
  have hmap : map φ (graphHyperplaneRestriction α (map (Int.castRingHom ℚ) f)) =
      graphHyperplaneRestriction αK (map (Int.castRingHom K) f) := by
    rw [graphHyperplaneRestriction_map, show φ ∘ α = αK from funext fun _ => by simp [φ, α, αK],
      map_map]
    rfl
  refine ⟨D, a, hD, hdet3 M fun i j => hvT _, haheight, ?_, ?_⟩
  · rw [← totalDegree_map_of_injective φ.injective _, hmap, hgood.1, hfdegree]
  · change Irreducible (map φ (graphHyperplaneRestriction α (map (Int.castRingHom ℚ) f)))
    rw [hmap]; exact hgood.2

end
end CCDN
