/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Algebra.Equations
public import CCDN.Hypersurface.GraphHyperplaneRestriction
public import CCDN.Algebra.PolynomialPredicates
import CCDN.Algebra.LinearForm
import CCDN.Algebra.IntegerPolynomialAvoidance
import CCDN.Algebra.OriginShift
import CCDN.Plane.IntegerPlaneHeight
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! A good hyperplane of cubic height, found by interpolating the plane witness directly in graph coordinates. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Center the interpolation grid, halving the bound on its absolute radius. -/
private lemma centered_grid {σ : Type*} [Finite σ] {f : MvPolynomial σ ℚ} (hf : f ≠ 0)
    {D : ℕ} (hd : f.totalDegree ≤ 2 * D) :
    ∃ a : σ → ℤ, (∀ i, |a i| ≤ D) ∧ eval (fun i => (a i : ℚ)) f ≠ 0 := by
  let u := fun _ : σ => -(D : ℚ)
  obtain ⟨v, hv, h⟩ := exists_integer_grid_eval_ne_zero_of_totalDegree _ (originShift_ne_zero u hf)
    _ ((originShift_totalDegree_le u f).trans hd)
  refine ⟨fun i => v i - D, fun i => by grind, ?_⟩
  simpa [originShift, ← eval_assoc, Function.comp_def, u, sub_eq_add_neg] using h

section

variable (n : ℕ)

private abbrev Coordinates := Fin (3 + n)
private abbrev Parameters := PlaneParameters (Option (Coordinates n))

end

/-- Any nonvanishing plane-parameter condition of degree at most `2*D`
can be achieved on a plane contained in a graph with integral slopes of size `D`.
Fix a good plane with the first three remaining rows independent, and vary its
first row as a linear combination of those rows. The condition stays nonzero and
its degree in the combination coefficients has not increased. -/
private lemma exists_plane_on_small_graph {n D : ℕ} (W : MvPolynomial (Parameters n) ℚ)
    (hW : W ≠ 0) (hdeg : W.totalDegree ≤ 2 * D) :
    ∃ (a : Coordinates n → ℤ) (v : Parameters n → ℚ),
      (∀ i, |a i| ≤ D) ∧ eval v W ≠ 0 ∧ ∀ j, v (none, j) = ∑ i, (a i : ℚ) * v (some i, j) := by
  classical
  let A : MvPolynomial (Parameters n) ℚ :=
    (Matrix.of fun i j : Fin 3 => X (some (i.castAdd n), j)).det
  have hA : A ≠ 0 := by
    intro h
    let u (p : Parameters n) : ℚ := Option.elim p.1 0 fun i => if i.val = p.2.val then 1 else 0
    have := congrArg (eval u) h
    norm_num [A, u, Matrix.det_fin_three] at this
    exact this rfl
  obtain ⟨w, hw⟩ : ∃ w, eval w (W * A) ≠ 0 := by
    by_contra! hn
    exact mul_ne_zero hW hA (MvPolynomial.funext (by simpa using hn))
  rw [map_mul, mul_ne_zero_iff] at hw
  let M := Matrix.of fun i j : Fin 3 => w (some (i.castAdd n), j)
  have hm := M.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr (by
    simpa [A, M, Matrix.det_fin_three] using hw.2))
  obtain ⟨b, hb⟩ := (Matrix.vecMul_surjective_iff_isUnit.mpr hm) (fun j => w (none, j))
  let u : Parameters n → CoordinatePolynomial 3 := fun (i, j) =>
    i.elim (linearForm fun k : Fin 3 => w (some (k.castAdd n), j)) (fun l => C (w (some l, j)))
  have hub : eval b ∘ u = w := by
    funext ⟨i, j⟩
    cases i with
    | none => simpa [u, M, Matrix.vecMul, dotProduct, mul_comm] using congrFun hb j
    | some i => simp [u]
  have hP : (eval₂Hom C u W) ≠ 0 := by
    intro h
    apply hw.1
    rw [← hub, eval_assoc]; simp_all
  have hPd := by
    apply linear_eval₂_totalDegree_le (RingHom.id ℚ) u _ W
    rintro ⟨_ | i, j⟩
    · exact linearForm_totalDegree_le _
    · simp [u]
  obtain ⟨a, ha, haW⟩ := centered_grid hP (hPd.trans hdeg)
  let z : Coordinates n → ℤ := Fin.addCases a (fun _ => 0)
  refine ⟨z, eval (fun i => (a i : ℚ)) ∘ u, Fin.addCases (by simpa [z] using ha) (by simp [z]), ?_, ?_⟩
  · rwa [eval_assoc]
  simp [u, z, Fin.sum_univ_add, mul_comm]

/-- A graph with bounded integral slopes whose restriction is geometrically irreducible. -/
theorem exists_geometrically_good_hyperplane {n : ℕ} (f : MvPolynomial (Option (Fin (3 + n))) ℤ)
    (hd : 0 < f.totalDegree) (hir : AbsolutelyIrreducible f) :
    ∃ a : Fin (3 + n) → ℤ, (∀ i, |a i| ≤ (f.totalDegree ^ 3 : ℕ)) ∧
      AbsolutelyIrreducible (graphHyperplaneRestriction a f) := by
  let q := rationalEquation f
  let φ := algebraMap ℚ (AlgebraicClosure ℚ)
  have hqd : q.totalDegree = f.totalDegree := rational_map_totalDegree _
  have hdpos := hqd ▸ hd
  obtain ⟨rows, cols, hw, hdeg⟩ := exists_universalPlane_badWitness q ((absolutelyIrreducibleRat_map_iff _).mpr hir) hdpos (.of_charZero _)
  obtain ⟨a, v, ha, hwv, hrel⟩ := exists_plane_on_small_graph _ hw hdeg
  have hh := universalPlaneBadWitness_good_specialization q hdpos (.of_charZero _) rows cols
    (φ.comp (eval v)) (by aesop)
  let α := fun i => (a i : ℚ)
  have hg := graphHyperplaneRestriction_irreducible_of_plane (map φ q) (φ ∘ α) (φ ∘ v)
    (by simp_all [α])
    (by rw [universalPlaneSection_map, universalPlaneSection, ← bivariateMap_comp_apply]; exact hh.2.2)
    (by rw [universalPlaneSection_map, universalPlaneSection, ← bivariateMap_comp_apply,
      totalDegree_map_of_injective φ.injective]; exact hh.2.1)
  refine ⟨a, hqd ▸ ha, ?_⟩
  rw [AbsolutelyIrreducible, graphHyperplaneRestriction_map]
  have he : map φ q = map (Int.castRingHom _) f := by
    rw [show q = q from rfl, map_map, RingHom.ext_int (φ.comp _)]
  simpa [he, α, Function.comp_def] using hg.2

end
end CCDN
