/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Plane.FiniteFieldBadPlanes
import CCDN.Noether.ClosedFormParameterDegree
import CCDN.Noether.UniversalPlaneSpecialization

/-! A geometrically good integer plane whose three parameter columns have
an invertible minor in three selected ambient coordinates. This additional
condition allows a containing rational hyperplane to be constructed. -/

@[expose] public section
namespace CCDN
open MvPolynomial

private noncomputable def planeAnchorMinor (n : ℕ) :
    MvPolynomial (PlaneParameters (Option (Fin (3 + n)))) ℤ :=
  Matrix.det (Matrix.of (fun i j : Fin 3 => X (some (i.castAdd n), j)))

private lemma planeAnchorMinor_eval (n : ℕ)
    (v : PlaneParameters (Option (Fin (3 + n))) → ℤ) :
    eval v (planeAnchorMinor n) =
      Matrix.det (Matrix.of (fun i j : Fin 3 => v (some (i.castAdd n), j))) := by
  simp [planeAnchorMinor, Matrix.det_fin_three]

private lemma planeAnchorMinor_ne_zero (n : ℕ) : planeAnchorMinor n ≠ 0 := by
  let v : PlaneParameters (Option (Fin (3 + n))) → ℤ :=
    fun p => Option.elim p.1 0 (fun i => if i.val = p.2.val then 1 else 0)
  have hv : eval v (planeAnchorMinor n) = 1 := by
    rw [planeAnchorMinor_eval]
    norm_num [v, Matrix.det_fin_three]
  intro hz
  rw [hz, map_zero] at hv
  norm_num at hv

/-- The extra determinant condition costs only three in the integer grid
size. -/
theorem exists_integer_good_plane_with_anchor {n : ℕ}
    (f : MvPolynomial (Option (Fin (3 + n))) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) :
    ∃ v : PlaneParameters (Option (Fin (3 + n))) → ℤ,
      Matrix.det (Matrix.of (fun i j : Fin 3 => v (some (i.castAdd n), j))) ≠ 0 ∧
      bivariateTotalDegree (bivariateMap (Int.castRingHom (AlgebraicClosure ℚ))
        (universalPlaneSection f v)) = f.totalDegree ∧
      Irreducible (bivariateMap (Int.castRingHom (AlgebraicClosure ℚ))
        (universalPlaneSection f v)) := by
  obtain ⟨v, hminor, hgood⟩ := exists_integer_geometrically_good_plane_avoiding
    f hir hd (planeAnchorMinor n) (planeAnchorMinor_ne_zero n)
  exact ⟨v, by simpa [planeAnchorMinor_eval] using hminor, hgood⟩

end CCDN
