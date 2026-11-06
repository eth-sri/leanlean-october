/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Plane.FiniteFieldBadPlanes
import CCDN.Noether.ClosedFormParameterDegree
import CCDN.Noether.UniversalPlaneSpecialization

/-! A bounded geometrically good plane whose three parameter columns have
an invertible minor in three selected ambient coordinates. This additional
condition allows an effective containing hyperplane to be constructed. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The extra determinant condition costs only three in the integer grid
size. -/
theorem exists_integer_good_plane_with_anchor {n : ℕ}
    (f : MvPolynomial (Option (Fin (3 + n))) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) :
    ∃ v : PlaneParameters (Option (Fin (3 + n))) → ℤ,
      (∀ p, 0 ≤ v p ∧ v p ≤ 2 * f.totalDegree ^ 3 + 3) ∧
      Matrix.det (Matrix.of (fun i j : Fin 3 => v (some (i.castAdd n), j))) ≠ 0 ∧
      (bivariateMap (Int.castRingHom (AlgebraicClosure ℚ))
        (universalPlaneSection f v)).natDegree = f.totalDegree ∧
      bivariateTotalDegree (bivariateMap (Int.castRingHom (AlgebraicClosure ℚ))
        (universalPlaneSection f v)) = f.totalDegree ∧
      Irreducible (bivariateMap (Int.castRingHom (AlgebraicClosure ℚ))
        (universalPlaneSection f v)) := by
  let P : MvPolynomial (PlaneParameters (Option (Fin (3 + n)))) ℤ :=
    Matrix.det (Matrix.of (fun i j : Fin 3 => X (some (i.castAdd n), j)))
  have hP_eval (v : PlaneParameters (Option (Fin (3 + n))) → ℤ) :
      eval v P = Matrix.det (Matrix.of (fun i j : Fin 3 => v (some (i.castAdd n), j))) := by
    simp [P, Matrix.det_fin_three]
  have hP_ne : P ≠ 0 := fun hz => by
    let v : PlaneParameters (Option (Fin (3 + n))) → ℤ :=
      fun p => Option.elim p.1 0 (fun i => if i.val = p.2.val then 1 else 0)
    have hv : eval v P = 1 := by rw [hP_eval]; norm_num [v, Matrix.det_fin_three]
    rw [hz, map_zero] at hv
    norm_num at hv
  obtain ⟨v, hv, hminor, hgood⟩ := exists_integer_geometrically_good_plane_avoiding f hir hd P hP_ne
  refine ⟨v, fun p => ⟨(hv p).1, (hv p).2.trans ?_⟩, by simpa only [hP_eval] using hminor, hgood⟩
  have hh := matrix_det_parameterDegree
    (Matrix.of (fun i j : Fin 3 => (X (some (i.castAdd n), j) :
      MvPolynomial (PlaneParameters (Option (Fin (3 + n)))) ℤ))) 1 (by intros; simp)
  exact_mod_cast Nat.add_le_add_left
    (by simpa only [P, Fintype.card_fin, Nat.mul_one] using hh) (2 * f.totalDegree ^ 3)

end
end CCDN
