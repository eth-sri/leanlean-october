/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.PolynomialPredicates
import CCDN.Plane.FiniteFieldBadPlanes
import CCDN.Noether.ClosedFormParameterDegree
import CCDN.Noether.UniversalPlaneSpecialization

/-! A bounded geometrically good plane whose three parameter columns have
an invertible minor in three selected ambient coordinates. This additional
condition allows an effective containing hyperplane to be constructed. -/

namespace CCDN
noncomputable section
open MvPolynomial

section
variable (n : ℕ)

def planeAnchorMinor :
    MvPolynomial (PlaneParameters (Option (Fin (3 + n)))) ℤ :=
  Matrix.det (Matrix.of (fun i j : Fin 3 => X (some (i.castAdd n), j)))

lemma planeAnchorMinor_eval
    (v : PlaneParameters (Option (Fin (3 + n))) → ℤ) :
    eval v (planeAnchorMinor n) =
      Matrix.det (Matrix.of (fun i j : Fin 3 => v (some (i.castAdd n), j))) := by
  simp [planeAnchorMinor, Matrix.det_fin_three]

end

