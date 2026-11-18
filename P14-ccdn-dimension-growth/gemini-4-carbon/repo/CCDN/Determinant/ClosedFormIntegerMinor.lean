/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.ClosedFormBaseChange

/-! A nonzero integer minor of the closed-form coefficient matrix.
Rank drop after reduction forces divisibility of this same integer. The
geometric rank-drop criterion and the height bound are separate obligations. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Matrix

/-- Determinants of selected coefficient minors commute with any coefficient
ring map. -/
theorem closedForm_minor_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (d r : ℕ) (f : R[X][X])
    (a : Fin r → ℕ × ℕ) (c : Fin r → ClosedFormColumns d) :
    φ (((closedFormCoefficientMatrix d f).submatrix a c).det) =
      ((closedFormCoefficientMatrix d (bivariateMap φ f)).submatrix a c).det := by
  rw [φ.map_det]
  change (((closedFormCoefficientMatrix d f).map φ).submatrix a c).det = _
  rw [closedFormCoefficientMatrix_map]

end
end CCDN
