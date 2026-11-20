module
public import Glennie.Compact.Affine20.Relabel
meta import Glennie.Compact.Affine20.Relabel
public import Glennie.ExactCoordinates
meta import Glennie.ExactCoordinates
public import Glennie.MatrixCertificate
meta import Glennie.MatrixCertificate
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic.Eval
@[expose] public section
namespace Glennie.SubmissionR03

/-- The same 27 fixed bracketed words evaluated in any marked product. -/
def wordValues {E : Type*} (e : E) (a : Fin 3 → E)
    (j : E → E → E) : Fin 27 → E :=
  let x := a f0
  let y := a f1
  let z := a f2
  let xx := j x x
  let xy := j x y
  let xz := j x z
  let yy := j y y
  let yz := j y z
  let zz := j z z
  ![e, x, y, z, xx, xy, xz, yy, yz, zz,
    j x xy, j x xz, j x yy, j x yz, j x zz,
    j y xz, j y yz, j y zz,
    j xx yy, j xx yz, j xx zz, j xy yz, j xy zz, j yy zz,
    j x (j y xz), j x (j y yz), j x (j y zz)]
noncomputable def nativeWordValues : Fin 27 → Albert := wordValues 1 nativeMarks jordan

variable {A E : Type*} in
theorem map_wordValues (f : A → E) (j : A → A → A) (k : E → E → E)
    (h : ∀ x y, f (j x y) = k (f x) (f y)) (e : A) (a : Fin 3 → A) (i : Fin 27) :
    f (wordValues e a j i) = wordValues (f e) (fun r => f (a r)) k i := by
  fin_cases i <;> simp [wordValues, h]

end Glennie.SubmissionR03

namespace Glennie.Compact.NativeWordTableR01
open Glennie ExactCoordinates Module SubmissionR03
open scoped BigOperators Matrix

private noncomputable abbrev coef := Rat.castHom ℝ
def rationalWords : Fin 27 → Coords ℚ := wordValues 1 (marks ℚ) (product (1/2))

private theorem realize_word (i : Fin 27) : realize coef (rationalWords i) = nativeWordValues i := by
  rw [rationalWords, map_wordValues _ _ _ (realize_product coef (1/2) (by norm_num)), realize_one]
  simp [nativeWordValues, realize_marks]

def Q : Matrix (Fin 27) (Fin 27) ℚ := fun i j => coords (rationalWords j) i

-- Check the certificate over the rationals before transporting it to ℝ.
private def Qdata : Matrix (Fin 27) (Fin 27) ℚ :=
  MatrixCertificate.ofRows (eval%
    let words := Array.ofFn rationalWords
    Array.ofFn fun i => words.map (coords · i))

private def B : Matrix (Fin 27) (Fin 27) ℚ :=
  MatrixCertificate.ofRows (eval% MatrixCertificate.inverseCandidateRows Inv.inv Qdata)

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 20000 in
private theorem Q_inv : Q * B = 1 := by
  have h : Q = Qdata := MatrixCertificate.eq_of_check _ _ (by decide +kernel)
  rw [h]
  exact MatrixCertificate.eq_of_check _ _ (by decide +kernel)

theorem det_Q_cast : IsUnit (Q.map (Rat.castHom ℝ)).det := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact IsUnit.map _ (isUnit_iff_ne_zero.mpr (MatrixCertificate.det_ne_zero_of_inverse Q_inv))

noncomputable def wordCoordinates : Albert ≃ₗ[ℝ] (Fin 27 → ℝ) :=
  flattened.trans ((Q.map (Rat.castHom ℝ)).toLinearEquiv' (Matrix.invertibleOfIsUnitDet _ det_Q_cast)).symm

noncomputable def wordBasis : Basis (Fin 27) ℝ Albert := Basis.ofEquivFun wordCoordinates

theorem wordBasis_eq_nativeWordValues (i : Fin 27) : wordBasis i = nativeWordValues i := by
  rw [show wordBasis i = wordCoordinates.symm (Pi.single i 1) from
    congrFun (Basis.coe_ofEquivFun wordCoordinates) i]
  apply flattened.injective
  rw [wordCoordinates, LinearEquiv.symm_trans_apply, LinearEquiv.apply_symm_apply]
  change (Q.map coef) *ᵥ Pi.single i 1 = flattened (nativeWordValues i)
  rw [Matrix.mulVec_single_one]
  funext k
  rw [← realize_word, flattened_realize]
  rfl

end Glennie.Compact.NativeWordTableR01
