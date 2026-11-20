/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Plane.FiniteFieldBadPlanes
import CCDN.Algebra.IntegerPolynomialAvoidance
import CCDN.Noether.ShearNormalization

/-!
# Specializations of universal plane sections

Evaluation of a universal section, including the three points obtained from the base point by
adding each direction. A nonzero universal witness certifies a geometrically irreducible plane
section in characteristic zero, and integer specialization can simultaneously avoid any
additional nonzero polynomial condition on the plane parameters.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

variable {K σ : Type*} [CommRing K] (f : MvPolynomial σ K) (v : PlaneParameters σ → K) (x y : K)

/-- Evaluate the outer coordinate at x and the inner coordinate at y. -/
def bivariateEval : Polynomial (Polynomial K) →+* K :=
  (Polynomial.evalRingHom x).comp (Polynomial.mapRingHom (Polynomial.evalRingHom y))

/-- Evaluating the universal plane section of `f` with parameters `v` at `(x, y)` gives `f` at the
point `a + x • b + y • c` of the plane with base point `a` and directions `b`, `c` given by `v`. -/
lemma universalPlaneSection_eval :
    bivariateEval x y (universalPlaneSection f v) =
      eval (fun i => v (i,0) + v (i,1) * x + v (i,2) * y) f := by
  have he : (bivariateEval x y).comp
      ((bivariateMap (eval v)).comp
        ((bivariatePolynomialEquiv _).toRingHom.comp (universalPlaneMap K σ).toRingHom)) =
      eval (fun i => v (i,0) + v (i,1) * x + v (i,2) * y) := by
    apply MvPolynomial.ringHom_ext
    simp [bivariateEval, universalPlaneMap, bivariatePolynomialEquiv_C, bivariateMap]
    · simp [bivariateEval, universalPlaneMap, bivariatePolynomialEquiv_C,
        bivariatePolynomialEquiv_X_zero, bivariatePolynomialEquiv_X_one, bivariateMap]
  exact RingHom.congr_fun he f

/-- The equivalence between plane parameters, a base point `a` with directions `b` and `c`, and
the three defining points `a`, `a + b` and `a + c` of the plane. -/
def planeTriplePointsEquiv :
    (PlaneParameters σ → K) ≃ (Fin 3 → σ → K) where
  toFun v := ![fun i => v (i,0), fun i => v (i,0) + v (i,1), fun i => v (i,0) + v (i,2)]
  invFun w := fun i => ![w 0 i.1, w 1 i.1 - w 0 i.1, w 2 i.1 - w 0 i.1] i.2
  left_inv v := by
    funext i
    rcases i with ⟨i,j⟩
    fin_cases j <;> simp
  right_inv w := by
    funext j i
    fin_cases j <;> simp

/-- A zero section contains all three defining points, including coincident
ones. This does not require the parameterization to be injective. -/
lemma zero_universalPlaneSection_three_points
    (hv : universalPlaneSection f v = 0) (j : Fin 3) :
    eval (planeTriplePointsEquiv v j) f = 0 := by
  have h0 := universalPlaneSection_eval f v 0 0
  have h1 := universalPlaneSection_eval f v 1 0
  have h2 := universalPlaneSection_eval f v 0 1
  rw [hv, map_zero] at h0 h1 h2
  fin_cases j
  · simpa [planeTriplePointsEquiv] using h0.symm
  · simpa [planeTriplePointsEquiv] using h1.symm
  · simpa [planeTriplePointsEquiv] using h2.symm

end
end CCDN
