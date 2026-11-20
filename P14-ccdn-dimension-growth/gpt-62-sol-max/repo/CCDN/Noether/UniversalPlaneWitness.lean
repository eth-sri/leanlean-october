/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.AffineLineLeading
public import CCDN.Algebra.CharZeroOrGT
public import CCDN.Noether.UniversalPlane
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import CCDN.Determinant.ClosedFormIntegerMinor
import CCDN.Determinant.UniversalPlaneMinor
import CCDN.ForMathlib.MvPolynomial
import CCDN.Noether.ClosedFormParameterDegree
import CCDN.Noether.ShearNormalization
import Mathlib.Algebra.MvPolynomial.Funext

/-!
The leading coefficient of a universal plane section detects loss of the full outer
degree, and specializes to the highest homogeneous form evaluated in the first direction.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

section

variable {K L σ : Type*} [CommRing K] [CommRing L]
  (φ : K →+* L) (f : MvPolynomial σ K)
include K L σ φ f

private lemma universalPlaneMap_map :
    universalPlaneMap L σ (MvPolynomial.map φ f) =
      MvPolynomial.map (MvPolynomial.map φ) (universalPlaneMap K σ f) := by
  have he : (universalPlaneMap L σ).toRingHom.comp (MvPolynomial.map φ) =
      (MvPolynomial.map (MvPolynomial.map φ)).comp (universalPlaneMap K σ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    simp
    · intro i
      simp [universalPlaneMap]
  exact RingHom.congr_fun he f

/-- The universal plane restriction commutes with applying a coefficient ring homomorphism. -/
lemma universalPlanePolynomial_map :
    universalPlanePolynomial (MvPolynomial.map φ f) =
      bivariateMap (MvPolynomial.map φ) (universalPlanePolynomial f) := by
  rw [universalPlanePolynomial, universalPlaneMap_map, universalPlanePolynomial,
    bivariatePolynomialEquiv_map]

end

private lemma universalPlanePolynomial_specialize_axis {K σ : Type*} [CommRing K]
    (a b c : σ → K) (f : MvPolynomial σ K) :
    Polynomial.map (Polynomial.evalRingHom 0)
      (bivariateMap (planeParameterEval (RingHom.id K) a b c) (universalPlanePolynomial f)) =
      affineLinePolynomial a b f := by
  rw [universalPlanePolynomial_specialize]
  have he : (Polynomial.mapRingHom (Polynomial.evalRingHom (0 : K))).comp
      ((bivariatePolynomialEquiv K).toRingHom.comp
        (eval₂Hom (C.comp (RingHom.id K))
          (fun i => C (a i) + C (b i) * X 0 + C (c i) * X 1))) = affineLinePolynomial a b := by
    apply MvPolynomial.ringHom_ext
    simp_all [affineLinePolynomial, bivariatePolynomialEquiv_C]
    simp [affineLinePolynomial, bivariatePolynomialEquiv_C, bivariatePolynomialEquiv_X_zero, bivariatePolynomialEquiv_X_one]
  exact RingHom.congr_fun he f

/-- The coefficient of x^d y^0, as a polynomial in all plane parameters. -/
def universalPlaneLeading {K σ : Type*} [CommRing K] (f : MvPolynomial σ K) :
    MvPolynomial (PlaneParameters σ) K :=
  ((universalPlanePolynomial f).coeff f.totalDegree).coeff 0

private lemma universalPlaneLeading_specialize {K σ : Type*} [CommRing K]
    (a b c : σ → K) (f : MvPolynomial σ K) :
    planeParameterEval (RingHom.id K) a b c (universalPlaneLeading f) =
      eval b (homogeneousComponent f.totalDegree f) := by
  have h := congrArg (fun q : Polynomial K => q.coeff f.totalDegree)
    (universalPlanePolynomial_specialize_axis a b c f)
  rw [Polynomial.coeff_map, affineLinePolynomial_top_coefficient a b f _ le_rfl] at h
  change Polynomial.eval 0 ((bivariateMap (planeParameterEval (RingHom.id K) a b c)
    (universalPlanePolynomial f)).coeff f.totalDegree) = _ at h
  rw [← Polynomial.coeff_zero_eq_eval_zero, bivariateMap_coeff] at h
  exact h

/-- The universal outer leading coefficient is nonzero for any nonzero equation
 over an infinite domain. -/
lemma universalPlaneLeading_ne_zero {K σ : Type*} [CommRing K] [IsDomain K] [Infinite K]
    (f : MvPolynomial σ K) (hf : f ≠ 0) : universalPlaneLeading f ≠ 0 := by
  intro h
  apply homogeneousComponent_totalDegree_ne_zero hf
  apply MvPolynomial.funext
  intro b
  rw [← universalPlaneLeading_specialize 0 b 0, h, map_zero, map_zero]

end
end CCDN
