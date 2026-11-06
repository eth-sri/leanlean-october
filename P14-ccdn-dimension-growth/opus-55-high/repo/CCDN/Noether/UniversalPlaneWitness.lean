/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.AffineLineLeading
import CCDN.Algebra.CharZeroOrGT
import CCDN.Noether.UniversalPlane
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import CCDN.Determinant.ClosedFormIntegerMinor
import CCDN.Determinant.UniversalPlaneMinor
import CCDN.ForMathlib.MvPolynomial
import CCDN.Noether.ClosedFormParameterDegree
import CCDN.Noether.ShearNormalization

/-!
A nonzero universal minor of cubic parameter degree, over the original coefficient field; the
nonvanishing proof descends from an algebraic closure. The leading coefficient of a universal
plane section, evaluated by the highest homogeneous form in the first direction, detects loss of
the full outer degree.
-/

namespace CCDN
noncomputable section
open MvPolynomial

section
variable {K L σ : Type*} [CommRing K] [CommRing L] (φ : K →+* L) (f : MvPolynomial σ K)

lemma universalPlaneMap_map
    :
    universalPlaneMap L σ (MvPolynomial.map φ f) =
      MvPolynomial.map (MvPolynomial.map φ) (universalPlaneMap K σ f) := by
  have he : (universalPlaneMap L σ).toRingHom.comp (MvPolynomial.map φ) =
      (MvPolynomial.map (MvPolynomial.map φ)).comp (universalPlaneMap K σ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · simp_all
    · intro i
      simp [universalPlaneMap]
  exact RingHom.congr_fun he f

/-- The universal plane restriction commutes with applying a coefficient ring homomorphism. -/
lemma universalPlanePolynomial_map
    :
    universalPlanePolynomial (MvPolynomial.map φ f) =
      bivariateMap (MvPolynomial.map φ) (universalPlanePolynomial f) := by
  rw [universalPlanePolynomial, universalPlaneMap_map, universalPlanePolynomial,
    bivariatePolynomialEquiv_map]

end

section
variable {K σ : Type*} [CommRing K]

/-- The coefficient of x^d y^0, as a polynomial in all plane parameters. -/
def universalPlaneLeading (f : MvPolynomial σ K) :
    MvPolynomial (PlaneParameters σ) K :=
  ((universalPlanePolynomial f).coeff f.totalDegree).coeff 0

lemma universalPlaneLeading_specialize
    (a b c : σ → K) (f : MvPolynomial σ K) :
    planeParameterEval (RingHom.id K) a b c (universalPlaneLeading f) =
      eval b (homogeneousComponent f.totalDegree f) := by
  have h := congrArg (fun q => q.coeff f.totalDegree)
    (show Polynomial.map (Polynomial.evalRingHom 0)
          (bivariateMap (planeParameterEval (RingHom.id K) a b c) (universalPlanePolynomial f)) =
          affineLinePolynomial a b f by
        rw [universalPlanePolynomial, bivariatePolynomialEquiv_map, universalPlaneMap_specialize]
        have he : (Polynomial.mapRingHom (Polynomial.evalRingHom (0 : K))).comp
            ((bivariatePolynomialEquiv K).toRingHom.comp
              (eval₂Hom (C.comp (RingHom.id K))
                (fun i => C (a i) + C (b i) * X 0 + C (c i) * X 1))) = affineLinePolynomial a b := by
          apply MvPolynomial.ringHom_ext
          · intro r
            simp [affineLinePolynomial, bivariatePolynomialEquiv_C]
          · intro i
            simp [affineLinePolynomial, bivariatePolynomialEquiv_C,
              bivariatePolynomialEquiv_X_zero, bivariatePolynomialEquiv_X_one]
        exact RingHom.congr_fun he f)
  rw [Polynomial.coeff_map, affineLinePolynomial_top_coefficient a b f _ le_rfl] at h
  change Polynomial.eval 0 ((bivariateMap (planeParameterEval (RingHom.id K) a b c)
    (universalPlanePolynomial f)).coeff f.totalDegree) = _ at h
  rwa [← Polynomial.coeff_zero_eq_eval_zero, bivariateMap_coeff] at h

end

lemma universalPlaneLeading_map {K L σ : Type*} [Field K] [Field L]
    (φ : K →+* L) (f : MvPolynomial σ K) :
    universalPlaneLeading (MvPolynomial.map φ f) =
      MvPolynomial.map φ (universalPlaneLeading f) := by
  have ht : (MvPolynomial.map φ f).totalDegree = f.totalDegree :=
      totalDegree_map_of_injective φ.injective _
  simp [universalPlaneLeading, ht, universalPlanePolynomial_map, bivariateMap_coeff]

variable {K σ : Type*} [Field K] [Fintype σ]

/-- Over an algebraically closed field, irreducibility and the characteristic bound
suffice for the leading polynomial to be nonzero. -/
theorem universalPlaneLeading_ne_zero_of_irreducible
    [IsAlgClosed K]
    (f : MvPolynomial (Option σ) K) (hf : Irreducible f) (hpos : 0 < f.totalDegree)
    (hchar : CharZeroOrGT K f.totalDegree) :
    universalPlaneLeading f ≠ 0 := by
  obtain ⟨a, b, _, hdir, _⟩ := exists_monic_smooth_hypersurface_coordinates f hf hpos hchar
  intro hz
  apply hdir
  rw [← universalPlaneLeading_specialize a b 0, hz, map_zero]

