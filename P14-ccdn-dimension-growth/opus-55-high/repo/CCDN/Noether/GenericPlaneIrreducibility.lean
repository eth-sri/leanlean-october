/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Noether.ClosedFormBaseChange
import CCDN.Noether.GenericPlaneStretch
import CCDN.Algebra.PolynomialPrimeLocalization
import CCDN.Noether.ShearNormalization

/-! Ordinary irreducibility of f(x,y*z_1,...,y*z_n) over the rational function
field in the slopes z_i. The original equation is irreducible and monic in x;
all parameter extensions and changes of polynomial presentation are proved. -/

namespace CCDN
noncomputable section
open MvPolynomial

section
variable (K σ : Type*) [Field K]

/-- Exchange the fresh y parameter with the transverse slope variables. -/
def genericPlaneCoefficientEquiv :
    MvPolynomial σ (MvPolynomial Unit K) ≃ₐ[K] Polynomial (MvPolynomial σ K) :=
  (commAlgEquiv K σ Unit).trans ((uniqueAlgEquiv (MvPolynomial σ K) Unit).restrictScalars K)

/-- Replace each transverse variable z_i with the polynomial z_i*y. -/
def genericPlaneCoefficients :
    MvPolynomial σ K →ₐ[K] Polynomial (MvPolynomial σ K) :=
  aeval (fun i => Polynomial.C (X i) * Polynomial.X)

end

section
variable {K σ : Type*} [Field K] (f : MvPolynomial (Option σ) K)

/-- The generic plane equation, with x outermost and y the inner variable. -/
def genericPlanePolynomial
    : Polynomial (Polynomial (MvPolynomial σ K)) :=
  Polynomial.map (genericPlaneCoefficients K σ).toRingHom (optionEquivLeft K σ f)

lemma genericPlaneCoefficientEquiv_stretch
    :
    Polynomial.map (genericPlaneCoefficientEquiv K σ).toRingHom (genericPlaneStretch f) =
      genericPlanePolynomial f := by
  have he : (genericPlaneCoefficientEquiv K σ).toRingHom.comp
      (genericStretchCoefficients K σ).toRingHom = (genericPlaneCoefficients K σ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [genericPlaneCoefficientEquiv, genericStretchCoefficients, genericPlaneCoefficients]
    · intro i
      simp [genericPlaneCoefficientEquiv, genericStretchCoefficients, genericPlaneCoefficients]
  simp only [genericPlaneStretch, genericPlanePolynomial, Polynomial.map_map, he]

/-- If `f` is monic in its distinguished variable, then so is the generic plane equation of `f`. -/
lemma genericPlanePolynomial_monic
    (hf : (optionEquivLeft K σ f).Monic) :
    (genericPlanePolynomial f).Monic := hf.map _

/-- If `f` is monic in its distinguished variable, then the generic plane equation of `f` has the
same degree in that variable. -/
lemma genericPlanePolynomial_natDegree
    (hf : (optionEquivLeft K σ f).Monic) :
    (genericPlanePolynomial f).natDegree = (optionEquivLeft K σ f).natDegree :=
  hf.natDegree_map _

end

