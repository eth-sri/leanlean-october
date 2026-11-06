/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Noether.BivariateTotalDegree
import CCDN.Noether.GenericPlaneIrreducibility
import CCDN.Noether.ShearNormalization

/-! The generic plane f(x,y*z), with slopes in their rational function
field, has a smooth origin whenever the original equation does. Together with
ordinary irreducibility this proves geometric irreducibility of the generic
plane in the positioned coordinates. -/

namespace CCDN
noncomputable section
open MvPolynomial

/-- The generic plane substitution as a map of multivariate polynomial rings. -/
def genericPlaneMap (K F σ : Type*) [Field K] [Field F]
    [Algebra K F] [Algebra (MvPolynomial σ K) F] :
    MvPolynomial (Option σ) K →ₐ[K] MvPolynomial (Fin 2) F :=
  aeval (fun i => Option.elim i (X 0)
    (fun j => C (algebraMap (MvPolynomial σ K) F (X j)) * X 1))

variable {K F σ : Type*} [Field K] [Field F] [Algebra K F] [Algebra (MvPolynomial σ K) F]

/-- The generic plane substitution `genericPlaneMap K F σ f` corresponds, as a bivariate polynomial
over `F`, to the generic plane equation `genericPlanePolynomial f` with its coefficients mapped into
`F`. -/
lemma genericPlaneMap_bivariate
    [IsScalarTower K (MvPolynomial σ K) F]
    (f : MvPolynomial (Option σ) K) :
    bivariatePolynomialEquiv F (genericPlaneMap K F σ f) =
      bivariateMap (algebraMap (MvPolynomial σ K) F) (genericPlanePolynomial f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    simp [genericPlaneMap, genericPlanePolynomial, genericPlaneCoefficients,
      bivariateMap, bivariatePolynomialEquiv_C]
    exact IsScalarTower.algebraMap_apply K (MvPolynomial σ K) F a
  | add f g hf hg =>
    simp [map_add, hf, hg, genericPlanePolynomial, Polynomial.map_add]
  | mul_X f i hf =>
    cases i <;>
      simp [genericPlaneMap, genericPlanePolynomial, genericPlaneCoefficients,
        bivariateMap, bivariatePolynomialEquiv_X_zero, bivariatePolynomialEquiv_X_one,
        bivariatePolynomialEquiv_C] at hf ⊢
    all_goals simp [hf, true_or]

/-- The generic plane section of `f` takes at the origin the value `f(0)`. -/
lemma genericPlaneMap_eval_zero
    (f : MvPolynomial (Option σ) K) :
    eval (0 : Fin 2 → F) (genericPlaneMap K F σ f) =
      algebraMap K F (eval (0 : Option σ → K) f) := by
  have he : (eval (0 : Fin 2 → F)).comp (genericPlaneMap K F σ).toRingHom =
      (algebraMap K F).comp (eval (0 : Option σ → K)) := by
    apply MvPolynomial.ringHom_ext
    · simp_all
    · intro i
      cases i <;> simp [genericPlaneMap]
  exact RingHom.congr_fun he f

/-- The derivative of the generic plane section of `f` in its first variable is the generic plane
section of the derivative of `f` in the distinguished variable `none`. -/
lemma genericPlaneMap_pderiv
    (f : MvPolynomial (Option σ) K) :
    pderiv 0 (genericPlaneMap K F σ f) = genericPlaneMap K F σ (pderiv none f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [map_add, hf, hg]
  | mul_X f i hf =>
    cases i <;> simp [genericPlaneMap, pderiv_X] at hf ⊢
    all_goals simp [hf, true_or]

/-- Ordinary irreducibility over the rational function field in slopes. -/
theorem genericPlaneMap_irreducible
    [IsScalarTower K (MvPolynomial σ K) F] [IsFractionRing (MvPolynomial σ K) F]
    (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hd : 0 < f.totalDegree) (hm : (optionEquivLeft K σ f).Monic)
    (hx : 0 < (optionEquivLeft K σ f).natDegree) :
    Irreducible (genericPlaneMap K F σ f) := by
  apply (MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv F)).mp
  rw [genericPlaneMap_bivariate]
  let R := MvPolynomial σ K
  let g := (bivariatePolynomialEquiv R).symm (genericPlanePolynomial f)
  have hg :=
    (MulEquiv.irreducible_iff (f := (bivariatePolynomialEquiv R).symm)).mpr
      (show Irreducible (genericPlanePolynomial f) by
          rw [← genericPlaneCoefficientEquiv_stretch]
          exact (MulEquiv.irreducible_iff
            (f := Polynomial.mapAlgEquiv (genericPlaneCoefficientEquiv K σ))).mpr
              (show Irreducible (genericPlaneStretch f) by
                  let R := MvPolynomial Unit K
                  let F := FractionRing R
                  let ι : R →+* F := algebraMap R F
                  let κ : K →+* F := ι.comp C
                  let y : F := ι (X ())
                  have hy : y ≠ 0 := by aesop
                  let e := Polynomial.mapAlgEquiv (variableScaleEquiv F σ y hy)
                  have hbase : Irreducible (optionEquivLeft F σ (MvPolynomial.map κ f)) :=
                    (MulEquiv.irreducible_iff (f := optionEquivLeft F σ)).mpr
                      (irreducible_mvPolynomial_map_fraction_parameters f hf hd)
                  have hi :=
                    (MulEquiv.irreducible_iff (f := e)).mpr hbase
                  apply Polynomial.Monic.irreducible_of_irreducible_map
                    (MvPolynomial.map ι) (genericPlaneStretch f) (hm.map _)
                  have he : (MvPolynomial.map ι).comp (genericStretchCoefficients K σ).toRingHom =
                      (variableScaleEquiv F σ y hy).toRingHom.comp (MvPolynomial.map κ) := by
                    apply MvPolynomial.ringHom_ext
                    · intro a
                      simp [genericStretchCoefficients, κ, ι, variableScaleEquiv]
                    · intro i
                      simp [genericStretchCoefficients, y, variableScaleEquiv]
                  change Irreducible (Polynomial.map (variableScaleEquiv F σ y hy).toRingHom
                    (optionEquivLeft F σ (MvPolynomial.map κ f))) at hi
                  rw [optionEquivLeft_map_coefficients, Polynomial.map_map] at hi
                  simpa only [genericPlaneStretch, Polynomial.map_map, he] using hi))
  have hgdeg : 0 < g.totalDegree := by
    have hh := bivariate_natDegree_le_totalDegree (genericPlanePolynomial f)
    rw [genericPlanePolynomial_natDegree f hm] at hh
    exact hx.trans_le hh
  have hp := prime_mvPolynomial_map_localization (S := F) (nonZeroDivisors R)
    le_rfl g hg.prime hgdeg
  have he := (MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv F)).mpr hp.irreducible
  rw [← bivariatePolynomialEquiv_map] at he
  simpa [g, AlgEquiv.apply_symm_apply] using he

