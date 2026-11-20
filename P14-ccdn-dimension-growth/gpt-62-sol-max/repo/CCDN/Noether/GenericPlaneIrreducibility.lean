/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.ClosedFormBaseChange
public import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import CCDN.Noether.BivariateTotalDegree
import CCDN.Algebra.PolynomialPrimeLocalization
import CCDN.Noether.ShearNormalization

/-! Ordinary irreducibility of f(x,y*z_1,...,y*z_n) over the rational function
field in the slopes z_i. Before localizing, specialize y to 1 and use monicity in x. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Replace each transverse variable z_i with the polynomial z_i*y. -/
def genericPlaneCoefficients (K σ : Type*) [Field K] :
    MvPolynomial σ K →ₐ[K] Polynomial (MvPolynomial σ K) :=
  aeval (fun i => Polynomial.C (X i) * Polynomial.X)

/-- The generic plane equation, with x outermost and y the inner variable. -/
def genericPlanePolynomial {K σ : Type*} [Field K]
    (f : MvPolynomial (Option σ) K) : Polynomial (Polynomial (MvPolynomial σ K)) :=
  Polynomial.map (genericPlaneCoefficients K σ).toRingHom (optionEquivLeft K σ f)

section

variable {K σ : Type*} [Field K]
  (f : MvPolynomial (Option σ) K)
include K σ f

/-- If `f` is monic in its distinguished variable, then so is the generic plane equation of `f`. -/
lemma genericPlanePolynomial_monic (hf : (optionEquivLeft K σ f).Monic) :
    (genericPlanePolynomial f).Monic := hf.map _

/-- If `f` is monic in its distinguished variable, then the generic plane equation of `f` has the
same degree in that variable. -/
lemma genericPlanePolynomial_natDegree (hf : (optionEquivLeft K σ f).Monic) :
    (genericPlanePolynomial f).natDegree = (optionEquivLeft K σ f).natDegree :=
  hf.natDegree_map _

/-- The joint polynomial is monic in `x`, and the specialization `y = 1` recovers `f`. -/
private theorem genericPlanePolynomial_irreducible (hf : Irreducible f)
    (hm : (optionEquivLeft K σ f).Monic) : Irreducible (genericPlanePolynomial f) := by
  let ε := Polynomial.evalRingHom (1 : MvPolynomial σ K)
  have he : ε.comp (genericPlaneCoefficients K σ).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [ε, genericPlaneCoefficients, Polynomial.algebraMap_apply]
    · intro i; simp [ε, genericPlaneCoefficients]
  apply (genericPlanePolynomial_monic f hm).irreducible_of_irreducible_map ε
  rw [genericPlanePolynomial, Polynomial.map_map, he, Polynomial.map_id]
  exact (MulEquiv.irreducible_iff (f := optionEquivLeft K σ)).mpr hf

end

/-- Localizing the slope parameters preserves the ordinary irreducibility of
the generic plane equation. -/
theorem genericPlanePolynomial_irreducible_fraction_slopes
    {K F σ : Type*} [Field K] [Field F]
    [Algebra (MvPolynomial σ K) F] [IsFractionRing (MvPolynomial σ K) F]
    (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hm : (optionEquivLeft K σ f).Monic)
    (hx : 0 < (optionEquivLeft K σ f).natDegree) :
    Irreducible (bivariateMap (algebraMap (MvPolynomial σ K) F) (genericPlanePolynomial f)) := by
  let R := MvPolynomial σ K
  let g := (bivariatePolynomialEquiv R).symm (genericPlanePolynomial f)
  have hg :=
    (MulEquiv.irreducible_iff (f := (bivariatePolynomialEquiv R).symm)).mpr
      (genericPlanePolynomial_irreducible f hf hm)
  have hgdeg : 0 < g.totalDegree := by
    have hh := bivariate_natDegree_le_totalDegree (genericPlanePolynomial f)
    rw [genericPlanePolynomial_natDegree f hm] at hh
    exact hx.trans_le hh
  have hp := prime_mvPolynomial_map_localization (S := F) (nonZeroDivisors R)
    le_rfl g hg.prime hgdeg
  have he := (MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv F)).mpr hp.irreducible
  rw [← bivariatePolynomialEquiv_map] at he
  aesop

end
end CCDN
