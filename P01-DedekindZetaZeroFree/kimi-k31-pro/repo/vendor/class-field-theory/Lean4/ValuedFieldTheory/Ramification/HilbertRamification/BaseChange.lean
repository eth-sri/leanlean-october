module

public import ValuedFieldTheory.Ramification.HilbertRamification.DecompositionGroup
public import ValuedFieldTheory.Valuation.DiscreteValuationField.ResidueField

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Conjugation and base change

This file proves functoriality of the decomposition, inertia, and
ramification groups under a commutative square of field embeddings.  Only
normality of the lower extension is needed to restrict conjugation to its
Galois group.  The decomposition statement for absolute values includes
the archimedean case; the valuation-subring statements give the three
nonarchimedean homomorphisms.
-/

noncomputable section

universe u v u' v'

namespace HilbertRamification

open AlgebraicNumberTheory.Valuations
open scoped Pointwise

variable {K : Type u} {L : Type v} {K' : Type u'} {L' : Type v'}
variable [Field K] [Field L] [Field K'] [Field L']
variable [Algebra K L] [Algebra K' L']

section GaloisPullback

variable (tauK : K →+* K') (tauL : L →+* L')
variable (hsquare : tauL.comp (algebraMap K L) =
  (algebraMap K' L').comp tauK)
variable [Normal K L]

include hsquare in
 def galoisPullbackElement (sigma : L' ≃ₐ[K'] L') : L ≃ₐ[K] L := by
  letI : Algebra K K' := tauK.toAlgebra
  letI : Algebra K L' := ((algebraMap K' L').comp tauK).toAlgebra
  letI : Algebra L L' := tauL.toAlgebra
  letI : IsScalarTower K K' L' :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K L L' :=
    IsScalarTower.of_algebraMap_eq' (by
      simpa only [RingHom.algebraMap_toAlgebra] using hsquare.symm)
  let tauLK : L →ₐ[K] L' :=
    { tauL with
      commutes' := fun x => by
        exact (congrFun (RingHom.coe_coe tauL) _).trans
          (DFunLike.congr_fun hsquare x) }
  exact
    Normal.algHomEquivAut K L' L
      ((sigma.restrictScalars K).toAlgHom.comp
        tauLK)

 theorem galoisPullbackElement_commutes
    (sigma : L' ≃ₐ[K'] L') (x : L) :
    tauL (galoisPullbackElement tauK tauL hsquare sigma x) =
      sigma (tauL x) := by
  let : Algebra K K' := tauK.toAlgebra
  let : Algebra K L' := ((algebraMap K' L').comp tauK).toAlgebra
  let : Algebra L L' := tauL.toAlgebra
  let : IsScalarTower K K' L' :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K L L' :=
    IsScalarTower.of_algebraMap_eq' (by
      simpa only [RingHom.algebraMap_toAlgebra] using hsquare.symm)
  let tauLK : L →ₐ[K] L' :=
    { tauL with
      commutes' := fun y => by
        exact (congrFun (RingHom.coe_coe tauL) _).trans
          (DFunLike.congr_fun hsquare y) }
  change algebraMap L L'
      (galoisPullbackElement tauK tauL hsquare sigma x) = _
  change algebraMap L L'
      ((((sigma.restrictScalars K).toAlgHom.comp tauLK).restrictNormal' L) x) = _
  rw [show
      (((sigma.restrictScalars K).toAlgHom.comp tauLK).restrictNormal' L) x =
        (((sigma.restrictScalars K).toAlgHom.comp tauLK).restrictNormal L) x by
      apply congrFun
      exact AlgEquiv.coe_ofBijective _ _]
  rw [AlgHom.restrictNormal_commutes]
  rfl

include hsquare in
/-- The conjugation and base-change law: conjugation along a commutative
square restricts to a homomorphism on Galois groups. -/
def galoisPullback_galoisPullback : (L' ≃ₐ[K'] L') →* (L ≃ₐ[K] L) where
  toFun := galoisPullbackElement tauK tauL hsquare
  map_one' := by
    ext x
    apply tauL.injective
    rw [galoisPullbackElement_commutes]
    simp
  map_mul' sigma rho := by
    ext x
    apply tauL.injective
    rw [galoisPullbackElement_commutes]
    change sigma (rho (tauL x)) =
      tauL (galoisPullbackElement tauK tauL hsquare sigma
        (galoisPullbackElement tauK tauL hsquare rho x))
    rw [galoisPullbackElement_commutes, galoisPullbackElement_commutes]

/-- The defining equation `tauL (tau^* sigma x) = sigma (tauL x)`. -/
@[simp] theorem galoisPullback_galoisPullback_commutes
    (sigma : L' ≃ₐ[K'] L') (x : L) :
    tauL (galoisPullback_galoisPullback tauK tauL hsquare sigma x) =
      sigma (tauL x) :=
  galoisPullbackElement_commutes tauK tauL hsquare sigma x



namespace ValuationSubring

open RamificationTheory.HilbertRamification.ValuationSubring

variable (A' : _root_.ValuationSubring L')

 

 



 



 







 



end ValuationSubring

end GaloisPullback

end HilbertRamification

end
