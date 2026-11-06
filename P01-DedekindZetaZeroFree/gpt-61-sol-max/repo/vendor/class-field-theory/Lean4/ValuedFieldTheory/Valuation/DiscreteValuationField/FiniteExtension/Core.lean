module

public import Mathlib

public import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Degree
public import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Uniqueness

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false
/-! Provides the public declarations in the `ValuationTheory.DiscreteValuationField.FiniteExtension` Lean module. -/

namespace ValuationTheory

noncomputable section

universe u v w x y

namespace DiscreteValuationField

namespace ValuedExtension.Henselian

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : HenselianDVF.{u, v} K) (target : HenselianDVF.{w, x} L)
variable [base.toDVF.valuation.HasExtension target.toDVF.valuation]

/-- The canonical integer map from a Henselian base valuation ring to the
valuation subring constructed from the actual integral closure. -/
def integralClosureValuationSubringIntegerMapOfMemOrInv
    (base : HenselianDVF.{u, v} K)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring) :
    base.valuationSubring →+*
      ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
        (L := L) base.toDVF.valuation hval where
  toFun a :=
    ⟨algebraMap K L (a : K),
      (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_pullback
        (L := L) base.toDVF.valuation hval (a : K)).2 a.2⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' := by intro a b; ext; simp
  map_mul' := by intro a b; ext; simp

omit [FiniteDimensional K L] in
/-- The integer map into the integral-closure valuation ring is the ambient algebra map. -/
@[simp] theorem integralClosureValuationSubringIntegerMapOfMemOrInv_apply
    (base : HenselianDVF.{u, v} K)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (a : base.valuationSubring) :
    ((integralClosureValuationSubringIntegerMapOfMemOrInv
      (K := K) (L := L) base hval a) : L) =
      algebraMap K L (a : K) :=
  rfl

omit [FiniteDimensional K L] in
/-- The canonical integer map into the valuation subring built from the actual
integral closure is injective. -/
theorem integralClosureValuationSubringIntegerMapOfMemOrInv_injective
    (base : HenselianDVF.{u, v} K)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring) :
    Function.Injective
      (integralClosureValuationSubringIntegerMapOfMemOrInv
        (K := K) (L := L) base hval) := by
  intro a b hab
  apply Subtype.ext
  apply FaithfulSMul.algebraMap_injective K L
  exact congrArg
      (fun x :
        ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) base.toDVF.valuation hval => (x : L)) hab

omit [FiniteDimensional K L] in
/-- The center of an extension valuation ring on the constructed actual
integral-closure valuation subring contracts to the base maximal ideal. -/
theorem idealOfLE_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (base : HenselianDVF.{u, v} K) (vL : _root_.Valuation L ΓL)
    [base.toDVF.valuation.HasExtension vL]
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring) :
    let B :=
      ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
        (L := L) base.toDVF.valuation hval
    let hvL_le : B ≤ vL.valuationSubring :=
      ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
        (L := L) base.toDVF.valuation vL hval
    (ValuationSubring.idealOfLE B vL.valuationSubring hvL_le).comap
        (integralClosureValuationSubringIntegerMapOfMemOrInv
          (K := K) (L := L) base hval) =
      base.maximalIdeal := by
  let B :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
      (L := L) base.toDVF.valuation hval
  let hvL_le : B ≤ vL.valuationSubring :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
      (L := L) base.toDVF.valuation vL hval
  let i : base.valuationSubring →+* B :=
    integralClosureValuationSubringIntegerMapOfMemOrInv
      (K := K) (L := L) base hval
  apply Ideal.ext
  intro a
  rw [Ideal.mem_comap]
  change B.inclusion vL.valuationSubring hvL_le (i a) ∈
      IsLocalRing.maximalIdeal vL.valuationSubring ↔
    a ∈ IsLocalRing.maximalIdeal base.toDVF.valuation.valuationSubring
  rw [Valuation.mem_maximalIdeal_iff (v := vL)]
  rw [Valuation.mem_maximalIdeal_iff (v := base.toDVF.valuation)]
  have hcoe :
      ((B.inclusion vL.valuationSubring hvL_le (i a)) : L) =
        algebraMap K L (a : K) := rfl
  rw [hcoe]
  apply Valuation.HasExtension.val_map_lt_one_iff

/-- In a finite separable extension, once the actual integral closure has the
valuation-ring dichotomy, the constructed integral-closure valuation ring has a
unique prime over the base maximal ideal. -/
theorem prime_eq_maximalIdeal_of_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
    (base : HenselianDVF.{u, v} K)
    [Algebra.IsSeparable K L]
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (P :
      Ideal
        (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) base.toDVF.valuation hval))
    (hP : P.IsPrime)
    (hcomap :
      P.comap
          (integralClosureValuationSubringIntegerMapOfMemOrInv
            (K := K) (L := L) base hval) =
        base.maximalIdeal) :
    P =
      IsLocalRing.maximalIdeal
        (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) base.toDVF.valuation hval) := by
  let B :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
      (L := L) base.toDVF.valuation hval
  let i : base.valuationSubring →+* B :=
    integralClosureValuationSubringIntegerMapOfMemOrInv
      (K := K) (L := L) base hval
  let : base.toDVF.valuation.HasExtension B.valuation :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_hasExtension
      (L := L) base.toDVF.valuation hval
  let : IsFractionRing base.valuationSubring K :=
    base.toDVF.valuationSubring_isFractionRing
  let  :=
    base.valuationSubring_isDiscreteValuationRing
  let : IsDedekindDomain base.valuationSubring := inferInstance
  let  := RingHom.toAlgebra i
  let : IsScalarTower base.valuationSubring B L :=
    IsScalarTower.of_algebraMap_eq (by
      intro a
      rfl)
  let : IsIntegralClosure B base.valuationSubring L :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_isIntegralClosure
      (L := L) base.toDVF.valuation hval
  let  :=
    IsIntegralClosure.isDedekindDomain base.valuationSubring K L B
  have hi : Function.Injective i :=
    integralClosureValuationSubringIntegerMapOfMemOrInv_injective
      (K := K) (L := L) base hval
  have hP_ne_bot : P ≠ ⊥ := by
    have hnot_le_bot : ¬ base.maximalIdeal ≤ ⊥ := by
      intro hle
      exact base.maximalIdeal_ne_bot (le_antisymm hle bot_le)
    obtain ⟨a, ha_max, ha_not_bot⟩ := Set.not_subset.mp hnot_le_bot
    have ha_ne_zero : a ≠ 0 := by
      intro ha
      apply ha_not_bot <;> assumption
    intro hPbot
    have ha_comap : a ∈ P.comap i := by
      simpa [B, i, hcomap] using ha_max
    have hai_mem : i a ∈ P := ha_comap
    have hai_zero : i a = 0 := by
      simpa [hPbot] using hai_mem
    exact ha_ne_zero (hi (by simpa using hai_zero))
  exact IsLocalRing.eq_maximalIdeal (hP.isMaximal hP_ne_bot)

omit [FiniteDimensional K L] in
/-- Center-equality form of Henselian-DVF valuation uniqueness after the actual
integral closure has been turned into a valuation subring. -/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_center_eq_maximalIdeal

    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (htargetCenter :
      ValuationSubring.idealOfLE
        (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) base.toDVF.valuation hval)
        target.toDVF.valuation.valuationSubring
        (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
          (L := L) base.toDVF.valuation target.toDVF.valuation hval) =
        IsLocalRing.maximalIdeal
          (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
            (L := L) base.toDVF.valuation hval))
    (hcenter :
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.toDVF.valuation.HasExtension v'],
          ValuationSubring.idealOfLE
            (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
              (L := L) base.toDVF.valuation hval)
            v'.valuationSubring
            (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
              (L := L) base.toDVF.valuation v' hval) =
            IsLocalRing.maximalIdeal
              (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
                (L := L) base.toDVF.valuation hval)) :
    HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target := by
  let B :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
      (L := L) base.toDVF.valuation hval
  have htarget_le : B ≤ target.toDVF.valuation.valuationSubring :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
      (L := L) base.toDVF.valuation target.toDVF.valuation hval
  have htarget_eq  :=
    ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal
      B target.toDVF.valuation.valuationSubring htarget_le
      (htargetCenter)
  intro Gamma' _ v' hExt
  let  := hExt
  have hv_le : B ≤ v'.valuationSubring :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
      (L := L) base.toDVF.valuation v' hval
  have hv_eq  :=
    ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal
      B v'.valuationSubring hv_le
      (by apply hcenter)
  have hSubring  :=
    htarget_eq.trans hv_eq.symm
  exact HenselianDVF.valuation_isEquiv_of_valuationSubring_eq base target v' hSubring

omit [FiniteDimensional K L] in
/-- Prime-uniqueness form of Henselian-DVF valuation uniqueness. -/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_unique_primes_over_base_maximal

    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (hunique :
      let B :=
        ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) base.toDVF.valuation hval
      let i : base.valuationSubring →+* B :=
        integralClosureValuationSubringIntegerMapOfMemOrInv
          (K := K) (L := L) base hval
      ∀ P : Ideal B, P.IsPrime → P.comap i = base.maximalIdeal →
        P = IsLocalRing.maximalIdeal B) :
    HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target := by
  let B :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
      (L := L) base.toDVF.valuation hval
  
  refine
    (hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_center_eq_maximalIdeal
      (K := K) (L := L) (base := base) (target := target)  hval ?_ ?_ :
        HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target)
  · let htarget_le : B ≤ target.toDVF.valuation.valuationSubring :=
      ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
        (L := L) base.toDVF.valuation target.toDVF.valuation hval
    exact hunique
      (ValuationSubring.idealOfLE B target.toDVF.valuation.valuationSubring htarget_le)
      (by infer_instance)
      (by
        apply idealOfLE_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal)
  · intro Gamma' _ v' hExt
    let  := hExt
    let hv_le : B ≤ v'.valuationSubring :=
      ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
        (L := L) base.toDVF.valuation v' hval
    exact hunique
      (ValuationSubring.idealOfLE B v'.valuationSubring hv_le)
      (by infer_instance)
      (by
        apply idealOfLE_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal)

/-- Finite-separable Henselian-DVF uniqueness once the actual integral closure
has the valuative dichotomy. -/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv

    [Algebra.IsSeparable K L]
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring) :
    HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target :=
  (hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_unique_primes_over_base_maximal base target)
    hval
    (by
      let B :=
        ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) base.toDVF.valuation hval
      let i : base.valuationSubring →+* B :=
        integralClosureValuationSubringIntegerMapOfMemOrInv
          (K := K) (L := L) base hval
      change ∀ P : Ideal B, P.IsPrime → P.comap i = base.maximalIdeal →
        P = IsLocalRing.maximalIdeal B
      intro P hP hcomap
      apply prime_eq_maximalIdeal_of_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal <;> assumption)

/-- Finite-separable Henselian-DVF uniqueness once the actual integral closure
is local. -/
theorem hasUniqueValuationExtension_of_integralClosure_isLocalRing

    [Algebra.IsSeparable K L]
    [IsLocalRing (integralClosureIntegers base target)] :
    HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target :=
  (hasUniqueValuationExtension_of_integralClosure_mem_or_inv base target)
    (integralClosure_mem_or_inv_of_isLocalRing base target)

/-- Finite-separable Henselian-DVF uniqueness once the residue fiber over the
base maximal ideal has at most one prime. -/
theorem hasUniqueValuationExtension_of_integralClosure_base_maximal_fiber_subsingleton

    [Algebra.IsSeparable K L]
    [Subsingleton
      (PrimeSpectrum (base.maximalIdeal.Fiber (integralClosureIntegers base target)))] :
    HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target := by
  let  :=
    (integralClosure_isLocalRing_of_base_maximal_fiber_subsingleton base target)
  exact
    (hasUniqueValuationExtension_of_integralClosure_isLocalRing
      (K := K) (L := L) (base := base) (target := target)  :
        HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target)





















/-- Finite-separable Henselian-DVF uniqueness from the Henselian-kernel
idempotent-lifting criterion for the residue-fiber `includeRight` map. -/
theorem IntegralClosureFiber.unique_of_includeRight_surjective_henselianRing_ker

    [Algebra.IsSeparable K L]
    (hsurj :
      Function.Surjective
        (Algebra.TensorProduct.includeRight :
          (integralClosureIntegers base target) →ₐ[base.valuationSubring]
            base.maximalIdeal.Fiber (integralClosureIntegers base target)))
    [HenselianRing (integralClosureIntegers base target)
      (RingHom.ker
        ((Algebra.TensorProduct.includeRight :
          (integralClosureIntegers base target) →ₐ[base.valuationSubring]
            base.maximalIdeal.Fiber (integralClosureIntegers base target)) :
          (integralClosureIntegers base target) →+*
            base.maximalIdeal.Fiber (integralClosureIntegers base target)))] :
    HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target := by
  let : Subsingleton
      (PrimeSpectrum (base.maximalIdeal.Fiber (integralClosureIntegers base target))) :=
    (integralClosure_base_maximal_fiber_subsingleton_of_includeRight_surjective_henselianRing_ker base target)
      hsurj
  exact
    (hasUniqueValuationExtension_of_integralClosure_base_maximal_fiber_subsingleton
      (K := K) (L := L) (base := base) (target := target)  :
        HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target)

























































































































































































end ValuedExtension.Henselian

namespace HenselianDVF

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
















































































































































end HenselianDVF
end DiscreteValuationField

end

end ValuationTheory
