module

public import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Degree

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false
/-! Provides the public declarations in the `ValuationTheory.DiscreteValuationField.FiniteExtension.Uniqueness` Lean module. -/

namespace ValuationTheory

noncomputable section

universe u v w x y

namespace DiscreteValuationField
namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- A complete-DVF uniqueness predicate for extensions of the base valuation. -/
def HasUniqueValuationExtension (base : CompleteDVF.{u, v} K)
    (target : CompleteDVF.{w, x} L) : Prop :=
  ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
      target.valuation.IsEquiv v'













omit [FiniteDimensional K L] in
/-- Center-prime form of the Henselian uniqueness frontier.

If the actual integral closure of the base valuation ring is a valuation ring,
and the center of every extension valuation ring on that integral-closure
valuation ring is the maximal ideal, then the extension valuation is unique.

This is the exact prime-theoretic step that remains after proving the
Henselian valuative dichotomy: the hypotheses are the center equalities
the Henselian finite-extension theorem must supply, not local-map or
certificate-style substitutes. -/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_center_eq_maximalIdeal

    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (htargetCenter :
      ValuationSubring.idealOfLE
        (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval)
        target.valuation.valuationSubring
        (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
          (L := L) base.valuation target.valuation hval) =
        IsLocalRing.maximalIdeal
          (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
            (L := L) base.valuation hval))
    (hcenter :
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
          ValuationSubring.idealOfLE
            (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
              (L := L) base.valuation hval)
            v'.valuationSubring
            (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
              (L := L) base.valuation v' hval) =
            IsLocalRing.maximalIdeal
              (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
                (L := L) base.valuation hval)) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let B :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
      (L := L) base.valuation hval
  have htarget_le : B ≤ target.valuation.valuationSubring :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
      (L := L) base.valuation target.valuation hval
  have htarget_eq : target.valuation.valuationSubring = B :=
    ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal
      B target.valuation.valuationSubring htarget_le
      (by simpa [B, htarget_le] using htargetCenter)
  intro Gamma' _ v' hExt
  let : base.valuation.HasExtension v' := hExt
  have hv_le : B ≤ v'.valuationSubring :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
      (L := L) base.valuation v' hval
  have hv_eq : v'.valuationSubring = B :=
    ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal
      B v'.valuationSubring hv_le
      (by simpa [B, hv_le] using (@hcenter Gamma' inferInstance v' hExt))
  have hSubring : target.valuation.valuationSubring = v'.valuationSubring :=
    htarget_eq.trans hv_eq.symm
  exact valuation_isEquiv_of_valuationSubring_eq target v' hSubring

omit [FiniteDimensional K L] in
/-- Prime-uniqueness form of the Henselian uniqueness frontier.

After the actual integral closure has been turned into a valuation subring, it
is enough to prove that every prime of that valuation subring whose contraction
to the base valuation ring is the base maximal ideal is itself the maximal
ideal.  The center of each extension valuation ring has exactly that
contraction, so this theorem converts the Henselian local prime-uniqueness
statement into uniqueness of valuation extensions. -/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_unique_primes_over_base_maximal

    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (hunique :
      let B :=
        ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval
      let i : base.valuationSubring →+* B :=
        integralClosureValuationSubringIntegerMapOfMemOrInv
          (K := K) (L := L) base hval
      ∀ P : Ideal B, P.IsPrime → P.comap i = base.maximalIdeal →
        P = IsLocalRing.maximalIdeal B) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let B :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
      (L := L) base.valuation hval
  let i : base.valuationSubring →+* B :=
    integralClosureValuationSubringIntegerMapOfMemOrInv
      (K := K) (L := L) base hval
  refine
    (hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_center_eq_maximalIdeal
      (K := K) (L := L) (base := base) (target := target)  hval ?_ ?_ :
        HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target))
  · let htarget_le : B ≤ target.valuation.valuationSubring :=
      ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
        (L := L) base.valuation target.valuation hval
    exact hunique
      (ValuationSubring.idealOfLE B target.valuation.valuationSubring htarget_le)
      (by infer_instance)
      (by
        simpa [B, htarget_le, i] using
          idealOfLE_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
            (K := K) (L := L) base target.valuation hval)
  · intro Gamma' _ v' hExt
    let : base.valuation.HasExtension v' := hExt
    let hv_le : B ≤ v'.valuationSubring :=
      ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
        (L := L) base.valuation v' hval
    exact hunique
      (ValuationSubring.idealOfLE B v'.valuationSubring hv_le)
      (by infer_instance)
      (by
        simpa [B, hv_le, i] using
          idealOfLE_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
            (K := K) (L := L) base v' hval)

/-- Finite-separable form of the Henselian uniqueness bridge.

After the Henselian part proves the valuative dichotomy for the actual
integral closure, finite separability supplies the prime uniqueness over the
base maximal ideal by Dedekind theory.  Thus no separate local-map, center
equality, integral-inclusion, or module-finiteness certificates are needed to
deduce uniqueness of the valuation extension. -/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv

    [Algebra.IsSeparable K L]
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) :=
  (hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_unique_primes_over_base_maximal base target)
    hval
    (by
      let B :=
        ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval
      let i : base.valuationSubring →+* B :=
        integralClosureValuationSubringIntegerMapOfMemOrInv
          (K := K) (L := L) base hval
      change ∀ P : Ideal B, P.IsPrime → P.comap i = base.maximalIdeal →
        P = IsLocalRing.maximalIdeal B
      intro P hP hcomap
      exact
        prime_eq_maximalIdeal_of_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
          (K := K) (L := L) (base := base) hval P hP hcomap)







/-- Finite-separable uniqueness once the actual integral closure is local.

This is the sharpened Henselian frontier: after the Henselian argument proves
that the finite integral closure is a local ring, Dedekind theory makes it a
valuation ring and the valuative-dichotomy bridge above supplies uniqueness of
all valuation extensions. -/
theorem hasUniqueValuationExtension_of_integralClosure_isLocalRing

    [Algebra.IsSeparable K L]
    [IsLocalRing (integralClosureIntegers base target)] :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) :=
  (hasUniqueValuationExtension_of_integralClosure_mem_or_inv base target)
    (integralClosure_mem_or_inv_of_isLocalRing base target)



/-- Finite-separable uniqueness once the residue fiber over the base maximal
ideal has at most one prime.

The actual integral closure has a prime above the base maximal ideal by
going-up, and the fiber order-isomorphism identifies uniqueness in the fiber
with uniqueness of primes above the base maximal ideal.  The already-proved
singleton/local bridge then supplies valuation uniqueness. -/
theorem hasUniqueValuationExtension_of_integralClosure_base_maximal_fiber_subsingleton

    [Algebra.IsSeparable K L]
    [Subsingleton
      (PrimeSpectrum (base.maximalIdeal.Fiber (integralClosureIntegers base target)))] :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let : IsLocalRing (integralClosureIntegers base target) :=
    (integralClosure_isLocalRing_of_base_maximal_fiber_subsingleton base target)
  exact
    (hasUniqueValuationExtension_of_integralClosure_isLocalRing
      (K := K) (L := L) (base := base) (target := target)  :
        HasUniqueValuationExtension.{u, v, w, x, y}
          (base := base) (target := target))







/-- Finite-separable uniqueness from the natural Henselian-pair ideal in the
actual integral closure.

The kernel computation for the residue-fiber includeRight map identifies its
kernel with base.maximalIdeal.map; hence a Henselian proof for that natural
ideal is enough to enter the finite-extension uniqueness bridge. -/
theorem hasUniqueValuationExtension_of_integralClosure_base_maximal_map_henselianRing

    [Algebra.IsSeparable K L]
    [HenselianRing (integralClosureIntegers base target)
      (base.maximalIdeal.map
        (algebraMap base.valuationSubring (integralClosureIntegers base target)))] :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let : Subsingleton
      (PrimeSpectrum (base.maximalIdeal.Fiber (integralClosureIntegers base target))) :=
    (integralClosure_base_maximal_fiber_subsingleton_of_henselianRing_maximalIdeal_map base target)
  exact
    (hasUniqueValuationExtension_of_integralClosure_base_maximal_fiber_subsingleton
      (K := K) (L := L) (base := base) (target := target)  :
        HasUniqueValuationExtension.{u, v, w, x, y}
          (base := base) (target := target))


/-- Finite separable extensions of complete DVFs have a unique extension of the
base valuation, up to mathlib's valuation equivalence.

The proof routes through the actual integral closure: finite-module completeness
makes the ideal generated by the base maximal ideal Henselian there, and the
residue-fiber idempotent argument collapses the possible primes above the base
maximal ideal. -/
theorem hasUniqueValuationExtension_of_finite_separable

    [Algebra.IsSeparable K L] :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let : HenselianRing (integralClosureIntegers base target)
      (base.maximalIdeal.map
        (algebraMap base.valuationSubring (integralClosureIntegers base target))) :=
    (integralClosure_base_maximal_map_henselianRing base target)
  exact
    (hasUniqueValuationExtension_of_integralClosure_base_maximal_map_henselianRing
      (K := K) (L := L) (base := base) (target := target)  :
        HasUniqueValuationExtension.{u, v, w, x, y}
          (base := base) (target := target))



/-- In a finite separable extension of complete DVFs, the actual integral
closure of the base valuation ring is itself a valuation ring. -/
theorem integralClosure_mem_or_inv_of_finite_separable
    (target : CompleteDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [Algebra.IsSeparable K L] :
    ∀ z : L,
      z ∈ (integralClosure base.valuationSubring L).toSubring ∨
        z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring := by
  let : HenselianRing (integralClosureIntegers base target)
      (base.maximalIdeal.map
        (algebraMap base.valuationSubring (integralClosureIntegers base target))) :=
    (integralClosure_base_maximal_map_henselianRing base target)
  let : Subsingleton
      (PrimeSpectrum (base.maximalIdeal.Fiber (integralClosureIntegers base target))) :=
    (integralClosure_base_maximal_fiber_subsingleton_of_henselianRing_maximalIdeal_map base target)
  let : IsLocalRing (integralClosureIntegers base target) :=
    (integralClosure_isLocalRing_of_base_maximal_fiber_subsingleton base target)
  exact (integralClosure_mem_or_inv_of_isLocalRing base target)









omit [FiniteDimensional K L] [base.valuation.HasExtension target.valuation] in
/-- The valuation-subring equality consequence of unique valuation extension. -/
theorem valuationSubring_eq_of_hasUniqueValuationExtension

    (huniq : HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target))
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'] :
    target.valuation.valuationSubring = v'.valuationSubring :=
  valuationSubring_eq_of_valuation_isEquiv target (@huniq Gamma' _ v' _)





/-- In a finite separable extension of complete DVFs, every extension valuation
is equivalent to the chosen target valuation. -/
theorem valuation_isEquiv_of_finite_separable

    [Algebra.IsSeparable K L]
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'] :
    target.valuation.IsEquiv v' :=
  ((hasUniqueValuationExtension_of_finite_separable base target) :
    HasUniqueValuationExtension.{u, v, w, x, y}
      (base := base) (target := target)) v'

/-- In a finite separable extension of complete DVFs, the chosen target
valuation subring equals the valuation subring of any extension valuation. -/
theorem valuationSubring_eq_of_finite_separable

    [Algebra.IsSeparable K L]
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'] :
    target.valuation.valuationSubring = v'.valuationSubring :=
  (valuationSubring_eq_of_hasUniqueValuationExtension base target)
    ((hasUniqueValuationExtension_of_finite_separable base target) :
      HasUniqueValuationExtension.{u, v, w, x, y}
        (base := base) (target := target)) v'







omit [FiniteDimensional K L] [base.valuation.HasExtension target.valuation] in
/-- Under unique extension, any valuation subring whose canonical valuation
extends the base valuation is the chosen target valuation ring. -/
theorem target_valuationSubring_eq_of_hasUniqueValuationExtension
    (huniq : HasUniqueValuationExtension.{u, v, w, x, w}
      (base := base) (target := target))
    (B : ValuationSubring L) [base.valuation.HasExtension B.valuation] :
    target.valuation.valuationSubring = B := by
  have hEquiv : target.valuation.IsEquiv B.valuation :=
    huniq B.valuation
  have hSubring :
      target.valuation.valuationSubring = B.valuation.valuationSubring :=
    (_root_.Valuation.isEquiv_iff_valuationSubring
      target.valuation B.valuation).1 hEquiv
  simpa [ValuationSubring.valuationSubring_valuation] using hSubring



omit [FiniteDimensional K L] [base.valuation.HasExtension target.valuation] in
/-- Under unique extension, the actual valuation produced by Chevalley's
theorem can be chosen together with all construction data and is equivalent to
the chosen target valuation.  This is the finite-extension frontier form of
Chevalley plus uniqueness: it does not merely return a valuation subring, but
keeps the extension valuation, exact base pullback, integral-closure
containment, local map, residue injection, valuation equivalence, and
valuation-ring equality for the same witness. -/
theorem exists_chevalley_extension_valuation_eq_target_of_hasUniqueValuationExtension

    (huniq : HasUniqueValuationExtension.{u, v, w, x, w}
      (base := base) (target := target)) :
    ∃ ΓL : Type w,
      ∃ _ : LinearOrderedCommGroupWithZero ΓL,
        ∃ vL : _root_.Valuation L ΓL,
          ∃ hExt : base.valuation.HasExtension vL,
            letI : base.valuation.HasExtension vL := hExt
            letI : Algebra base.valuationSubring vL.valuationSubring := by
              change Algebra base.valuation.valuationSubring vL.valuationSubring
              infer_instance
            letI : IsLocalHom
                (algebraMap base.valuationSubring vL.valuationSubring) := by
              exact Valuation.integerMap_isLocalHom_of_hasExtension
                base.valuation vL
            (∀ a : K, algebraMap K L a ∈ vL.valuationSubring ↔
              a ∈ base.valuation.valuationSubring) ∧
            (∀ z : integralClosure base.valuationSubring L,
              (z : L) ∈ vL.valuationSubring) ∧
            (IsLocalRing.maximalIdeal vL.valuationSubring).LiesOver
              (IsLocalRing.maximalIdeal base.valuationSubring) ∧
            IsLocalHom
              (algebraMap base.valuationSubring vL.valuationSubring) ∧
            Function.Injective
              (IsLocalRing.ResidueField.map
                (algebraMap base.valuationSubring vL.valuationSubring)) ∧
            target.valuation.IsEquiv vL ∧
            target.valuation.valuationSubring = vL.valuationSubring := by
  obtain ⟨ΓL, hΓL, vL, hExt, hpullback, hIntegral, hlies, hlocal,
      hResidue⟩ :=
    ValuationTheory.DiscreteValuationField.Valuation.chevalley_exists_extension_valuation_with_pullback_integralClosure_local_data
      (L := L) base.valuation
  let : LinearOrderedCommGroupWithZero ΓL := hΓL
  let : base.valuation.HasExtension vL := hExt
  let : Algebra base.valuationSubring vL.valuationSubring := by
    change Algebra base.valuation.valuationSubring vL.valuationSubring
    infer_instance
  let : IsLocalHom
      (algebraMap base.valuationSubring vL.valuationSubring) := by
    exact Valuation.integerMap_isLocalHom_of_hasExtension
      base.valuation vL
  have hEquiv : target.valuation.IsEquiv vL :=
    @huniq ΓL inferInstance vL inferInstance
  have hSubring : target.valuation.valuationSubring = vL.valuationSubring :=
    valuationSubring_eq_of_valuation_isEquiv target hEquiv
  exact ⟨ΓL, inferInstance, vL, inferInstance, hpullback, hIntegral, hlies,
    hlocal, hResidue, hEquiv, hSubring⟩


/-- In a finite separable extension, any valuation subring whose valuation
extends the base valuation is the chosen target valuation ring. -/
theorem target_valuationSubring_eq_of_finite_separable

    [Algebra.IsSeparable K L]
    (B : ValuationSubring L) [base.valuation.HasExtension B.valuation] :
    target.valuation.valuationSubring = B := by
  exact target_valuationSubring_eq_of_hasUniqueValuationExtension
    (K := K) (L := L) (base := base) (target := target)
    ((hasUniqueValuationExtension_of_finite_separable base target) :
      HasUniqueValuationExtension.{u, v, w, x, w}
        (base := base) (target := target)) B

/-- In a finite separable extension, the chosen target valuation ring is the
actual integral closure of the base valuation ring in `L`. -/
theorem target_valuationSubring_isIntegralClosure_of_finite_separable

    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    IsIntegralClosure target.valuationSubring base.valuationSubring L := by
  let hval := (integralClosure_mem_or_inv_of_finite_separable base target)
  let B :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
      (L := L) base.valuation hval
  let : base.valuation.HasExtension B.valuation :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_hasExtension
      (L := L) base.valuation hval
  have htarget_eq : target.valuation.valuationSubring = B :=
    (target_valuationSubring_eq_of_finite_separable base target) B
  have hB : IsIntegralClosure B base.valuationSubring L :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_isIntegralClosure
      (L := L) base.valuation hval
  change IsIntegralClosure target.valuation.valuationSubring base.valuationSubring L
  rw [htarget_eq]
  exact hB

/-- Module-finiteness of the target valuation ring in a finite separable
extension, with no separate integral-closure certificate. -/
theorem moduleFinite_target_valuationSubring_of_finite_separable

    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    Module.Finite base.valuationSubring target.valuationSubring := by
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L :=
    (target_valuationSubring_isIntegralClosure_of_finite_separable base target)
  exact moduleFinite_target_valuationSubring_of_isIntegralClosure
    (K := K) (L := L) base target





/-- Torsion-freeness of the target valuation ring over the base valuation ring
in a finite separable extension, with no separate integral-closure
certificate. -/
theorem moduleIsTorsionFree_target_valuationSubring_of_finite_separable

    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    Module.IsTorsionFree base.valuationSubring target.valuationSubring := by
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L :=
    (target_valuationSubring_isIntegralClosure_of_finite_separable base target)
  let : IsFractionRing base.valuationSubring K :=
    base_valuationSubring_isFractionRing (K := K) base
  let : FaithfulSMul base.valuationSubring L :=
    FaithfulSMul.of_field_isFractionRing base.valuationSubring L K L
  let : Module.IsTorsionFree base.valuationSubring L := inferInstance
  exact IsIntegralClosure.isTorsionFree base.valuationSubring L



/-- The canonical ramification index times residue degree is the field degree for a
finite separable extension, with no separate integral-closure certificate. -/
theorem ramificationIndex_mul_residueDegree_eq_degree_of_finite_separable

    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    (ValuedExtension.ramificationIndex base.toDVF target.toDVF) * (ValuedExtension.residueDegree base.toDVF target.toDVF) = (ValuedExtension.degree base.toDVF target.toDVF) := by
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L :=
    (target_valuationSubring_isIntegralClosure_of_finite_separable base target)
  exact (ramificationIndex_mul_residueDegree_eq_degree_of_isIntegralClosure base target)









end ValuedExtension
end DiscreteValuationField

end

end ValuationTheory
