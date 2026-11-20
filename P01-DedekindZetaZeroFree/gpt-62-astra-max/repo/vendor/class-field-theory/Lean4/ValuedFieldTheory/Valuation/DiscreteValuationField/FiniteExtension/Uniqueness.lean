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
        (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv base.valuation hval)
        target.valuation.valuationSubring
        (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension base.valuation target.valuation hval) =
        IsLocalRing.maximalIdeal
          (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv base.valuation hval))
    (hcenter :
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
          ValuationSubring.idealOfLE
            (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv base.valuation hval)
            v'.valuationSubring
            (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension base.valuation v' hval) =
            IsLocalRing.maximalIdeal
              (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv base.valuation hval)) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let B :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
       base.valuation hval
  have htarget_le :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
       base.valuation target.valuation hval
  intro Gamma' _ v' hExt
  let := hExt
  have hv_le :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
       base.valuation v' hval
  exact valuation_isEquiv_of_valuationSubring_eq target v' ((ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal
    B target.valuation.valuationSubring htarget_le
    (by exact htargetCenter)).trans (ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal
    B v'.valuationSubring hv_le
    (by simp_all [B, hv_le])).symm)

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
        ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv base.valuation hval
      let i : base.valuationSubring →+* B :=
        integralClosureValuationSubringIntegerMapOfMemOrInv base hval
      ∀ P : Ideal B, P.IsPrime → P.comap i = base.maximalIdeal →
        P = IsLocalRing.maximalIdeal B) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let B :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
       base.valuation hval
  let i :=
    integralClosureValuationSubringIntegerMapOfMemOrInv
        base hval
  refine
    (hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_center_eq_maximalIdeal
      (K := K) (L := L) (base := base) (target := target)  hval ?_ ?_ :
        HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target))
  · let htarget_le :=
      ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
         base.valuation target.valuation hval
    exact hunique
      (ValuationSubring.idealOfLE B target.valuation.valuationSubring htarget_le)
      (by infer_instance)
      (by
        apply idealOfLE_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal)
  · intro Gamma' _ v' hExt
    let := hExt
    let hv_le :=
      ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
         base.valuation v' hval
    exact hunique
      (ValuationSubring.idealOfLE B v'.valuationSubring hv_le)
      (by infer_instance)
      (by
        apply idealOfLE_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal)

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
      exact prime_eq_maximalIdeal_of_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal base hval)

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
  let :=
    (integralClosure_isLocalRing_of_base_maximal_fiber_subsingleton base target)
  exact
    (hasUniqueValuationExtension_of_integralClosure_isLocalRing (L := L) (base := base) (target := target) :
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
  let :=
    (integralClosure_base_maximal_fiber_subsingleton_of_henselianRing_maximalIdeal_map base target)
  exact
    (hasUniqueValuationExtension_of_integralClosure_base_maximal_fiber_subsingleton (L := L) (base := base) (target := target) :
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
  let :=
    (integralClosure_base_maximal_map_henselianRing base target)
  apply hasUniqueValuationExtension_of_integralClosure_base_maximal_map_henselianRing

/-- In a finite separable extension of complete DVFs, the actual integral
closure of the base valuation ring is itself a valuation ring. -/
theorem integralClosure_mem_or_inv_of_finite_separable
    (target : CompleteDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [Algebra.IsSeparable K L] :
    ∀ z : L,
      z ∈ (integralClosure base.valuationSubring L).toSubring ∨
        z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring := by
  let :=
    (integralClosure_base_maximal_map_henselianRing base target)
  let :=
    (integralClosure_base_maximal_fiber_subsingleton_of_henselianRing_maximalIdeal_map base target)
  let :=
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
  simpa using ((_root_.Valuation.isEquiv_iff_valuationSubring
    target.valuation B.valuation).1 (huniq B.valuation))

/-- In a finite separable extension, any valuation subring whose valuation
extends the base valuation is the chosen target valuation ring. -/
theorem target_valuationSubring_eq_of_finite_separable

    [Algebra.IsSeparable K L]
    (B : ValuationSubring L) [base.valuation.HasExtension B.valuation] :
    target.valuation.valuationSubring = B := target_valuationSubring_eq_of_hasUniqueValuationExtension (L := L) (base := base) (target := target)
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
       base.valuation hval
  let :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_hasExtension
       base.valuation hval
  have htarget_eq :=
    (target_valuationSubring_eq_of_finite_separable base target) B
  change IsIntegralClosure target.valuation.valuationSubring base.valuationSubring L
  rw [htarget_eq]
  exact ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_isIntegralClosure
    base.valuation hval

/-- Module-finiteness of the target valuation ring in a finite separable
extension, with no separate integral-closure certificate. -/
theorem moduleFinite_target_valuationSubring_of_finite_separable

    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    Module.Finite base.valuationSubring target.valuationSubring := by
  let :=
    (target_valuationSubring_isIntegralClosure_of_finite_separable base target)
  exact moduleFinite_target_valuationSubring_of_isIntegralClosure
      base target

/-- Torsion-freeness of the target valuation ring over the base valuation ring
in a finite separable extension, with no separate integral-closure
certificate. -/
theorem moduleIsTorsionFree_target_valuationSubring_of_finite_separable

    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    Module.IsTorsionFree base.valuationSubring target.valuationSubring := by
  let :=
    (target_valuationSubring_isIntegralClosure_of_finite_separable base target)
  let :=
    base_valuationSubring_isFractionRing base
  let :=
    FaithfulSMul.of_field_isFractionRing base.valuationSubring L K L
  let : Module.IsTorsionFree base.valuationSubring L := inferInstance
  exact IsIntegralClosure.isTorsionFree base.valuationSubring L

/-- The canonical ramification index times residue degree is the field degree for a
finite separable extension, with no separate integral-closure certificate. -/
theorem ramificationIndex_mul_residueDegree_eq_degree_of_finite_separable

    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    (ValuedExtension.ramificationIndex base.toDVF target.toDVF) * (ValuedExtension.residueDegree base.toDVF target.toDVF) = (ValuedExtension.degree base.toDVF target.toDVF) := by
  let :=
    (target_valuationSubring_isIntegralClosure_of_finite_separable base target)
  grind [ramificationIndex_mul_residueDegree_eq_degree_of_isIntegralClosure]

end ValuedExtension
end DiscreteValuationField

end

end ValuationTheory
