module

public import Mathlib.Algebra.GroupWithZero.Torsion
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.RingTheory.DedekindDomain.Instances
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.RingTheory.NormalClosure
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


namespace LocalClassFieldTheory

open LocalFieldTheory

/-!
# Finite local reciprocity: normalized valuation of field norms

This file supplies the local-field calculation used when the abstract
class-formation framework is specialized to separable-closure units.  All
ramification and residue degrees below are the actual invariants of the
valuation-ring extension; no packaged norm-valuation hypothesis is assumed.
-/

noncomputable section

universe u v w

open scoped BigOperators ValuativeRel
open IsNonarchimedeanLocalField

section SeparableIdealNorm

variable (R : Type u) (S : Type v)
  [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [IsIntegrallyClosed R] [IsIntegrallyClosed S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]

local instance : Algebra (FractionRing R) (FractionRing S) :=
  FractionRing.liftAlgebra R (FractionRing S)

/-- A normal closure inside a separable ambient field is separable over the
base whenever the extension being closed is separable.  Keeping this
field-theoretic step separate prevents the integral-closure transport below
from repeatedly elaborating the full `iSup` of embedding ranges. -/
theorem intermediateNormalClosure_isSeparable_of_isSeparable
    (K : Type u) (L : Type v) (A : Type w)
    [Field K] [Field L] [Field A]
    [Algebra K L] [Algebra K A] [Algebra L A]
    [IsScalarTower K L A] [Algebra.IsSeparable K L] :
    Algebra.IsSeparable K (IntermediateField.normalClosure K L A) := by
  change Algebra.IsSeparable K ↥(⨆ f : L →ₐ[K] A, f.fieldRange)
  exact IntermediateField.isSeparable_iSup K A
    (h := fun f => AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField f))

/-- The field-theoretic normal closure of a finite separable extension is
Galois, with no perfectness assumption on the base. -/
theorem intermediateNormalClosure_isGalois_of_isSeparable
    (K : Type u) (L : Type v) (A : Type w)
    [Field K] [Field L] [Field A]
    [Algebra K L] [Algebra K A] [Algebra L A]
    [IsScalarTower K L A] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [Normal K A] :
    IsGalois K (IntermediateField.normalClosure K L A) := by
  exact
    { to_isSeparable :=
        intermediateNormalClosure_isSeparable_of_isSeparable K L A
      to_normal := normalClosure.normal K L A }

/-- A finite extension remains finite over the field-theoretic normal
closure when viewed from the top of the tower. -/
theorem intermediateNormalClosure_finiteDimensional_top
    (K : Type u) (L : Type v) (A : Type w)
    [Field K] [Field L] [Field A]
    [Algebra K L] [Algebra K A] [Algebra L A]
    [IsScalarTower K L A] [FiniteDimensional K L] :
    let E := IntermediateField.normalClosure K L A
    letI : Algebra L E := normalClosure.algebra K L A
    FiniteDimensional L E := 
  Module.Finite.right K L (IntermediateField.normalClosure K L A)

omit [IsIntegrallyClosed R] [IsIntegrallyClosed S] in
/-- The integral normal closure has the field-theoretic normal closure as
its fraction field. -/
theorem ringNormalClosure_isFractionRing :
    let K := FractionRing R
    let L := FractionRing S
    let A := AlgebraicClosure L
    let E := IntermediateField.normalClosure K L A
    let T := Ring.NormalClosure R S
    letI : Algebra L E := normalClosure.algebra K L A
    letI : Algebra S E := ((algebraMap L E).comp (algebraMap S L)).toAlgebra
    letI : Algebra T E := by
      change Algebra (integralClosure S E) E
      infer_instance
    IsFractionRing T E := by
  let K := FractionRing R
  let L := FractionRing S
  let A := AlgebraicClosure L
  let E := IntermediateField.normalClosure K L A
  let : Algebra L E := normalClosure.algebra K L A
  let T := Ring.NormalClosure R S
  let : Algebra S E := ((algebraMap L E).comp (algebraMap S L)).toAlgebra
  let : IsScalarTower S L E := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  let : Algebra T E := by
    change Algebra (integralClosure S E) E
    infer_instance
  let : FiniteDimensional L E :=
    intermediateNormalClosure_finiteDimensional_top K L A
  change IsFractionRing (integralClosure S E) E
  exact integralClosure.isFractionRing_of_finite_extension L E

omit [IsIntegrallyClosed R] [IsIntegrallyClosed S] in
/-- Transport Galoisness from the field-theoretic normal closure to the
fraction field of the integral normal closure. -/
theorem ringNormalClosure_isGalois_transport :
    let K := FractionRing R
    let L := FractionRing S
    let A := AlgebraicClosure L
    let E := IntermediateField.normalClosure K L A
    let T := Ring.NormalClosure R S
    letI : Algebra K E := SubalgebraClass.toAlgebra E
    letI : Algebra K (FractionRing T) :=
      FractionRing.liftAlgebra R (FractionRing T)
    IsGalois K E → IsGalois K (FractionRing T) := by
  simp only
  let K := FractionRing R
  let L := FractionRing S
  let A := AlgebraicClosure L
  let E := IntermediateField.normalClosure K L A
  let : Algebra L E := normalClosure.algebra K L A
  let T := Ring.NormalClosure R S
  let : Algebra S E := ((algebraMap L E).comp (algebraMap S L)).toAlgebra
  let : IsScalarTower S L E := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  let : Algebra T E := by
    change Algebra (integralClosure S E) E
    infer_instance
  let : IsScalarTower S T E :=
    IsScalarTower.subalgebra' S E E (integralClosure S E)
  let : IsScalarTower R L E := IsScalarTower.to₁₃₄ R K L E
  let : IsScalarTower R S E := IsScalarTower.to₁₂₄ R S L E
  let : IsScalarTower R T E := IsScalarTower.to₁₃₄ R S T E
  let : IsFractionRing T E := ringNormalClosure_isFractionRing R S
  intro hGalois
  refine IsGalois.of_equiv_equiv (F := K) («E» := E)
    (f := (FractionRing.algEquiv R K).symm.toRingEquiv)
    (g := (FractionRing.algEquiv T E).symm.toRingEquiv) ?_
  ext
  simpa using IsFractionRing.algEquiv_commutes
    (FractionRing.algEquiv R K).symm
    (FractionRing.algEquiv T E).symm _

omit [IsIntegrallyClosed R] in
/-- Finiteness of the integral normal closure follows from separability of
the original fraction-field extension. -/
theorem ringNormalClosure_moduleFinite_of_isSeparable
    [IsNoetherianRing S]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)] :
    Module.Finite S (Ring.NormalClosure R S) := by
  let K := FractionRing R
  let L := FractionRing S
  let A := AlgebraicClosure L
  let E := IntermediateField.normalClosure K L A
  let : Algebra L E := normalClosure.algebra K L A
  let T := Ring.NormalClosure R S
  let : Algebra S E := ((algebraMap L E).comp (algebraMap S L)).toAlgebra
  let : IsScalarTower S L E := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  let : Algebra T E := by
    change Algebra (integralClosure S E) E
    infer_instance
  let : IsScalarTower S T E :=
    IsScalarTower.subalgebra' S E E (integralClosure S E)
  let : IsIntegralClosure T S E := integralClosure.isIntegralClosure S E
  let : FiniteDimensional L E :=
    intermediateNormalClosure_finiteDimensional_top K L A
  let : Algebra.IsSeparable K E :=
    intermediateNormalClosure_isSeparable_of_isSeparable K L A
  let : Algebra.IsSeparable L E :=
    Algebra.isSeparable_tower_top_of_isSeparable K L E
  change Module.Finite S (integralClosure S E)
  exact IsIntegralClosure.finite S L E (integralClosure S E)

end SeparableIdealNorm

section SeparableIdealNormDedekind

variable (R : Type u) (S : Type v)
  [CommRing R] [IsDomain R] [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]

local instance : Algebra (FractionRing R) (FractionRing S) :=
  FractionRing.liftAlgebra R (FractionRing S)

/-- The same separable normal-closure construction is Dedekind when the
original rings are Dedekind. -/
theorem ringNormalClosure_isDedekindDomain_of_isSeparable
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)] :
    IsDedekindDomain (Ring.NormalClosure R S) := by
  let K := FractionRing R
  let L := FractionRing S
  let A := AlgebraicClosure L
  let E := IntermediateField.normalClosure K L A
  let : Algebra L E := normalClosure.algebra K L A
  let T := Ring.NormalClosure R S
  let : Algebra S E := ((algebraMap L E).comp (algebraMap S L)).toAlgebra
  let : IsScalarTower S L E := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  let : Algebra T E := by
    change Algebra (integralClosure S E) E
    infer_instance
  let : IsScalarTower S T E :=
    IsScalarTower.subalgebra' S E E (integralClosure S E)
  let : IsIntegralClosure T S E := integralClosure.isIntegralClosure S E
  let : FiniteDimensional L E :=
    intermediateNormalClosure_finiteDimensional_top K L A
  let : Algebra.IsSeparable K E :=
    intermediateNormalClosure_isSeparable_of_isSeparable K L A
  let : Algebra.IsSeparable L E :=
    Algebra.isSeparable_tower_top_of_isSeparable K L E
  change IsDedekindDomain (integralClosure S E)
  exact integralClosure.isDedekindDomain S L E

end SeparableIdealNormDedekind

section SeparableIdealNormGalois

variable (R : Type u) (S : Type v)
  [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]

local instance : Algebra (FractionRing R) (FractionRing S) :=
  FractionRing.liftAlgebra R (FractionRing S)

/-- The normal closure of a finite separable extension of fraction fields is
Galois without assuming that the base fraction field is perfect.  Mathlib's
default instance uses perfectness because it treats arbitrary finite
extensions; here separability is precisely the available hypothesis. -/
theorem ringNormalClosure_isGalois_of_isSeparable
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)] :
    IsGalois (FractionRing R)
      (FractionRing (Ring.NormalClosure R S)) := by
  let K := FractionRing R
  let L := FractionRing S
  let A := AlgebraicClosure L
  let E := IntermediateField.normalClosure K L A
  let T := Ring.NormalClosure R S
  exact ringNormalClosure_isGalois_transport R S
    (intermediateNormalClosure_isGalois_of_isSeparable K L A)

end SeparableIdealNormGalois

section SeparableIdealNormRelNorm

variable (R : Type u) (S : Type v)
  [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]

attribute [local instance] FractionRing.liftAlgebra

/-- Relative ideal norm of a maximal ideal in a finite separable extension.
This is the separable replacement for mathlib's perfect-base theorem and is
proved by the same normal-closure descent. -/
theorem relNorm_eq_pow_inertiaDeg_of_isSeparable
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    (P : Ideal S) (p : Ideal R) [P.LiesOver p]
    [P.IsMaximal] [p.IsMaximal] :
    Ideal.relNorm R P = p ^ P.inertiaDeg R := by
  let T := Ring.NormalClosure R S
  let : Module.Finite S T :=
    ringNormalClosure_moduleFinite_of_isSeparable R S
  let : Module.Finite R T := Module.Finite.trans S T
  let : IsDedekindDomain T :=
    ringNormalClosure_isDedekindDomain_of_isSeparable R S
  let : IsScalarTower R (FractionRing S) (FractionRing T) :=
    IsScalarTower.to₁₃₄ R S (FractionRing S) (FractionRing T)
  let : IsScalarTower (FractionRing R) (FractionRing S) (FractionRing T) :=
    IsScalarTower.of_algebraMap_eq' (by
      apply IsFractionRing.ringHom_ext (A := R)
      intro x
      rw [← IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing T)]
      change algebraMap R (FractionRing T) x =
        algebraMap (FractionRing S) (FractionRing T)
          (algebraMap (FractionRing R) (FractionRing S)
            (algebraMap R (FractionRing R) x))
      rw [← IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing S),
        ← IsScalarTower.algebraMap_apply R (FractionRing S) (FractionRing T)])
  let : IsGalois (FractionRing R) (FractionRing T) :=
    ringNormalClosure_isGalois_of_isSeparable R S
  let : IsGalois (FractionRing S) (FractionRing T) :=
    IsGalois.tower_top_of_isGalois
      (FractionRing R) (FractionRing S) (FractionRing T)
  obtain ⟨Q, hQm, hQP⟩ : ∃ Q : Ideal T, Q.IsMaximal ∧ Q.LiesOver P :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral P
  let : Q.IsMaximal := hQm
  let : Q.LiesOver P := hQP
  let : Q.LiesOver p := Ideal.LiesOver.trans Q P p
  have h := Ideal.relNorm_eq_pow_of_isPrime_isGalois Q p
  rwa [← Ideal.relNorm_relNorm R S,
    Ideal.relNorm_eq_pow_of_isPrime_isGalois Q P, map_pow,
    Ideal.inertiaDeg_tower (R := R) P Q, pow_mul, pow_left_inj] at h
  exact Nat.ne_zero_iff_zero_lt.mpr (Ideal.inertiaDeg_pos Q S)

end SeparableIdealNormRelNorm

attribute [local instance] FractionRing.liftAlgebra

/-- Separability of an actual field extension transfers to the canonical
fraction fields of its valuation integer rings. -/
theorem fractionRing_integerRing_isSeparable
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L]
    [Algebra K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)] :
    Algebra.IsSeparable (FractionRing 𝒪[K]) (FractionRing 𝒪[L]) := by
  apply Algebra.IsSeparable.of_equiv_equiv
    (FractionRing.algEquiv 𝒪[K] K).symm.toRingEquiv
    (FractionRing.algEquiv 𝒪[L] L).symm.toRingEquiv
  ext x
  exact IsFractionRing.algEquiv_commutes
    (FractionRing.algEquiv 𝒪[K] K).symm
    (FractionRing.algEquiv 𝒪[L] L).symm x

/-- In a finite separable local-field extension, the relative ideal norm of
the upstairs maximal ideal is the residue-degree power of the base maximal
ideal. -/
theorem relNorm_maximalIdeal_eq_pow_residue_finrank
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] :
    Ideal.relNorm 𝒪[K] (𝓂[L] : Ideal 𝒪[L]) =
      (𝓂[K] : Ideal 𝒪[K]) ^ Module.finrank 𝓀[K] 𝓀[L] := by
  let : Algebra.IsSeparable (FractionRing 𝒪[K]) (FractionRing 𝒪[L]) :=
    fractionRing_integerRing_isSeparable K L
  have h := relNorm_eq_pow_inertiaDeg_of_isSeparable
    𝒪[K] 𝒪[L] (𝓂[L] : Ideal 𝒪[L]) (𝓂[K] : Ideal 𝒪[K])
  rw [Ideal.inertiaDeg_eq_of_isMaximal
    (𝓂[K] : Ideal 𝒪[K]) (𝓂[L] : Ideal 𝒪[L])] at h
  exact h

/-- The norm of the chosen upstairs prime element has base normalized value
the negative of the actual residue degree, for every finite separable
extension (not only a Galois one). -/
theorem v_normUnits_integerRingUniformizerFieldUnit_of_isSeparable
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    v K (Additive.ofMul
        (normUnits K L (integerRingUniformizerFieldUnit L))) =
      -(Module.finrank 𝓀[K] 𝓀[L] : Int) := by
  let : Module.Finite 𝒪[K] 𝒪[L] :=
    IsIntegralClosure.finite 𝒪[K] K L 𝒪[L]
  let f : Nat := Module.finrank 𝓀[K] 𝓀[L]
  have hspan :
      Ideal.span
          (Set.singleton (Algebra.intNorm 𝒪[K] 𝒪[L]
            (chosenIntegerRingUniformizer L))) =
        Ideal.span (Set.singleton (chosenIntegerRingUniformizer K ^ f)) := by
    calc
      Ideal.span
          (Set.singleton (Algebra.intNorm 𝒪[K] 𝒪[L]
            (chosenIntegerRingUniformizer L))) =
          Ideal.relNorm 𝒪[K]
            (Ideal.span ({chosenIntegerRingUniformizer L} : Set 𝒪[L])) := by
        exact (Ideal.spanNorm_singleton (R := 𝒪[K])
          (r := chosenIntegerRingUniformizer L)).symm
      _ = Ideal.relNorm 𝒪[K] (𝓂[L] : Ideal 𝒪[L]) := by
        rw [chosenIntegerRingUniformizer_maximalIdeal_eq L]
      _ = (𝓂[K] : Ideal 𝒪[K]) ^ f := by
        simpa [f] using relNorm_maximalIdeal_eq_pow_residue_finrank K L
      _ = Ideal.span (Set.singleton (chosenIntegerRingUniformizer K ^ f)) :=
        maximalIdeal_pow_eq_span_uniformizer_pow K f
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  have hfieldUnits :
      normUnits K L (integerRingUniformizerFieldUnit L) *
        integerUnitsToFieldUnits K u =
      integerRingUniformizerFieldUnit K ^ f := by
    apply Units.ext
    have huField := congrArg (algebraMap 𝒪[K] K) hu
    rw [map_mul, Algebra.algebraMap_intNorm (K := K) (L := L)] at huField
    change
      Algebra.norm K (algebraMap 𝒪[L] L (chosenIntegerRingUniformizer L)) *
          algebraMap 𝒪[K] K (u : 𝒪[K]) =
        algebraMap 𝒪[K] K (chosenIntegerRingUniformizer K) ^ f
    exact huField
  have hvalue := congrArg
    (fun z : Kˣ => v K (Additive.ofMul z)) hfieldUnits
  change v K (Additive.ofMul
      (normUnits K L (integerRingUniformizerFieldUnit L) *
        integerUnitsToFieldUnits K u)) =
    v K (Additive.ofMul (integerRingUniformizerFieldUnit K ^ f)) at hvalue
  rw [v_mul, v_integerUnitsToFieldUnits, add_zero, v_pow,
    v_integerRingUniformizerFieldUnit] at hvalue
  simpa [f] using hvalue

/-- The norm of the positive generator (the inverse chosen prime element) has
base normalized value equal to the actual residue degree. -/
theorem v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparable
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    v K (Additive.ofMul
        (normUnits K L (inverseIntegerRingUniformizerFieldUnit L))) =
      (Module.finrank 𝓀[K] 𝓀[L] : Int) := by
  rw [inverseIntegerRingUniformizerFieldUnit, map_inv, v_inv,
    v_normUnits_integerRingUniformizerFieldUnit_of_isSeparable]
  simp

/-- Finite local reciprocity, normalized norm calculation for every finite separable
local-field extension: the normalized value of a field norm is the actual
residue degree times the upstairs normalized value. -/
theorem v_normUnits_eq_residue_finrank_mul_of_isSeparable
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (x : Lˣ) :
    v K (Additive.ofMul (normUnits K L x)) =
      (Module.finrank 𝓀[K] 𝓀[L] : Int) *
        v L (Additive.ofMul x) := by
  let ϖ : Lˣ := inverseIntegerRingUniformizerFieldUnit L
  have hϖ : v L (Additive.ofMul ϖ) = 1 :=
    v_inverseIntegerRingUniformizerFieldUnit L
  let n : Int := v L (Additive.ofMul x)
  let a : 𝒪[L]ˣ := uniformizerUnitFactor L ϖ hϖ x
  have haNorm :
      normUnits K L (integerUnitsToFieldUnits L a) =
        integerUnitsToFieldUnits K (normIntegerUnits K L a) := by
    rfl
  have hx : integerUnitsToFieldUnits L a * ϖ ^ n = x := 
    uniformizerUnitFactor_mul_uniformizer_zpow L ϖ hϖ x
  have hxNorm :
      normUnits K L x =
        integerUnitsToFieldUnits K (normIntegerUnits K L a) *
          (normUnits K L ϖ) ^ n := by
    calc
      normUnits K L x =
          normUnits K L (integerUnitsToFieldUnits L a * ϖ ^ n) :=
        congrArg (normUnits K L) hx.symm
      _ = normUnits K L (integerUnitsToFieldUnits L a) *
          (normUnits K L ϖ) ^ n := by
        simp only [map_mul, map_zpow]
      _ = integerUnitsToFieldUnits K (normIntegerUnits K L a) *
          (normUnits K L ϖ) ^ n := by rw [haNorm]
  rw [hxNorm, v_mul, v_integerUnitsToFieldUnits, zero_add, v_zpow,
    v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparable]
  simp only [n]
  ring

/-- The Galois specialization of the finite-separable normalized norm
calculation in the finite local reciprocity construction. -/
theorem v_normUnits_eq_residue_finrank_mul_of_isGalois
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (x : Lˣ) :
    v K (Additive.ofMul (normUnits K L x)) =
      (Module.finrank 𝓀[K] 𝓀[L] : Int) *
        v L (Additive.ofMul x) :=
  v_normUnits_eq_residue_finrank_mul_of_isSeparable K L x
