module

public import Mathlib

public import ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameters
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Automorphisms of standard Lubin--Tate level fields

The finite unit parameters at primitive level `n + 1` act on the chosen
primitive division point.  Once the resulting roots are regarded as elements
of the simple level field, the canonical power basis lifts them to algebra
automorphisms.  Faithfulness of the finite action and the parameter-cardinality
formula then show that the automorphism group has cardinality equal to the
field degree, hence that every standard level is Galois.
-/

noncomputable section

open scoped Polynomial PowerSeries

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open ValuationTheory.DiscreteValuationField

variable {K : Type u} [Field K]

 noncomputable local instance (priority := 50)
    standardLubinTateLevelAutomorphismCoefficientUniformSpace
    (F : LocalField.{u, v} K) :
    UniformSpace F.valuationSubring :=
  ⊥

 noncomputable local instance
    standardLubinTateLevelAutomorphismTargetWithIdeal
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    WithIdeal
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring where
  i := (standardLubinTateLevelCompleteDVF hπ n).maximalIdeal

 noncomputable local instance
    standardLubinTateLevelAutomorphismTargetCompleteSpace
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    CompleteSpace
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring := by
  let target := standardLubinTateLevelCompleteDVF hπ n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).1

 noncomputable local instance
    standardLubinTateLevelAutomorphismTargetT2Space
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    T2Space
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring := by
  let target := standardLubinTateLevelCompleteDVF hπ n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).2

section
variable (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ)
include F π hπ n
/-- A finite parameter root, regarded as an element of its standard level
field through the analytically constructed integral action. -/
noncomputable def standardLubinTateUnitParameterLevelRoot
      (a : standardLubinTateUnitParameter F n)  :=
  standardLubinTatePrimitiveLevelAction hπ n
    (standardLubinTateUnitParameterChosenRepresentative F n a)

/-- The level-field realization of a parameter root agrees with its ambient
separable-closure realization. -/
@[simp]
theorem standardLubinTateUnitParameterLevelRoot_coe
      (a : standardLubinTateUnitParameter F n) :
    (standardLubinTateUnitParameterLevelRoot F hπ n a :
      SeparableClosure K) =
        standardLubinTateUnitParameterRoot F hπ n a := rfl

/-- Distinct finite unit parameters give distinct roots inside the standard
level field. -/
theorem standardLubinTateUnitParameterLevelRoot_injective
      :
    Function.Injective
      (standardLubinTateUnitParameterLevelRoot F hπ n) := by
  intro a b hab
  let u :=
    standardLubinTateUnitParameterChosenRepresentative F n a
  let w :=
    standardLubinTateUnitParameterChosenRepresentative F n b
  have hroot :
      standardLubinTatePrimitiveRootAction hπ n u =
        standardLubinTatePrimitiveRootAction hπ n w := by
    have hcoe := congrArg
      (fun z : standardLubinTateLevelField hπ n =>
        (z : SeparableClosure K)) hab
    exact hcoe
  have hdiv  :=
    (standardLubinTatePrimitiveRootAction_eq_iff_div_mem_higherPrincipalUnitGroup
      hπ n u w).mp hroot
  calc
    a = standardLubinTateUnitParameterClass F n u := by
      simp [u]
    _ = standardLubinTateUnitParameterClass F n w :=
      (standardLubinTateUnitParameterClass_eq_iff_div_mem
        F n u w).2 hdiv
    _ = b := by
      simp [w]

/-- The identity parameter gives the chosen power-basis generator. -/
@[simp]
theorem standardLubinTateUnitParameterLevelRoot_one
      :
    standardLubinTateUnitParameterLevelRoot F hπ n 1 =
      (standardLubinTateLevelPowerBasis hπ n).gen := by
  apply Subtype.ext
  rw [standardLubinTateUnitParameterLevelRoot_coe]
  have hroot :
      standardLubinTateUnitParameterRoot F hπ n 1 =
        standardLubinTatePrimitiveRootAction hπ n
          (1 : F.valuationSubringˣ) := by
    apply standardLubinTateUnitParameterRoot_class
  rw [hroot, standardLubinTatePrimitiveRootAction_one]
  exact (standardLubinTateLevelGenerator_coe hπ n).symm

/-- A parameter root annihilates the minimal polynomial of the canonical
level-field generator. -/
theorem standardLubinTateUnitParameterLevelRoot_aeval_minpoly
      (a : standardLubinTateUnitParameter F n) :
    Polynomial.aeval (standardLubinTateUnitParameterLevelRoot F hπ n a)
        (minpoly K (standardLubinTateLevelPowerBasis hπ n).gen) = 0 := by
  rw [standardLubinTateLevelPowerBasis_minpoly]
  let ι : standardLubinTateLevelField hπ n →ₐ[K] SeparableClosure K :=
    (standardLubinTateLevelField hπ n).val
  apply ι.injective
  change ι (Polynomial.aeval
    (standardLubinTateUnitParameterLevelRoot F hπ n a)
    (standardLubinTatePrimitivePolynomialOverField F π n)) = ι 0
  rw [← Polynomial.aeval_algHom_apply (f := ι), map_zero]
  change Polynomial.eval₂
    (algebraMap K (SeparableClosure K))
    (standardLubinTateUnitParameterRoot F hπ n a)
    (standardLubinTatePrimitivePolynomialOverField F π n) = 0
  simpa [standardLubinTateUnitParameterRoot, Polynomial.IsRoot, Polynomial.eval_map] using
    standardLubinTateUnitParameterRoot_isRoot F hπ n a

/-- The algebra endomorphism sending the chosen primitive generator to the
root attached to a finite unit parameter. -/
noncomputable def standardLubinTateUnitParameterAlgHom
      (a : standardLubinTateUnitParameter F n) :
    standardLubinTateLevelField hπ n →ₐ[K]
      standardLubinTateLevelField hπ n :=
  (standardLubinTateLevelPowerBasis hπ n).lift
    (standardLubinTateUnitParameterLevelRoot F hπ n a)
    (standardLubinTateUnitParameterLevelRoot_aeval_minpoly F hπ n a)

/-- The parameter endomorphism sends the power-basis generator to the
corresponding parameter root. -/
@[simp]
theorem standardLubinTateUnitParameterAlgHom_apply_gen
      (a : standardLubinTateUnitParameter F n) :
    standardLubinTateUnitParameterAlgHom F hπ n a
        (standardLubinTateLevelPowerBasis hπ n).gen =
      standardLubinTateUnitParameterLevelRoot F hπ n a :=
  (standardLubinTateLevelPowerBasis hπ n).lift_gen _ _

/-- The finite-dimensional parameter endomorphism is an automorphism. -/
noncomputable def standardLubinTateUnitParameterAlgEquiv
      (a : standardLubinTateUnitParameter F n) :
    standardLubinTateLevelField hπ n ≃ₐ[K]
      standardLubinTateLevelField hπ n := by
  letI  :=
    standardLubinTateLevelField_finiteDimensional hπ n
  exact AlgEquiv.ofBijective
    (standardLubinTateUnitParameterAlgHom F hπ n a)
    (AlgHom.bijective
      (standardLubinTateUnitParameterAlgHom F hπ n a))

/-- The parameter automorphism sends the power-basis generator to the
corresponding parameter root. -/
@[simp]
theorem standardLubinTateUnitParameterAlgEquiv_apply_gen
      (a : standardLubinTateUnitParameter F n) :
    standardLubinTateUnitParameterAlgEquiv F hπ n a
        (standardLubinTateLevelPowerBasis hπ n).gen =
      standardLubinTateUnitParameterLevelRoot F hπ n a := by
  rw [standardLubinTateUnitParameterAlgEquiv,
    AlgEquiv.ofBijective_apply,
    standardLubinTateUnitParameterAlgHom_apply_gen]
end


 section
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ)
    (σ : Gal((standardLubinTateLevelField hπ n) / K))
include F π hπ n σ
theorem
    standardLubinTateLevelAlgEquiv_mem_valuationSubring_iff
     
    (x : standardLubinTateLevelField hπ n) :
    x ∈ (standardLubinTateLevelCompleteDVF hπ n).valuation.valuationSubring ↔
      σ x ∈
        (standardLubinTateLevelCompleteDVF hπ n).valuation.valuationSubring := by
  let target := standardLubinTateLevelCompleteDVF hπ n
  let : IsScalarTower F.valuationSubring target.valuationSubring
      (standardLubinTateLevelField hπ n) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsIntegralClosure target.valuationSubring F.valuationSubring
      (standardLubinTateLevelField hπ n) :=
    standardLubinTateLevelCompleteDVF_isIntegralClosure hπ n
  have hforward
      (τ : Gal((standardLubinTateLevelField hπ n) / K))
      {y : standardLubinTateLevelField hπ n}
      (hy : y ∈ target.valuation.valuationSubring) :
      τ y ∈ target.valuation.valuationSubring := by
    have hyIntegral : IsIntegral F.valuationSubring y :=
      (IsIntegralClosure.isIntegral_iff
        (A := target.valuationSubring)
        (R := F.valuationSubring)
        (B := standardLubinTateLevelField hπ n)).2
          ⟨⟨y, hy⟩, rfl⟩
    have hτIntegral : IsIntegral F.valuationSubring (τ y) :=
      IsIntegral.map τ.toAlgHom hyIntegral
    rcases
        (IsIntegralClosure.isIntegral_iff
          (A := target.valuationSubring)
          (R := F.valuationSubring)
          (B := standardLubinTateLevelField hπ n)).1 hτIntegral
      with ⟨z, hz⟩
    exact hz ▸ z.property
  constructor
  · exact hforward σ
  · intro hσx
    have hback := hforward σ.symm hσx
    simpa using hback

 noncomputable def
    standardLubinTateLevelAutomorphismIntegerRingEquiv
      :
    (standardLubinTateLevelCompleteDVF hπ n).valuationSubring ≃+*
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring :=
  higherPrincipalUnitGroup.valuationSubringRingEquivOfPreserves
    (standardLubinTateLevelCompleteDVF hπ n)
    σ.toRingEquiv
    (standardLubinTateLevelAlgEquiv_mem_valuationSubring_iff
      hπ n σ)

@[simp]
private theorem
    standardLubinTateLevelAutomorphismIntegerRingEquiv_apply
     
    (x :
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring) :
    (standardLubinTateLevelAutomorphismIntegerRingEquiv hπ n σ x).val =
        σ x.val :=
  rfl

private theorem
    standardLubinTateLevelAutomorphismIntegerRingEquiv_continuous
      :
    Continuous
      (standardLubinTateLevelAutomorphismIntegerRingEquiv hπ n σ) := by
  let target := standardLubinTateLevelCompleteDVF hπ n
  let r :=
    standardLubinTateLevelAutomorphismIntegerRingEquiv hπ n σ
  apply continuous_of_continuousAt_zero r.toAddMonoidHom
  rw [ContinuousAt, map_zero]
  have hadic : IsAdic target.maximalIdeal := rfl
  apply (hadic.hasBasis_nhds_zero.tendsto_right_iff).2
  intro m _
  apply (hadic.hasBasis_nhds_zero.mem_iff).2
  refine ⟨m, trivial, ?_⟩
  intro x hx
  exact
    (higherPrincipalUnitGroup.valuationSubringRingEquivOfPreserves_mem_maximalIdeal_pow_iff
        target σ.toRingEquiv
        (standardLubinTateLevelAlgEquiv_mem_valuationSubring_iff
          hπ n σ)
        m x).2 hx

private theorem
    standardLubinTateLevelAutomorphismIntegerRingEquiv_comp_coefficientHom
      :
    (standardLubinTateLevelAutomorphismIntegerRingEquiv hπ n σ :
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring →+*
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring).comp
        (standardLubinTateLevelCoefficientHom hπ n) =
      standardLubinTateLevelCoefficientHom hπ n := by
  ext a : 1
  apply Subtype.ext
  simp only [RingHom.comp_apply,
    standardLubinTateLevelCoefficientHom_apply]
  exact σ.commutes (a : K)

private theorem
    standardLubinTateLevelAutomorphismIntegerRingEquiv_primitivePoint_hasEval
      :
    PowerSeries.HasEval
      (standardLubinTateLevelAutomorphismIntegerRingEquiv hπ n σ
        (standardLubinTatePrimitivePointInteger hπ n)) := by
  let r :=
    standardLubinTateLevelAutomorphismIntegerRingEquiv hπ n σ
  let lambda := standardLubinTatePrimitivePointInteger hπ n
  have hlambda :
      Filter.Tendsto (fun m : ℕ => lambda ^ m) Filter.atTop
        (nhds (0 :
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)) :=
    standardLubinTatePrimitivePointInteger_hasEval hπ n
  have hr :
      Filter.Tendsto (fun m : ℕ => r (lambda ^ m)) Filter.atTop
        (nhds (r 0)) :=
    Filter.Tendsto.comp
      (standardLubinTateLevelAutomorphismIntegerRingEquiv_continuous
        hπ n σ).continuousAt
      hlambda
  change Filter.Tendsto
    (fun m : ℕ => (r lambda) ^ m) Filter.atTop (nhds 0)
  simpa only [map_pow, map_zero] using hr

private theorem
    standardLubinTateLevelAutomorphismIntegerRingEquiv_endomorphismValue
     
    (a : F.valuationSubring) :
    standardLubinTateLevelAutomorphismIntegerRingEquiv hπ n σ
        (standardLubinTateEndomorphismValue hπ n a) =
      standardLubinTateEndomorphismEvalAt hπ n
        (standardLubinTateLevelAutomorphismIntegerRingEquiv hπ n σ
          (standardLubinTatePrimitivePointInteger hπ n))
        (standardLubinTateLevelAutomorphismIntegerRingEquiv_primitivePoint_hasEval
          hπ n σ)
        a := by
  let r :=
    standardLubinTateLevelAutomorphismIntegerRingEquiv hπ n σ
  have hcomp :=
    PowerSeries.comp_eval₂
      (φ := standardLubinTateLevelCoefficientHom hπ n)
      continuous_of_discreteTopology
      (standardLubinTatePrimitivePointInteger_hasEval hπ n)
      (ε := (r :
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring →+*
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring))
      (standardLubinTateLevelAutomorphismIntegerRingEquiv_continuous
        hπ n σ)
  have happ := congrArg
    (fun f =>
      f (SameUniformizer.standardLubinTateEndomorphism hπ a))
    hcomp
  rw [
    standardLubinTateLevelAutomorphismIntegerRingEquiv_comp_coefficientHom
      hπ n σ] at happ
  simpa [standardLubinTateEndomorphismValue,
    standardLubinTateEndomorphismEvalAt,
    standardLubinTateLevelPowerSeriesEval,
    PowerSeries.coe_eval₂Hom, Function.comp_apply, r] using happ
end


section
variable (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ)
include F π hπ n
/-- A parameter automorphism transports every parameter root according to
multiplication of finite unit parameters. -/
theorem standardLubinTateUnitParameterAlgEquiv_apply_levelRoot
      (a b : standardLubinTateUnitParameter F n) :
    standardLubinTateUnitParameterAlgEquiv F hπ n a
        (standardLubinTateUnitParameterLevelRoot F hπ n b) =
      standardLubinTateUnitParameterLevelRoot F hπ n (a * b) := by
  let u :=
    standardLubinTateUnitParameterChosenRepresentative F n a
  let w :=
    standardLubinTateUnitParameterChosenRepresentative F n b
  let z :=
    standardLubinTateUnitParameterChosenRepresentative F n (a * b)
  let σ := standardLubinTateUnitParameterAlgEquiv F hπ n a
  let r :=
    standardLubinTateLevelAutomorphismIntegerRingEquiv hπ n σ
  have hrgen :
      r (standardLubinTatePrimitivePointInteger hπ n) =
        standardLubinTatePrimitivePointIntegerAction hπ n u := by
    apply Subtype.ext
    rw [standardLubinTateLevelAutomorphismIntegerRingEquiv_apply,
      standardLubinTatePrimitivePointInteger_coe]
    simp [σ, u, standardLubinTateLevelGenerator,
      standardLubinTateUnitParameterLevelRoot,
      standardLubinTatePrimitiveLevelAction]
  have hrw :
      r (standardLubinTatePrimitivePointIntegerAction hπ n w) =
        standardLubinTatePrimitivePointIntegerAction hπ n (w * u) := by
    calc
      r (standardLubinTatePrimitivePointIntegerAction hπ n w) =
          standardLubinTateEndomorphismEvalAt hπ n
            (r (standardLubinTatePrimitivePointInteger hπ n))
            (standardLubinTateLevelAutomorphismIntegerRingEquiv_primitivePoint_hasEval
              hπ n σ)
            (w : F.valuationSubring) := by
              apply standardLubinTateLevelAutomorphismIntegerRingEquiv_endomorphismValue
      _ =
          standardLubinTateEndomorphismEvalAt hπ n
            (standardLubinTatePrimitivePointIntegerAction hπ n u)
            (standardLubinTatePrimitivePointIntegerAction_hasEval hπ n u)
            (w : F.valuationSubring) := by
              simp only [hrgen]
      _ = standardLubinTatePrimitivePointIntegerAction hπ n (w * u) :=
        (standardLubinTatePrimitivePointIntegerAction_mul
          hπ n w u).symm
  have hclass :
      standardLubinTateUnitParameterClass F n (w * u) =
        standardLubinTateUnitParameterClass F n z := by
    calc
      standardLubinTateUnitParameterClass F n (w * u) =
          b * a := by
            rw [map_mul]
            simp [u, w]
      _ = a * b := mul_comm b a
      _ = standardLubinTateUnitParameterClass F n z := by
        simp [z]
  have hdiv  :=
    (standardLubinTateUnitParameterClass_eq_iff_div_mem
      F n (w * u) z).mp hclass
  have hwuz  :=
    (standardLubinTatePrimitivePointIntegerAction_eq_iff_div_mem_higherPrincipalUnitGroup
      hπ n (w * u) z).2 hdiv
  change
    σ
      (standardLubinTatePrimitivePointIntegerAction hπ n w).val =
      (standardLubinTatePrimitivePointIntegerAction hπ n z).val
  calc
    σ
        (standardLubinTatePrimitivePointIntegerAction hπ n w).val =
        (r (standardLubinTatePrimitivePointIntegerAction hπ n w)).val := rfl
    _ =
        (standardLubinTatePrimitivePointIntegerAction hπ n (w * u)).val :=
      congrArg Subtype.val hrw
    _ =
        (standardLubinTatePrimitivePointIntegerAction hπ n z).val :=
      congrArg Subtype.val hwuz

/-- The identity parameter gives the identity level-field automorphism. -/
theorem standardLubinTateUnitParameterAlgEquiv_one
      :
    standardLubinTateUnitParameterAlgEquiv F hπ n 1 = 1 := by
  apply MulSemiringAction.toAlgHom_injective K
    (standardLubinTateLevelField hπ n)
  apply (standardLubinTateLevelPowerBasis hπ n).algHom_ext
  simp only [MulSemiringAction.toAlgHom_apply, one_smul,
    AlgEquiv.smul_def]
  rw [standardLubinTateUnitParameterAlgEquiv_apply_gen,
    standardLubinTateUnitParameterLevelRoot_one]

/-- Multiplication of finite parameters is composition of the associated
level-field automorphisms. -/
theorem standardLubinTateUnitParameterAlgEquiv_mul
      (a b : standardLubinTateUnitParameter F n) :
    standardLubinTateUnitParameterAlgEquiv F hπ n (a * b) =
      standardLubinTateUnitParameterAlgEquiv F hπ n a *
        standardLubinTateUnitParameterAlgEquiv F hπ n b := by
  apply MulSemiringAction.toAlgHom_injective K
    (standardLubinTateLevelField hπ n)
  apply (standardLubinTateLevelPowerBasis hπ n).algHom_ext
  simp only [MulSemiringAction.toAlgHom_apply, mul_smul,
    AlgEquiv.smul_def]
  rw [standardLubinTateUnitParameterAlgEquiv_apply_gen,
    standardLubinTateUnitParameterAlgEquiv_apply_gen,
    standardLubinTateUnitParameterAlgEquiv_apply_levelRoot]

/-- The explicit map from finite unit parameters to the finite-level Galois
group. -/
noncomputable def standardLubinTateUnitParameterToGal
      :
    standardLubinTateUnitParameter F n →
      Gal((standardLubinTateLevelField hπ n) / K) :=
  standardLubinTateUnitParameterAlgEquiv F hπ n

/-- Faithfulness of the primitive action makes the parameter-to-automorphism
map injective. -/
theorem standardLubinTateUnitParameterToGal_injective
      :
    Function.Injective
      (standardLubinTateUnitParameterToGal F hπ n) := by
  intro a b hab
  apply standardLubinTateUnitParameterLevelRoot_injective F hπ n
  have hgen := congrArg
    (fun σ : Gal((standardLubinTateLevelField hπ n) / K) =>
      σ (standardLubinTateLevelPowerBasis hπ n).gen) hab
  simpa [standardLubinTateUnitParameterToGal] using hgen

/-- The explicit parameter map preserves the identity element. -/
def standardLubinTateUnitParameterToGal_one
       := standardLubinTateUnitParameterAlgEquiv_one F hπ n

/-- The explicit parameter map preserves multiplication. -/
def standardLubinTateUnitParameterToGal_mul
      (a b : standardLubinTateUnitParameter F n)  := standardLubinTateUnitParameterAlgEquiv_mul F hπ n a b
end


/-- The automorphism group of a standard finite level is finite. -/
noncomputable instance standardLubinTateLevelField_galFinite
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    Finite (Gal((standardLubinTateLevelField hπ n) / K)) := by
  let  :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : Module.Free K (standardLubinTateLevelField hπ n) :=
    Module.Free.of_divisionRing _ _
  let : Finite
      ((standardLubinTateLevelField hπ n) →ₐ[K]
        (standardLubinTateLevelField hπ n)) :=
    Finite.algHom _ _ _
  exact Finite.algEquiv

section
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
include F π hπ n
/-- The number of base-field automorphisms of a standard level is at most
its field degree. -/
theorem standardLubinTateLevelField_natCard_gal_le_finrank
      :
    Nat.card (Gal((standardLubinTateLevelField hπ n) / K)) ≤
      Module.finrank K (standardLubinTateLevelField hπ n) := by
  let  :=
    standardLubinTateLevelField_finiteDimensional hπ n
  rw [Nat.card_eq_fintype_card]
  exact AlgEquiv.card_le

/-- The automorphism group of a standard finite level has cardinality equal
to the field degree. -/
theorem standardLubinTateLevelField_natCard_gal
      :
    Nat.card (Gal((standardLubinTateLevelField hπ n) / K)) =
      Module.finrank K (standardLubinTateLevelField hπ n) := by
  let  :=
    standardLubinTateLevelField_finiteDimensional hπ n
  apply Nat.le_antisymm
  · exact standardLubinTateLevelField_natCard_gal_le_finrank hπ n
  · calc
      Module.finrank K (standardLubinTateLevelField hπ n) =
          Nat.card (standardLubinTateUnitParameter F n) := by
        rw [standardLubinTateLevelField_finrank hπ n,
          standardLubinTateUnitParameter_natCard F n]
      _ ≤ Nat.card (Gal((standardLubinTateLevelField hπ n) / K)) :=
        Nat.card_le_card_of_injective
          (standardLubinTateUnitParameterToGal F hπ n)
          (standardLubinTateUnitParameterToGal_injective F hπ n)
end


section
variable (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ)
include F π hπ n
/-- The parameter-to-Galois map is bijective. -/
theorem standardLubinTateUnitParameterToGal_bijective
      :
    Function.Bijective
      (standardLubinTateUnitParameterToGal F hπ n) := by
  apply (Nat.bijective_iff_injective_and_card
    (standardLubinTateUnitParameterToGal F hπ n)).2
  refine
    ⟨standardLubinTateUnitParameterToGal_injective F hπ n, ?_⟩
  rw [standardLubinTateUnitParameter_natCard F n,
    ← standardLubinTateLevelField_finrank hπ n,
    ← standardLubinTateLevelField_natCard_gal hπ n]

/-- Every finite-level automorphism is obtained from a finite unit
parameter. -/
def standardLubinTateUnitParameterToGal_surjective
       :=
  (standardLubinTateUnitParameterToGal_bijective F hπ n).2
end


/-- Every standard finite Lubin--Tate level field is Galois over its base
field. -/
theorem standardLubinTateLevelField_isGalois
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    IsGalois K (standardLubinTateLevelField hπ n) := by
  let  :=
    standardLubinTateLevelField_finiteDimensional hπ n
  exact IsGalois.of_card_aut_eq_finrank K
    (standardLubinTateLevelField hπ n)
    (standardLubinTateLevelField_natCard_gal hπ n)

end LubinTate

end
