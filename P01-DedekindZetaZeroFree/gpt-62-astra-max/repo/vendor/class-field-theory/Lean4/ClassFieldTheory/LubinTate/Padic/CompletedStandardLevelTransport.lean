module

public import ClassFieldTheory.LubinTate.Padic.CompletedFrobeniusLift
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Transporting a finite p-adic Lubin--Tate level to the completed level

The ordinary standard Lubin--Tate level embeds in the completed level by
sending its primitive generator to the chosen completed primitive point.
This file proves that the embedding also preserves the integral analytic
action.  In particular, the direct completed action of a p-adic unit is
the image of the finite action with the *same* unit-parameter class.

This fixes the parameter orientation before the completed Frobenius is
used in the changed-uniformizer norm argument.
-/

noncomputable section

open scoped PowerSeries

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField
open SameUniformizer

 noncomputable local instance
    padicStandardLevelTransportCoefficientUniformSpace
    (p : ℕ) [Fact p.Prime] :
    UniformSpace (padicLocalField p).valuationSubring :=
  ⊥

 noncomputable local instance
    padicStandardLevelTransportCoefficientTopologicalSpace
    (p : ℕ) [Fact p.Prime] :
    TopologicalSpace (padicLocalField p).valuationSubring :=
  ⊥

 noncomputable local instance (priority := 50)
    padicStandardLevelTransportWittUniformSpace
    (p : ℕ) [Fact p.Prime] :
    UniformSpace (padicCompletedUnramifiedWittRing p) :=
  ⊥

 noncomputable local instance
    padicStandardLevelTransportSourceWithIdeal
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    WithIdeal
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
      ).valuationSubring where
  i :=
    (standardLubinTateLevelCompleteDVF
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n
    ).maximalIdeal

 noncomputable local instance
    padicStandardLevelTransportTargetWithIdeal
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    WithIdeal
      (padicCompletedLevelCompleteDVF p n).valuationSubring where
  i := (padicCompletedLevelCompleteDVF p n).maximalIdeal

 noncomputable local instance
    padicStandardLevelTransportSourceCompleteSpace
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    CompleteSpace
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
      ).valuationSubring := by
  let source :=
    standardLubinTateLevelCompleteDVF
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n
  have hadic : IsAdic source.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp source.isAdicComplete).1

 noncomputable local instance
    padicStandardLevelTransportSourceT2Space
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    T2Space
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
      ).valuationSubring := by
  let source :=
    standardLubinTateLevelCompleteDVF
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n
  have hadic : IsAdic source.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp source.isAdicComplete).2

 noncomputable local instance
    padicStandardLevelTransportTargetCompleteSpace
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    CompleteSpace
      (padicCompletedLevelCompleteDVF p n).valuationSubring := by
  let target := padicCompletedLevelCompleteDVF p n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).1

 noncomputable local instance
    padicStandardLevelTransportTargetT2Space
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    T2Space
      (padicCompletedLevelCompleteDVF p n).valuationSubring := by
  let target := padicCompletedLevelCompleteDVF p n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).2

section

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- The standard finite-level embedding restricted to the actual valuation
rings. -/
noncomputable def padicStandardLevelIntegerEmbedding :
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    (standardLubinTateLevelCompleteDVF hπ n).valuationSubring →+*
      (padicCompletedLevelCompleteDVF p n).valuationSubring := by
  let F := padicLocalField p
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let L := standardLubinTateLevelField hπ n
  let source := standardLubinTateLevelCompleteDVF hπ n
  let A := padicCompletedUnramifiedCompleteDVF p
  let E := padicCompletedLevelField p n
  let target := padicCompletedLevelCompleteDVF p n
  let ι := padicStandardLevelEmbedding p n
  letI : F.valuation.HasExtension source.valuation :=
    standardLubinTateLevelCompleteDVF_hasExtension

       hπ n
  letI : Algebra F.valuationSubring source.valuationSubring :=
    Valuation.HasExtension.instAlgebra_valuationSubring
      (padicLocalField p).valuation
      (standardLubinTateLevelCompleteDVF

         hπ n).valuation
  letI : IsScalarTower F.valuationSubring source.valuationSubring L :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsIntegralClosure
      source.valuationSubring F.valuationSubring L :=
    standardLubinTateLevelCompleteDVF_isIntegralClosure hπ n
  letI : IsScalarTower A.valuationSubring target.valuationSubring E :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsIntegralClosure
      target.valuationSubring A.valuationSubring E :=
    padicCompletedLevelCompleteDVF_isIntegralClosure p n
  apply RingHom.codRestrict (ι.toRingHom.comp source.valuation.valuationSubring.subtype) target.valuation.valuationSubring
  intro x
  have hxIntegral :
      IsIntegral F.valuationSubring (x.val : L) :=
    (IsIntegralClosure.isIntegral_iff
      (A := source.valuationSubring)
      (R := F.valuationSubring)
      (B := L)).2 ⟨x, rfl⟩
  have hcomp :
      (algebraMap A.valuationSubring E).comp
          (padicCompletedUnramifiedIntegerMap p) =
        ι.toRingHom.comp (algebraMap F.valuationSubring L) := by
    ext a
    simp only [RingHom.comp_apply]
    change
      algebraMap (padicCompletedUnramifiedField p) E
          ((padicCompletedUnramifiedIntegerMap p a :
            A.valuationSubring) :
              padicCompletedUnramifiedField p) =
        ι (algebraMap ℚ_[p] L (a : ℚ_[p]))
    rw [padicCompletedUnramifiedIntegerMap_coe]
    calc
      algebraMap (padicCompletedUnramifiedField p) E
          (algebraMap ℚ_[p]
            (padicCompletedUnramifiedField p) (a : ℚ_[p])) =
          algebraMap ℚ_[p] E (a : ℚ_[p]) :=
        (IsScalarTower.algebraMap_apply ℚ_[p]
          (padicCompletedUnramifiedField p) E (a : ℚ_[p])).symm
      _ = ι (algebraMap ℚ_[p] L (a : ℚ_[p])) :=
        (ι.commutes (a : ℚ_[p])).symm
  have hxMappedIntegral :
      IsIntegral A.valuationSubring (ι (x.val : L)) :=
    IsIntegral.map_of_comp_eq
      (padicCompletedUnramifiedIntegerMap p)
      ι.toRingHom hcomp hxIntegral
  rcases
      (IsIntegralClosure.isIntegral_iff
        (A := target.valuationSubring)
        (R := A.valuationSubring)
        (B := E)).1 hxMappedIntegral with
    ⟨z, hz⟩
  change target.valuation (ι (x.val : L)) ≤ 1
  rw [← hz]
  exact z.property

/-- Coercing the integral standard-level embedding to the completed field
recovers the field embedding. -/
@[simp]
theorem padicStandardLevelIntegerEmbedding_coe
    (x :
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
      ).valuationSubring) :
    ((padicStandardLevelIntegerEmbedding p n x :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
      padicCompletedLevelField p n) =
        padicStandardLevelEmbedding p n
          (x.val :
            standardLubinTateLevelField
              (padicMultiplicativeLubinTateSeries_isUniformizer p) n) := rfl

/-- The integral embedding sends the finite primitive point to the chosen
completed primitive point. -/
@[simp]
theorem padicStandardLevelIntegerEmbedding_apply_primitivePoint :
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    padicStandardLevelIntegerEmbedding p n
        (standardLubinTatePrimitivePointInteger hπ n) =
      padicCompletedPrimitiveRootInteger p n := by
  apply Subtype.ext
  rw [padicStandardLevelIntegerEmbedding_coe,
    padicCompletedPrimitiveRootInteger_coe]
  exact (congrArg (padicStandardLevelEmbedding p n)
    (standardLubinTatePrimitivePointInteger_coe
       (padicMultiplicativeLubinTateSeries_isUniformizer p) n)).trans (padicStandardLevelEmbedding_apply_gen p n)

/-- The integral standard-level embedding is continuous for the two
maximal-ideal adic topologies. -/
theorem padicStandardLevelIntegerEmbedding_continuous :
    Continuous (padicStandardLevelIntegerEmbedding p n) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let source := standardLubinTateLevelCompleteDVF hπ n
  let target := padicCompletedLevelCompleteDVF p n
  let f :=
    padicStandardLevelIntegerEmbedding p n
  have hmap :
      Ideal.map f source.maximalIdeal ≤ target.maximalIdeal := by
    rw [source.maximalIdeal_eq_span_uniformizer
      (standardLubinTatePrimitivePoint_isUniformizer hπ n),
      Ideal.map_span, Set.image_singleton, Ideal.span_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    change
      padicStandardLevelIntegerEmbedding p n
          (standardLubinTatePrimitivePointInteger hπ n) ∈
        target.maximalIdeal
    rw [padicStandardLevelIntegerEmbedding_apply_primitivePoint]
    exact padicCompletedPrimitiveRootInteger_mem_maximalIdeal p n
  exact
    (WithIdeal.uniformContinuous_of_map_le hmap).continuous

/-- The integral embedding commutes with the canonical maps of p-adic
integer coefficients. -/
theorem padicStandardLevelIntegerEmbedding_comp_coefficientHom :
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    (padicStandardLevelIntegerEmbedding p n).comp
        (standardLubinTateLevelCoefficientHom hπ n) =
      padicCompletedLevelPadicIntegerCoefficientHom p n := by
  let E := padicCompletedLevelField p n
  ext a
  simp only [RingHom.comp_apply,
    padicStandardLevelIntegerEmbedding_coe,
    padicCompletedLevelPadicIntegerCoefficientHom_coe]
  change
    padicStandardLevelEmbedding p n
        (algebraMap ℚ_[p] (standardLubinTateLevelField (padicMultiplicativeLubinTateSeries_isUniformizer p) n) a) =
      algebraMap (padicCompletedUnramifiedField p) E
        (algebraMap ℚ_[p]
          (padicCompletedUnramifiedField p) a)
  rw [(padicStandardLevelEmbedding p n).commutes,
    ← IsScalarTower.algebraMap_apply ℚ_[p]
      (padicCompletedUnramifiedField p) E]

/-- Evaluation after extending p-adic coefficients to the completed Witt
ring is evaluation through the direct p-adic coefficient map. -/
theorem padicCompletedLevelPowerSeriesEval_map_padicCoefficients
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (f : PowerSeries (padicLocalField p).valuationSubring) :
    padicCompletedLevelPowerSeriesEval p n x hx
        (PowerSeries.map
          (padicValuationSubringToCompletedUnramifiedWittRing p) f) =
      PowerSeries.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n) x f := by
  rw [padicCompletedLevelPowerSeriesEval,
    PowerSeries.coe_eval₂Hom,
    PowerSeries.eval₂_eq_tsum
      (padicCompletedLevelWittCoefficientHom_continuous p n) hx,
    PowerSeries.eval₂_eq_tsum continuous_of_discreteTopology hx]
  apply tsum_congr
  intro d
  rw [PowerSeries.coeff_map]
  rfl

end

/-- Analytic evaluation in the finite standard level commutes with its
integral embedding into the completed level. -/
theorem padicStandardLevelIntegerEmbedding_powerSeriesEval
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x :
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
      ).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (f : PowerSeries (padicLocalField p).valuationSubring) :
    padicStandardLevelIntegerEmbedding p n
        (standardLubinTateLevelPowerSeriesEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p)
          n x hx f) =
      padicCompletedLevelPowerSeriesEval p n
        (padicStandardLevelIntegerEmbedding p n x)
        (hx.map (padicStandardLevelIntegerEmbedding_continuous p n))
        (PowerSeries.map
          (padicValuationSubringToCompletedUnramifiedWittRing p) f) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let j := padicStandardLevelIntegerEmbedding p n
  have hraw :=
    congrFun
      (PowerSeries.comp_eval₂
        (φ := standardLubinTateLevelCoefficientHom hπ n)
        continuous_of_discreteTopology hx
        (padicStandardLevelIntegerEmbedding_continuous p n)) f
  have htransport :
      j
          (PowerSeries.eval₂
            (standardLubinTateLevelCoefficientHom hπ n) x f) =
        PowerSeries.eval₂
          (padicCompletedLevelPadicIntegerCoefficientHom p n)
          (j x) f := by
    rw [← padicStandardLevelIntegerEmbedding_comp_coefficientHom p n]
    simpa using hraw
  calc
    _ =
        PowerSeries.eval₂
          (padicCompletedLevelPadicIntegerCoefficientHom p n)
          (j x) f := by
      simpa only [standardLubinTateLevelPowerSeriesEval,
        PowerSeries.coe_eval₂Hom] using htransport
    _ =
        padicCompletedLevelPowerSeriesEval p n (j x)
          (hx.map (padicStandardLevelIntegerEmbedding_continuous p n))
          (PowerSeries.map
            (padicValuationSubringToCompletedUnramifiedWittRing p) f) :=
      (padicCompletedLevelPowerSeriesEval_map_padicCoefficients
        p n (j x)
        (hx.map (padicStandardLevelIntegerEmbedding_continuous p n))
        f).symm

variable (p : ℕ) [Fact p.Prime] (n : ℕ) (u : (padicLocalField p).valuationSubringˣ)

/-- The integral embedding carries the finite analytic unit action to the
direct completed analytic unit action with the same unit. -/
@[simp]
theorem
    padicStandardLevelIntegerEmbedding_apply_primitivePointUnitAction :
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    padicStandardLevelIntegerEmbedding p n
        (standardLubinTatePrimitivePointIntegerAction hπ n u) =
      padicCompletedStandardPrimitivePointUnitAction p n u := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  have h :=
    padicStandardLevelIntegerEmbedding_powerSeriesEval p n
      (standardLubinTatePrimitivePointInteger hπ n)
      (standardLubinTatePrimitivePointInteger_hasEval hπ n)
      (standardLubinTateEndomorphism hπ
        u)
  simpa only [
    standardLubinTatePrimitivePointIntegerAction,
    standardLubinTateEndomorphismValue,
    standardLubinTateEndomorphismEvalAt,
    padicCompletedStandardPrimitivePointUnitAction,
    padicCompletedStandardScalarEndomorphismValue,
    padicCompletedStandardScalarEndomorphism,
    padicStandardLevelIntegerEmbedding_apply_primitivePoint] using h

/-- At the finite p-adic level, the parameter class of a unit realizes
exactly its direct analytic action. -/
theorem padicStandardUnitParameterLevelRoot_class :
    let F := padicLocalField p
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    standardLubinTateUnitParameterLevelRoot F hπ n
        (standardLubinTateUnitParameterClass F n u) =
      standardLubinTatePrimitiveLevelAction hπ n u := by
  let F := padicLocalField p
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  apply Subtype.ext
  exact (standardLubinTateUnitParameterLevelRoot_coe F hπ n
    (standardLubinTateUnitParameterClass F n u)).trans
      ((standardLubinTateUnitParameterRoot_class F hπ n u).trans
        (standardLubinTatePrimitiveLevelAction_coe
           hπ n u).symm)

/-- The direct completed unit action is the completed realization of the
same finite unit-parameter class. -/
@[simp]
theorem
    padicCompletedStandardPrimitivePointUnitAction_eq_unitParameterRoot :
    ((padicCompletedStandardPrimitivePointUnitAction p n u :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
      padicCompletedLevelField p n) =
        padicCompletedUnitParameterRoot p n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  calc
    _ =
        ((padicStandardLevelIntegerEmbedding p n
            (standardLubinTatePrimitivePointIntegerAction hπ n u) :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
            padicCompletedLevelField p n) := by
      simp
    _ =
        padicStandardLevelEmbedding p n
          ((standardLubinTatePrimitivePointIntegerAction hπ n u :
            (standardLubinTateLevelCompleteDVF hπ n).valuationSubring).val :
              standardLubinTateLevelField hπ n) := by
      rfl
    _ =
        padicStandardLevelEmbedding p n
          (standardLubinTateUnitParameterLevelRoot
            (padicLocalField p) hπ n
            (standardLubinTateUnitParameterClass
              (padicLocalField p) n u)) := by
      congr 1
      change
        standardLubinTatePrimitiveLevelAction hπ n u =
          standardLubinTateUnitParameterLevelRoot
            (padicLocalField p) hπ n
            (standardLubinTateUnitParameterClass
              (padicLocalField p) n u)
      exact (padicStandardUnitParameterLevelRoot_class p n u).symm
    _ =
        padicCompletedUnitParameterRoot p n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u) :=
      rfl

/-- The completed unit-indexed Frobenius lift restricts to the finite
standard-level automorphism with the same unit-parameter class. -/
theorem padicCompletedUnitFrobeniusLiftEquiv_standardLevelEmbedding
    (x :
      standardLubinTateLevelField
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n) :
    padicCompletedUnitFrobeniusLiftEquiv p n u
        (padicStandardLevelEmbedding p n x) =
      padicStandardLevelEmbedding p n
        (standardLubinTateUnitParameterAlgEquiv
          (padicLocalField p)
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u) x) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let L := standardLubinTateLevelField hπ n
  let E := padicCompletedLevelField p n
  let ι := padicStandardLevelEmbedding p n
  let δ : E →ₐ[ℚ_[p]] E :=
    { toRingHom :=
        (padicCompletedUnitFrobeniusLiftEquiv p n u).toRingHom
      commutes' := by
        intro b
        change
          padicCompletedUnitFrobeniusLiftEquiv p n u
              (algebraMap (padicCompletedUnramifiedField p) E
                (algebraMap ℚ_[p]
                  (padicCompletedUnramifiedField p) b)) =
            algebraMap (padicCompletedUnramifiedField p) E
              (algebraMap ℚ_[p]
                (padicCompletedUnramifiedField p) b)
        rw [padicCompletedUnitFrobeniusLiftEquiv_algebraMap,
          (padicCompletedUnramifiedFrobenius p).commutes] }
  let σ :=
    standardLubinTateUnitParameterAlgEquiv
      (padicLocalField p) hπ n
      (standardLubinTateUnitParameterClass
        (padicLocalField p) n u)
  have hintertwine : δ.comp ι = ι.comp σ.toAlgHom := by
    apply (standardLubinTateLevelPowerBasis hπ n).algHom_ext
    change
      padicCompletedUnitFrobeniusLiftEquiv p n u
          (padicStandardLevelEmbedding p n
            (standardLubinTateLevelPowerBasis hπ n).gen) =
        padicStandardLevelEmbedding p n
          (σ
            (standardLubinTateLevelPowerBasis hπ n).gen)
    rw [padicStandardLevelEmbedding_apply_gen,
      padicCompletedUnitFrobeniusLiftEquiv_primitiveRoot]
    have hgen := congrArg (padicStandardLevelEmbedding p n)
      (standardLubinTateUnitParameterAlgEquiv_apply_gen
        (padicLocalField p) hπ n
        (standardLubinTateUnitParameterClass (padicLocalField p) n u))
    exact (padicCompletedStandardPrimitivePointUnitAction_eq_unitParameterRoot
      p n u).trans hgen.symm
  exact DFunLike.congr_fun hintertwine x

/-- The inverse completed unit-indexed Frobenius lift restricts to the
inverse finite unit-parameter automorphism. -/
theorem padicCompletedUnitFrobeniusLiftEquiv_symm_standardLevelEmbedding
    (x :
      standardLubinTateLevelField
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n) :
    (padicCompletedUnitFrobeniusLiftEquiv p n u).symm
        (padicStandardLevelEmbedding p n x) =
      padicStandardLevelEmbedding p n
        ((standardLubinTateUnitParameterAlgEquiv
          (padicLocalField p)
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u)).symm x) := by
  apply (padicCompletedUnitFrobeniusLiftEquiv p n u).injective
  rw [
    (padicCompletedUnitFrobeniusLiftEquiv p n u).apply_symm_apply,
    padicCompletedUnitFrobeniusLiftEquiv_standardLevelEmbedding,
    (standardLubinTateUnitParameterAlgEquiv
      (padicLocalField p)
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n
      (standardLubinTateUnitParameterClass
        (padicLocalField p) n u)).apply_symm_apply]

/-- With the inverse unit as Frobenius-lift parameter, the inverse completed
lift acts on the standard finite level by the direct unit parameter.  This is
the orientation used by the actual local Artin map after changed-uniformizer
descent. -/
theorem
    padicCompletedInverseUnitFrobeniusLiftEquiv_standardLevelEmbedding
    (x :
      standardLubinTateLevelField
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n) :
    (padicCompletedUnitFrobeniusLiftEquiv p n u⁻¹).symm
        (padicStandardLevelEmbedding p n x) =
      padicStandardLevelEmbedding p n
        (standardLubinTateUnitParameterAlgEquiv
          (padicLocalField p)
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u) x) := by
  rw [
    padicCompletedUnitFrobeniusLiftEquiv_symm_standardLevelEmbedding]
  let standardLubinTateUnitParameterClass₀ := standardLubinTateUnitParameterClass (padicLocalField p) n
  have hparameter :
      standardLubinTateUnitParameterAlgEquiv
          (padicLocalField p)
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n
          (standardLubinTateUnitParameterClass₀ u⁻¹) =
        (standardLubinTateUnitParameterAlgEquiv
          (padicLocalField p)
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n
          (standardLubinTateUnitParameterClass₀ u))⁻¹ := by
    let standardLubinTateUnitParameterEquivGal₀ := standardLubinTateUnitParameterEquivGal (padicLocalField p) (padicMultiplicativeLubinTateSeries_isUniformizer p) n
    change
      standardLubinTateUnitParameterEquivGal₀
          (standardLubinTateUnitParameterClass₀ u⁻¹) =
        (standardLubinTateUnitParameterEquivGal₀
          (standardLubinTateUnitParameterClass₀ u))⁻¹
    rw [((standardLubinTateUnitParameterClass₀).map_inv u),
      (standardLubinTateUnitParameterEquivGal₀).map_inv]
  rw [hparameter]
  rfl

end LubinTate

end
