module

public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CompleteRangeRestriction
public import ValuedFieldTheory.Valuation.ValuedAdicComplete
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import Mathlib.Topology.Algebra.Valued.NormedValued

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Topology of range-restricted complete discretely valued fields

This file equips the multiplicative-range valuation with its valued and normed
field structures and transports adic completeness, compactness, properness,
and completeness.
-/

noncomputable section

universe u v

open Filter WithZero
open scoped NNReal Valued

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace CompleteDVF

variable {K : Type u} [Field K]

/-- The canonical `Valued` structure attached to the range-restricted complete
DVF valuation. -/
@[implicit_reducible]
def mrangeRestrictValued
    (F : CompleteDVF.{u, v} K) :
    Valued K (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
  Valued.mk' (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F)

@[instance_reducible]
 def mrangeRestrictValued_rankOne
    (F : CompleteDVF.{u, v} K) :
    (@Valued.v K _
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) _
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)).RankOne := by
  change
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).RankOne
  exact
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_rankOne F

/-- The rank-one normalized complete-DVF valuation supplies the normed-field
structure expected by mathlib's finite-dimensional closed-subspace theorem. -/
@[implicit_reducible]
def mrangeRestrict_nontriviallyNormedField
    (F : CompleteDVF.{u, v} K) :
    NontriviallyNormedField K :=
  Valued.toNontriviallyNormedField
    (L := K)
    (Γ₀ := MonoidHom.mrange F.valuation.toMonoidWithZeroHom)
    (val := LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    (hv := mrangeRestrictValued_rankOne F)

/-- For the topology induced by the range-restricted rank-one valuation, the
valuation ring has its maximal-ideal adic topology. -/
theorem mrangeRestrict_integer_isAdic
    (F : CompleteDVF.{u, v} K) :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    letI : NontriviallyNormedField K :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
    IsAdic (𝓂[K]) := by
  let Γ : Type v :=
    MonoidHom.mrange F.valuation.toMonoidWithZeroHom
  let : Valued K Γ :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  let : NontriviallyNormedField K :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
  have : IsCyclic Γˣ := by
    simpa [Γ] using
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_units_isCyclic F)
  let : MulArchimedean Γ :=
    WithZeroValuation.units_isCyclic_mulArchimedean Γ
  have : (Valued.v : _root_.Valuation K Γ).IsRankOneDiscrete := by
    change
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).IsRankOneDiscrete
    exact
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_isRankOneDiscrete F)
  exact ValuationTheory.Valuations.rankOneDiscreteValuationSubring_isAdic

/-- The valuation ring of a range-restricted complete DVF is complete for the
subspace topology coming from the corresponding normed-field topology. -/
theorem mrangeRestrict_integer_completeSpace
    (F : CompleteDVF.{u, v} K) :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    letI : NontriviallyNormedField K :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
    CompleteSpace 𝒪[K] := by
  let Γ : Type v :=
    MonoidHom.mrange F.valuation.toMonoidWithZeroHom
  let : Valued K Γ := (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  have : (Valued.v : _root_.Valuation K Γ).IsRankOneDiscrete := by
    change
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).IsRankOneDiscrete
    exact
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_isRankOneDiscrete F)
  have : (Valued.v : _root_.Valuation K Γ).RankOne := by
    change
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).RankOne
    exact
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_rankOne F)
  let : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField
      (L := K)
      (Γ₀ := MonoidHom.mrange
        F.valuation.toMonoidWithZeroHom)
  have : IsUltrametricDist K := by infer_instance
  have : IsDiscreteValuationRing 𝒪[K] := by
    change IsDiscreteValuationRing (Valued.v : _root_.Valuation K Γ).valuationSubring
    infer_instance
  have hadic : IsAdic (𝓂[K]) :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_integer_isAdic F)
  have hcomplete : IsAdicComplete (𝓂[K]) 𝒪[K] := by
    change
      IsAdicComplete
        (IsLocalRing.maximalIdeal (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring)
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring
    exact (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_isAdicComplete F)
  exact (hadic.isAdicComplete_iff.mp hcomplete).1

/-- The valuation ring of a range-restricted complete DVF with finite residue
field is compact.  This is the compactness input in the local-field structure theory,
the local compactness criterion. -/
theorem mrangeRestrict_integer_compactSpace_of_residueField_finite
    (F : CompleteDVF.{u, v} K) [Finite F.residueField] :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    letI : NontriviallyNormedField K :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
    CompactSpace 𝒪[K] := by
  let : Valued K
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  have :
      (Valued.v :
        _root_.Valuation K
          (MonoidHom.mrange
            F.valuation.toMonoidWithZeroHom)).IsRankOneDiscrete :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_isRankOneDiscrete F)
  have :
      (Valued.v :
        _root_.Valuation K
          (MonoidHom.mrange
            F.valuation.toMonoidWithZeroHom)).RankOne :=
    mrangeRestrictValued_rankOne F
  let : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField
      (L := K)
      (Γ₀ := MonoidHom.mrange
        F.valuation.toMonoidWithZeroHom)
  have : IsUltrametricDist K := by infer_instance
  have : IsDiscreteValuationRing 𝒪[K] := by
    change
      IsDiscreteValuationRing
        (Valued.v :
          _root_.Valuation K
            (MonoidHom.mrange
              F.valuation.toMonoidWithZeroHom)).valuationSubring
    infer_instance
  have : Finite 𝓀[K] := by
    change
      Finite
        (IsLocalRing.ResidueField (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring)
    exact (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_residueField_finite F)
  have hcomplete : CompleteSpace 𝒪[K] :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_integer_completeSpace F)
  exact
    (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
      (K := K)
      (Γ₀ := MonoidHom.mrange F.valuation.toMonoidWithZeroHom)).2
      ⟨hcomplete, inferInstance, inferInstance⟩

/-- A range-restricted complete DVF with finite residue field is proper for
the associated normed-field topology. -/
theorem mrangeRestrict_properSpace_of_residueField_finite
    (F : CompleteDVF.{u, v} K) [Finite F.residueField] :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    letI : NontriviallyNormedField K :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
    ProperSpace K := by
  let : Valued K
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  have :
      (Valued.v :
        _root_.Valuation K
          (MonoidHom.mrange
            F.valuation.toMonoidWithZeroHom)).RankOne :=
    mrangeRestrictValued_rankOne F
  let : NontriviallyNormedField K :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
  have hcompact : CompactSpace 𝒪[K] :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_integer_compactSpace_of_residueField_finite F)
  unfold mrangeRestrict_nontriviallyNormedField
  unfold Valued.toNontriviallyNormedField
  change @ProperSpace K
    (Valued.toNormedField K
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom)
      (val := LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
      (hv := mrangeRestrictValued_rankOne F)).toPseudoMetricSpace
  exact
    (@Valued.integer.properSpace_iff_compactSpace_integer
      K
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom)
      inferInstance inferInstance
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
      (mrangeRestrictValued_rankOne F)).2 hcompact

/-- A range-restricted complete DVF with finite residue field is complete for
the associated normed-field topology. -/
theorem mrangeRestrict_completeSpace_of_residueField_finite
    (F : CompleteDVF.{u, v} K) [Finite F.residueField] :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    letI : NontriviallyNormedField K :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
    CompleteSpace K := by
  let Γ : Type v :=
    MonoidHom.mrange F.valuation.toMonoidWithZeroHom
  let : Valued K Γ := (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  let : NontriviallyNormedField K :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
  have : ProperSpace K :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_properSpace_of_residueField_finite F)
  exact complete_of_proper
