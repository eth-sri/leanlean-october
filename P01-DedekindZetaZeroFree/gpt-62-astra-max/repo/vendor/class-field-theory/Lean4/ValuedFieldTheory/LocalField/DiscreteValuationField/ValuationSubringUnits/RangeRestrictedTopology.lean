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

set_option autoImplicit false

/-!
# Topology of range-restricted complete discretely valued fields

This file equips the multiplicative-range valuation with its valued and normed
field structures and transports adic completeness, compactness, properness,
and completeness.
-/

noncomputable section

universe u v

open Filter WithZero
open scoped NNReal Valued Filter WithZero

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace CompleteDVF

variable {K : Type u} [Field K]

section

variable (F : CompleteDVF.{u, v} K)

/-- The canonical `Valued` structure attached to the range-restricted complete
DVF valuation. -/
@[implicit_reducible]
noncomputable def mrangeRestrictValued :
    Valued K (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
  Valued.mk' (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F)

@[instance_reducible]
 noncomputable def mrangeRestrictValued_rankOne :
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
noncomputable def mrangeRestrict_nontriviallyNormedField :
    NontriviallyNormedField K :=
  Valued.toNontriviallyNormedField
    (L := K)
    (Γ₀ := MonoidHom.mrange F.valuation.toMonoidWithZeroHom)
    (val := LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    (hv := mrangeRestrictValued_rankOne F)

/-- For the topology induced by the range-restricted rank-one valuation, the
valuation ring has its maximal-ideal adic topology. -/
theorem mrangeRestrict_integer_isAdic :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    letI : NontriviallyNormedField K :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
    IsAdic (𝓂[K]) := by
  let Γ :=
    MonoidHom.mrange F.valuation.toMonoidWithZeroHom
  let :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  let :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
  have : IsCyclic Γˣ := by
    simpa [Γ] using
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_units_isCyclic F)
  solve_by_elim [_root_.Valuation, LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict, LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_isRankOneDiscrete, WithZeroValuation.units_isCyclic_mulArchimedean, ValuationTheory.Valuations.rankOneDiscreteValuationSubring_isAdic]

/-- The valuation ring of a range-restricted complete DVF is complete for the
subspace topology coming from the corresponding normed-field topology. -/
theorem mrangeRestrict_integer_completeSpace :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    letI : NontriviallyNormedField K :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
    CompleteSpace 𝒪[K] := by
  let Γ :=
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
  refine (((LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_integer_isAdic F)).isAdicComplete_iff.mp ?_).1
  change
    IsAdicComplete
      (IsLocalRing.maximalIdeal (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring)
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring
  exact (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_isAdicComplete F)

end

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
  let :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  have :
      Valued.v.IsRankOneDiscrete :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_isRankOneDiscrete F)
  have :
      Valued.v.RankOne :=
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
  exact Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr ⟨mrangeRestrict_integer_completeSpace F, ⟨inferInstance, inferInstance⟩⟩

variable (F : CompleteDVF.{u, v} K) [Finite F.residueField]

/-- A range-restricted complete DVF with finite residue field is proper for
the associated normed-field topology. -/
theorem mrangeRestrict_properSpace_of_residueField_finite :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    letI : NontriviallyNormedField K :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
    ProperSpace K := by
  exact
    (@Valued.integer.properSpace_iff_compactSpace_integer
      K
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom)
      inferInstance inferInstance
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
      (mrangeRestrictValued_rankOne F)).2 ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_integer_compactSpace_of_residueField_finite F))

/-- A range-restricted complete DVF with finite residue field is complete for
the associated normed-field topology. -/
theorem mrangeRestrict_completeSpace_of_residueField_finite :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    letI : NontriviallyNormedField K :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
    CompleteSpace K := by
  let := (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  let :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
  solve_by_elim [LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_properSpace_of_residueField_finite, complete_of_proper]

end CompleteDVF
end LocalFieldTheory.DiscreteValuationField

end
