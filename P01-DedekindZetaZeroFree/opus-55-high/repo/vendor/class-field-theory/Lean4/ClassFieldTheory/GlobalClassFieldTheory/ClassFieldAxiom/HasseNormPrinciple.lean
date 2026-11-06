module

public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdelePowerLocalUnitNormContainment
public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.CyclicIdeleClassNormIndex
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Norm
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.EquivariantEquiv
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.Herbrand
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.BaseChange
public import Mathlib.RingTheory.Norm.Transitivity
public import GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Cardinality
public import GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.TateComparison
public import GaloisCohomology.Cyclic.TateH0.Main
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.CohomologyBridge

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# The Hasse norm principle: the concrete local-global map

This file proves the Hasse norm principle on the actual idele and field norm
maps.  The local condition is expressed canonically:
at a place `v` it is the image of the determinant norm on
`K_v ⊗[K] L`.  At finite places this is the chosen completion norm
subgroup by
`_root_.finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup`.

The resulting homomorphism

`Kˣ / N(Lˣ) ⟶ I_K / I_K,loc-norm`

is the concrete diagonal local-norm map.  Its injectivity is exactly the
Hasse norm principle.  The global-to-local inclusion and this equivalence
are independent of the global class-field axiom; the reverse inclusion
follows from degree-minus-one Tate-cohomology vanishing.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

open CategoryTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand

/-- Ideles whose component at every infinite place lies in the image of
the determinant norm on the corresponding archimedean local tensor
algebra. -/
def allInfinitePlaceLocalNormCondition
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
  [FiniteDimensional K L] :
    Subgroup (IdeleGroup K) :=
  ⨅ v : InfinitePlace K,
    (Units.map
      (Algebra.norm v.Completion :
        (v.Completion ⊗[K] L) →* v.Completion)).range.comap
      (IdeleGroup.infiniteComponent v)

/-- The simultaneous determinant-norm condition at every finite and
infinite place. -/
def allPlaceLocalNormCondition
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Subgroup (IdeleGroup K) :=
  allFinitePlaceLocalNormCondition (K := K) (L := L) ⊓
    allInfinitePlaceLocalNormCondition (K := K) (L := L)

/-- Every global relative-idele norm is a local determinant norm at every
place. -/
theorem relativeIdeleNorm_range_le_allPlaceLocalNormCondition
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    (RelativeIdeleGroup.norm K L).range ≤
      allPlaceLocalNormCondition (K := K) (L := L) := by
  intro a ha
  refine ⟨relativeIdeleNorm_range_le_allFinitePlaceLocalNormCondition
      (K := K) (L := L) ha, ?_⟩
  rcases ha with ⟨b, rfl⟩
  rw [allInfinitePlaceLocalNormCondition]
  apply Subgroup.mem_iInf.mpr
  intro v
  exact
    ⟨RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) v b,
      (RelativeIdeleGroup.infiniteComponent_norm
        (K := K) (L := L) v b).symm⟩

/-- An idele is a relative-idele norm exactly when every one of its
finite and infinite components is a determinant norm.  The nontrivial
reverse inclusion uses the restricted-product preimage construction:
integral local preimages are chosen at almost every finite place. -/
theorem relativeIdeleNorm_range_eq_allPlaceLocalNormCondition
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    (RelativeIdeleGroup.norm K L).range =
      allPlaceLocalNormCondition (K := K) (L := L) := by
  apply le_antisymm
  · exact
      relativeIdeleNorm_range_le_allPlaceLocalNormCondition
        (K := K) (L := L)
  · intro a ha
    apply
      (_root_.mem_relativeIdeleNorm_range_iff_localTensorNorms
        (K := K) (L := L) a).2
    constructor
    · intro v
      have hv :
          IdeleGroup.infiniteComponent v a ∈
            (Units.map
              (Algebra.norm v.Completion :
                (v.Completion ⊗[K] L) →* v.Completion)).range := by
        exact
          Subgroup.mem_iInf.mp
            (show
              a ∈ allInfinitePlaceLocalNormCondition
                (K := K) (L := L) from ha.2) v
      simpa [_root_.infiniteTensorNormSubgroup,
        _root_.infiniteTensorDetNorm] using hv
    · intro v
      have hv :
          IdeleGroup.finiteComponent v a ∈
            _root_.chosenFinitePlaceLocalNormSubgroup
              (K := K) (L := L) v := by
        exact
          Subgroup.mem_iInf.mp
            (show
              a ∈ allFinitePlaceLocalNormCondition
                (K := K) (L := L) from ha.1) v
      rw [
        _root_.finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup]
      exact hv

section IdeleClassConnecting

attribute [local instance]
  RelativeIdeleGroup.Cohomology.relativeIdeleMulDistribMulAction
  RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction
  RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction
