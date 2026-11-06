module

public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdelePowerLocalUnitNormContainment
public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.CyclicIdeleClassNormIndex
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Norm
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Principal
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.NormProperties
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











set_option autoImplicit false

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

/-- The actual global field-norm subgroup `N_{L/K}(Lˣ)` of `Kˣ`. -/
def globalFieldNormSubgroup
    (K L : Type)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    Subgroup Kˣ :=
  (Units.map
    (Algebra.norm K : L →* K)).range

/-- Base-field units that are determinant norms at every completion. -/
def everywhereLocalFieldNormSubgroup
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Subgroup Kˣ :=
  (allPlaceLocalNormCondition (K := K) (L := L)).comap
    (IdeleGroup.principalIdele K)

/-- A global field norm is a local norm at every place.  This is the
unconditional direction of the Hasse norm principle. -/
theorem globalFieldNormSubgroup_le_everywhereLocalFieldNormSubgroup
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    globalFieldNormSubgroup K L ≤
      everywhereLocalFieldNormSubgroup K L := by
  rintro x ⟨y, rfl⟩
  show
    IdeleGroup.principalIdele K
        (Units.map
          (Algebra.norm K : L →* K) y) ∈
      allPlaceLocalNormCondition (K := K) (L := L)
  rw [← RelativeIdeleGroup.norm_principalIdele K L y]
  exact
    relativeIdeleNorm_range_le_allPlaceLocalNormCondition
      (K := K) (L := L) ⟨_, rfl⟩





section IdeleClassConnecting

attribute [local instance]
  RelativeIdeleGroup.Cohomology.relativeIdeleMulDistribMulAction
  RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction
  RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction





end IdeleClassConnecting

















/-- The concrete diagonal local-norm map.  Its source is the global norm
quotient, while its target kills precisely those ideles satisfying every
local norm condition. -/
noncomputable def hasseNormDiagonal
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Kˣ ⧸ globalFieldNormSubgroup K L →*
      IdeleGroup K ⧸ allPlaceLocalNormCondition (K := K) (L := L) :=
  QuotientGroup.map
    (globalFieldNormSubgroup K L)
    (allPlaceLocalNormCondition (K := K) (L := L))
    (IdeleGroup.principalIdele K)
    globalFieldNormSubgroup_le_everywhereLocalFieldNormSubgroup

/-- The Hasse norm diagonal sends the class of a field unit to the class
of its principal idele. -/
@[simp]
theorem hasseNormDiagonal_mk
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (x : Kˣ) :
    hasseNormDiagonal K L
        (QuotientGroup.mk' (globalFieldNormSubgroup K L) x) =
      QuotientGroup.mk'
        (allPlaceLocalNormCondition (K := K) (L := L))
        (IdeleGroup.principalIdele K x) :=
  rfl













end GlobalClassFieldTheory.ClassFieldAxiom

end
