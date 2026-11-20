module

public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Main
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteExtensionClassFieldAxiom
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormContinuity
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnitTopology
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Topological finite local reciprocity

This module upgrades the algebraic finite local reciprocity isomorphism to a
homeomorphic group isomorphism.  The key input is that the norm subgroup of a
finite Galois extension is open.  Consequently its quotient is discrete, as
is the topological abelianization of the finite Krull Galois group.
-/

noncomputable section

namespace LocalClassFieldTheory

open scoped NNReal ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

noncomputable local instance normQuotientTopologicalSpace
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [TopologicalSpace K] :
    TopologicalSpace (NormQuotient K L) := by
  change TopologicalSpace (Kˣ ⧸ localNormSubgroup K L)
  infer_instance

section NormSubgroupTopology

universe u

section

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [ValuativeRel L]

/-- The norm map restricted to valuation-ring units upstairs. -/
 def integerUnitNormMap : 𝒪[L]ˣ →* Kˣ :=
  (LocalFieldTheory.normUnits K L).comp (integerUnitsToFieldUnits L)

/-- The image of valuation-ring units under the field norm. -/
 def integerUnitNormSubgroup : Subgroup Kˣ :=
  MonoidHom.range (integerUnitNormMap K L)

end

private theorem integerUnitNormSubgroup_isCompact
    (K L : Type u) [NontriviallyNormedField K] [NormedField L]
    [NormedAlgebra K L] [FiniteDimensional K L] [CompleteSpace K]
    [ValuativeRel L] [CompactSpace 𝒪[L]] :
    IsCompact (integerUnitNormSubgroup K L : Set Kˣ) := by
  have hcontinuous : Continuous (integerUnitNormMap K L) :=
    (normUnits_continuous_of_finiteDimensional K L).comp
      (integerUnitsToFieldUnits_continuous L)
  have hcompact : IsCompact (Set.univ : Set 𝒪[L]ˣ) := isCompact_univ
  have himage := hcompact.image hcontinuous
  change IsCompact (Set.range (integerUnitNormMap K L))
  simpa only [Set.image_univ] using himage

private theorem integerUnitNormSubgroup_eq_localNormSubgroup_inf_baseUnits
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    integerUnitNormSubgroup K L =
      localNormSubgroup K L ⊓ localBaseUnitSubgroup K := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨⟨integerUnitsToFieldUnits L a, rfl⟩, ?_⟩
    refine ⟨normIntegerUnits K L a, ?_⟩
    apply Units.ext
    rfl
  · rintro ⟨⟨y, hy⟩, ⟨a, ha⟩⟩
    have hnorm := v_normUnits_eq_residue_finrank_mul_of_isSeparable K L y
    change v K (Additive.ofMul (LocalFieldTheory.normUnits K L y)) =
      (@Module.finrank 𝓀[K] 𝓀[L] _ _
        (IsLocalRing.ResidueField.instModule) : Int) *
        v L (Additive.ofMul y) at hnorm
    have hfinrank :
        (@Module.finrank 𝓀[K] 𝓀[L] _ _
          (IsLocalRing.ResidueField.instModule) : Int) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt Module.finrank_pos)
    obtain ⟨b, hb⟩ :=
      (integerUnitsToFieldUnits_mem_range_iff_valuationMap_eq_zero L y).2 (by
        rw [valuationMap_apply]
        exact ((mul_eq_zero.mp (by
          rw [← hnorm, hy]
          exact (by
            rw [← ha]
            exact v_integerUnitsToFieldUnits K a))).resolve_left hfinrank))
    refine ⟨b, ?_⟩
    change LocalFieldTheory.normUnits K L (integerUnitsToFieldUnits L b) = x
    rw [hb, hy]

private theorem localNormSubgroup_isOpen_of_compatibleLocalField
    (K L : Type)
    [NontriviallyNormedField K] [NormedField L] [NormedAlgebra K L]
    [CompleteSpace K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [IsNonarchimedeanLocalField L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    IsOpen (localNormSubgroup K L : Set Kˣ) := by
  have hintersection :=
    integerUnitNormSubgroup_eq_localNormSubgroup_inf_baseUnits K L
  let : Finite (Gal(L / K)) := by
    apply Nat.finite_of_card_ne_zero
    rw [IsGalois.card_aut_eq_finrank K L]
    exact Nat.ne_of_gt Module.finrank_pos
  let : Finite (Abelianization (Gal(L / K))) :=
    Finite.of_surjective Abelianization.of QuotientGroup.mk_surjective
  let :=
    Finite.of_equiv
      (Abelianization (Gal(L / K)))
      (abelianizationEquivNormQuotient K L).toEquiv
  let : Finite (Kˣ ⧸ localNormSubgroup K L) := by
    change Finite (NormQuotient K L)
    infer_instance
  let : (localNormSubgroup K L).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  let : ((localNormSubgroup K L).subgroupOf
      (localBaseUnitSubgroup K)).FiniteIndex := inferInstance

  have hrelativeClosed :
      IsClosed
        ((localNormSubgroup K L).subgroupOf (localBaseUnitSubgroup K) :
          Set (localBaseUnitSubgroup K)) := by
    rw [show
        ((localNormSubgroup K L).subgroupOf (localBaseUnitSubgroup K) :
            Set (localBaseUnitSubgroup K)) =
          (fun z : localBaseUnitSubgroup K => (z : Kˣ)) ⁻¹'
            (integerUnitNormSubgroup K L : Set Kˣ) by
      ext z
      rw [hintersection]
      constructor
      · intro hz
        exact ⟨hz, z.property⟩
      · exact fun hz => hz.1]
    exact (integerUnitNormSubgroup_isCompact K L).isClosed.preimage continuous_subtype_val

  have hrelativeOpen :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ hrelativeClosed
  have himageOpen :
      IsOpen (Subtype.val ''
        ((localNormSubgroup K L).subgroupOf (localBaseUnitSubgroup K) :
          Set (localBaseUnitSubgroup K))) :=
    (localBaseUnitSubgroup_isOpen K).isOpenMap_subtype_val _ hrelativeOpen
  have himage :
      Subtype.val ''
          ((localNormSubgroup K L).subgroupOf (localBaseUnitSubgroup K) :
            Set (localBaseUnitSubgroup K)) =
        (integerUnitNormSubgroup K L : Set Kˣ) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hintersection]
      exact ⟨hz, z.property⟩
    · intro hx
      have hx' := hx
      rw [hintersection] at hx'
      exact ⟨⟨x, hx'.2⟩, hx'.1, rfl⟩
  rw [himage] at himageOpen

  apply Subgroup.isOpen_mono

     ?_ himageOpen
  intro x hx
  rw [hintersection] at hx
  exact hx.1

/-- The norm subgroup of a finite Galois extension of a nonarchimedean local
field is open in the native topology of the base-field unit group. -/
theorem localNormSubgroup_isOpen
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    IsOpen (localNormSubgroup K L : Set Kˣ) := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  let : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  let : (Valued.v : Valuation K
      (ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField
      (L := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)

  let : NontriviallyNormedField L :=
    spectralNorm.nontriviallyNormedField K L
  let : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  let : CompleteSpace L := spectralNorm.completeSpace K L
  let : LocallyCompactSpace L :=
    LocallyCompactSpace.of_finiteDimensional_of_complete K L
  let : IsUltrametricDist L :=
    ⟨fun x y z => by
      change ‖x - z‖ ≤ max ‖x - y‖ ‖y - z‖
      rw [← sub_add_sub_cancel x y z]
      exact isNonarchimedean_spectralNorm
        (K := K) (L := L) (x - y) (y - z)⟩
  let : Valued L ℝ≥0 := NormedField.toValued
  let vL : Valuation L ℝ≥0 := Valued.v
  let : vL.IsNontrivial :=
    (inferInstance : (NormedField.valuation).IsNontrivial)
  let : ValuativeRel L := ValuativeRel.ofValuation vL
  let : vL.Compatible := Valuation.Compatible.ofValuation vL
  let : ValuativeRel.IsNontrivial L :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vL).2 inferInstance
  let : IsValuativeTopology L :=
    isValuativeTopology_of_valued_ofValuation L ℝ≥0
  let : IsNonarchimedeanLocalField L :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }

  let : (ValuativeRel.valuation K).HasExtension
      (ValuativeRel.valuation L) := by
    apply Valuation.HasExtension.ofComapInteger
    ext x
    change ValuativeRel.valuation L (algebraMap K L x) ≤ 1 ↔
      ValuativeRel.valuation K x ≤ 1
    rw [← (ValuativeRel.valuation L).vle_one_iff, vL.vle_one_iff]
    change spectralNorm K L (algebraMap K L x) ≤ 1 ↔
      ValuativeRel.valuation K x ≤ 1
    rw [spectralNorm_extends]
    exact Valued.toNormedField.norm_le_one_iff

  let : Algebra.IsIntegral 𝒪[K] 𝒪[L] := ⟨by
    intro y
    apply IsIntegral.tower_bot
      (R := 𝒪[K]) (A := 𝒪[L]) (B := L)
      (Subring.subtype_injective (ValuativeRel.valuation L).integer)
    have hyv : vL (y : L) ≤ 1 := by
      apply (vL.vle_one_iff).1
      apply ((ValuativeRel.valuation L).vle_one_iff).2
      exact y.property
    have hynorm : ‖(y : L)‖ ≤ 1 := by
      have hynormNN : ‖(y : L)‖₊ ≤ 1 := by
        simpa [vL, NormedField.valuation_apply] using hyv
      exact_mod_cast hynormNN
    change spectralNorm K L (y : L) ≤ 1 at hynorm
    have hcoeffNorm :=
      (spectralValue_le_one_iff
        (minpoly.monic (Algebra.IsIntegral.isIntegral (y : L)))).1
        (by simpa [spectralNorm] using hynorm)
    have hcoeff :
        (↑(minpoly K (y : L)).coeffs : Set K) ⊆
          (ValuativeRel.valuation K).integer := by
      intro c hc
      obtain ⟨n, _hn, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
      exact ((ValuativeRel.valuation K).mem_integer_iff _).2
        (Valued.toNormedField.norm_le_one_iff.mp (hcoeffNorm n))
    let p : Polynomial 𝒪[K] :=
      (minpoly K (y : L)).toSubring
        (ValuativeRel.valuation K).integer hcoeff
    refine ⟨p, ?_, ?_⟩
    · exact (Polynomial.monic_toSubring
        (minpoly K (y : L)) (ValuativeRel.valuation K).integer hcoeff).2
          (minpoly.monic (Algebra.IsIntegral.isIntegral (y : L)))
    · have hmaproot :
          Polynomial.aeval (y : L)
            (p.map (algebraMap 𝒪[K] K)) = 0 := by
        dsimp only [p]
        rw [show algebraMap 𝒪[K] K =
          (ValuativeRel.valuation K).integer.subtype from rfl,
          Polynomial.map_toSubring]
        exact minpoly.aeval K (y : L)
      rwa [Polynomial.aeval_map_algebraMap K (y : L) p] at hmaproot⟩

  let : Algebra.IsIntegral
      (ValuativeRel.valuation K).valuationSubring
      (ValuativeRel.valuation L).valuationSubring := by
    change Algebra.IsIntegral 𝒪[K] 𝒪[L]
    infer_instance
  let hIntegralClosure :=
    ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_isIntegralClosure_of_isIntegral
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)
  let : IsIntegralClosure 𝒪[L] 𝒪[K] L := by
    change IsIntegralClosure
      (ValuativeRel.valuation L).valuationSubring
      (ValuativeRel.valuation K).valuationSubring L
    exact hIntegralClosure

  exact localNormSubgroup_isOpen_of_compatibleLocalField K L

/-- The native quotient topology on the finite norm quotient is discrete. -/
theorem normQuotient_discrete
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    DiscreteTopology (NormQuotient K L) := by
  apply QuotientGroup.discreteTopology
  simpa using localNormSubgroup_isOpen K L

end NormSubgroupTopology

section TopologicalReciprocity

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsGalois K L]

 theorem commutator_topologicalClosure_eq
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DiscreteTopology G] :
    Subgroup.topologicalClosure (commutator G) = commutator G := by
  apply le_antisymm
  · solve_by_elim [Subgroup.topologicalClosure_minimal]
  · exact Subgroup.le_topologicalClosure _

/-- For a finite-dimensional Galois extension, algebraic and topological
abelianization agree as multiplicative groups. -/
noncomputable def topologicalAbelianization_finite_equiv :
    Abelianization (Gal(L / K)) ≃* TopologicalAbelianization (Gal(L / K)) := by
  exact QuotientGroup.quotientMulEquivOfEq (commutator_topologicalClosure_eq (Gal(L / K))).symm

/-- Finite local reciprocity as a homeomorphic group isomorphism from the
norm quotient to the topological abelianization of the Krull Galois group. -/
noncomputable def localReciprocityEquiv :
    NormQuotient K L ≃ₜ* TopologicalAbelianization (Gal(L / K)) := by
  letI : DiscreteTopology (NormQuotient K L) := normQuotient_discrete K L
  letI : DiscreteTopology (TopologicalAbelianization (Gal(L / K))) :=
    QuotientGroup.discreteTopology (isOpen_discrete _)
  exact
    { ((abelianizationEquivNormQuotient K L).symm.trans
      (topologicalAbelianization_finite_equiv K L)) with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- The quotient map to the norm quotient, bundled as a continuous
homomorphism for the native quotient topology. -/
noncomputable def normClassContinuous :
    Kˣ →ₜ* NormQuotient K L :=
  { normClass K L with
    continuous_toFun := QuotientGroup.continuous_mk }

/-- The continuous finite local Artin map. -/
noncomputable def localArtinMap :
    Kˣ →ₜ* TopologicalAbelianization (Gal(L / K)) :=
  (ContinuousMonoidHom.toContinuousMonoidHom (localReciprocityEquiv K L)).comp
    (normClassContinuous K L)

/-- The continuous finite local Artin map is surjective. -/
theorem localArtinMap_surjective :
    Function.Surjective (localArtinMap K L) :=
  (localReciprocityEquiv K L).surjective.comp
    (QuotientGroup.mk'_surjective (localNormSubgroup K L))

/-- The canonical first-isomorphism equivalence induced by the continuous
local Artin map. -/
noncomputable def localArtinMap_quotientKerEquiv :
    Kˣ ⧸ (localArtinMap K L).toMonoidHom.ker ≃*
      TopologicalAbelianization (Gal(L / K)) :=
  QuotientGroup.quotientKerEquivOfSurjective
    (localArtinMap K L).toMonoidHom (localArtinMap_surjective K L)

/-- The first-isomorphism equivalence sends the class of a field unit to its
image under the local Artin map. -/
@[simp]
theorem localArtinMap_quotientKerEquiv_mk (x : Kˣ) :
    localArtinMap_quotientKerEquiv K L (QuotientGroup.mk x) =
      localArtinMap K L x := rfl

end TopologicalReciprocity

end LocalClassFieldTheory

end
