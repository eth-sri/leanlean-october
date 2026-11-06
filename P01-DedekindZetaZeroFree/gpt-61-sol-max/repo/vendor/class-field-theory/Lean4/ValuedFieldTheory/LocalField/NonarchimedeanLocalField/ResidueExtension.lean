module

public import Mathlib

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.Valuation.Extension
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueUnits

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/













/-!
# Residue extensions

Constructs the maps induced on valuation rings, residue fields, and residue
units by a valued extension, with degree, trace, norm, and Frobenius results.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- The local-ring homomorphism on valuation integer rings induced by an extension
of valuations. -/
def integerRingMapOfValuationExtension (K L : Type u) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    𝒪[K] →+* 𝒪[L] :=
  algebraMap 𝒪[K] 𝒪[L]

/-- The map of valuation rings induced by a valued-field extension is a local ring homomorphism. -/
instance integerRingMapOfValuationExtension_isLocalHom (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    IsLocalHom (integerRingMapOfValuationExtension K L) := by
  change IsLocalHom (algebraMap 𝒪[K] 𝒪[L])
  infer_instance

section
variable (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
include K L
/-- The valuation-ring map of an extension is the ambient algebra map on underlying elements. -/
@[simp]
theorem integerRingMapOfValuationExtension_apply  
    (x : 𝒪[K]) :
    integerRingMapOfValuationExtension K L x = algebraMap 𝒪[K] 𝒪[L] x :=
  rfl

/-- The residue-field map induced by a valuation extension.  This is the
canonical `algebraMap 𝓀[K] 𝓀[L]`, named so later
local class field theory files can use it without unfolding mathlib's valuation-extension instances. -/
def residueFieldMapOfValuationExtension    :=
  IsLocalRing.ResidueField.map (integerRingMapOfValuationExtension K L)







/-- The residue-field map sends the residue of a base integer to the residue of its image in the
extension. -/
@[simp]
theorem residueFieldMapOfValuationExtension_residue  
    (x : 𝒪[K]) :
    residueFieldMapOfValuationExtension K L (IsLocalRing.residue 𝒪[K] x) =
      IsLocalRing.residue 𝒪[L] (integerRingMapOfValuationExtension K L x) :=
  rfl

/-- The residue-field algebra map commutes with reduction of valuation-ring elements. -/
@[simp]
theorem residueField_algebraMap_residue  
    (x : 𝒪[K]) :
    algebraMap 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[K] x) =
      IsLocalRing.residue 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] x) :=
  rfl

/-- The induced map on residue-field unit groups. -/
def residueUnitsMapOfValuationExtension   :
    𝓀[K]ˣ →* 𝓀[L]ˣ :=
  Units.map (residueFieldMapOfValuationExtension K L)

/-- The induced map on residue-field units applies the residue-field extension map to the underlying
residue. -/
@[simp]
theorem residueUnitsMapOfValuationExtension_apply  
    (u : 𝓀[K]ˣ) :
    ((residueUnitsMapOfValuationExtension K L u : 𝓀[L]ˣ) : 𝓀[L]) =
      algebraMap 𝓀[K] 𝓀[L] (u : 𝓀[K]) :=
  rfl

/-- The induced map on residue-field unit groups is injective. -/
def residueUnitsMapOfValuationExtension_injective    :=
  Units.map_injective (RingHom.injective (residueFieldMapOfValuationExtension K L))

/-- Base integer units embedded into extension integer units. -/
def integerUnitsMapOfValuationExtension    :=
  Units.map (integerRingMapOfValuationExtension K L).toMonoidHom

/-- The induced map on valuation-ring units applies the extension's integer-ring map to the
underlying unit. -/
@[simp]
theorem integerUnitsMapOfValuationExtension_apply  
    (u : 𝒪[K]ˣ) :
    ((integerUnitsMapOfValuationExtension K L u : 𝒪[L]ˣ) : 𝒪[L]) =
      integerRingMapOfValuationExtension K L (u : 𝒪[K]) :=
  rfl

/-- Mapping an integer unit to the extension and then reducing agrees with reducing first and
mapping residue units. -/
@[simp]
theorem residueUnitsMap_integerUnitsToResidueUnits  
    (u : 𝒪[K]ˣ) :
    residueUnitsMapOfValuationExtension K L (integerUnitsToResidueUnits K u) =
      integerUnitsToResidueUnits L (integerUnitsMapOfValuationExtension K L u) := by
  ext
  rfl

/-- A first principal unit remains a first principal unit after extension of valued fields. -/
theorem integerUnitsMapOfValuationExtension_mem_principalUnits_one  
    (u : 𝒪[K]ˣ) (hu : u ∈ principalUnits K 1) :
    integerUnitsMapOfValuationExtension K L u ∈ principalUnits L 1 := by
  rw [← integerUnitsToResidueUnits_eq_one_iff_mem_principalUnits_one L]
  rw [← residueUnitsMap_integerUnitsToResidueUnits K L u]
  rw [(integerUnitsToResidueUnits_eq_one_iff_mem_principalUnits_one K u).2 hu]
  apply map_one

/-- The map on integer-unit residue quotients induced by a valuation extension. -/
def integerUnitsModPrincipalUnitsMapOfValuationExtension   :
    IntegerUnitsModPrincipalUnits K →* IntegerUnitsModPrincipalUnits L :=
  integerUnitsModPrincipalUnitsLift
    ((integerUnitsModPrincipalUnitsMk L).comp
      (integerUnitsMapOfValuationExtension K L))
    (by
      intro u hu
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        IntegerUnitsModPrincipalUnits_mk_eq_one_iff]
      apply integerUnitsMapOfValuationExtension_mem_principalUnits_one <;> assumption)

/-- The map modulo first principal units sends a class to the class of the extended integer unit. -/
@[simp]
theorem integerUnitsModPrincipalUnitsMapOfValuationExtension_mk  
    (u : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsMapOfValuationExtension K L
        (integerUnitsModPrincipalUnitsMk K u) =
      integerUnitsModPrincipalUnitsMk L
        (integerUnitsMapOfValuationExtension K L u) :=
  rfl







































/-- The residue-field norm transported to the integer-unit quotients
`𝒪[L]ˣ/U_L¹ → 𝒪[K]ˣ/U_K¹`.

This is not the local field norm on integer units; it is the quotient-level
residue norm model used before proving compatibility with `normIntegerUnits`. -/
def integerUnitsModPrincipalUnitsResidueNormOfValuationExtension   :
    IntegerUnitsModPrincipalUnits L →* IntegerUnitsModPrincipalUnits K :=
  (integerUnitsModPrincipalUnitsEquivResidueUnits K).symm.toMonoidHom.comp
    ((Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L]))).comp
      (integerUnitsModPrincipalUnitsEquivResidueUnits L).toMonoidHom)

/-- The residue norm on classes modulo first principal units agrees with the finite residue-field
norm. -/
theorem integerUnitsModPrincipalUnitsResidueNorm_residue  
    (x : IntegerUnitsModPrincipalUnits L) :
    integerUnitsModPrincipalUnitsEquivResidueUnits K
        (integerUnitsModPrincipalUnitsResidueNormOfValuationExtension K L x) =
      Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L]))
        (integerUnitsModPrincipalUnitsEquivResidueUnits L x) := by
  change
    integerUnitsModPrincipalUnitsEquivResidueUnits K
        ((integerUnitsModPrincipalUnitsEquivResidueUnits K).symm
          (Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L]))
            (integerUnitsModPrincipalUnitsEquivResidueUnits L x))) =
      Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L]))
        (integerUnitsModPrincipalUnitsEquivResidueUnits L x)
  exact (integerUnitsModPrincipalUnitsEquivResidueUnits K).apply_symm_apply _
end


section
variable (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
include K L
/-- The finite-field residue norm, after base extension to `𝓀[L]`, is the
product over all residue-field automorphisms. -/
theorem residueUnitsMap_residueField_norm_eq_prod_algEquiv  
    (u : 𝓀[L]ˣ) :
    residueUnitsMapOfValuationExtension K L
        (Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L])) u) =
      Finset.univ.prod (fun τ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] =>
        Units.mapEquiv τ.toMulEquiv u) := by
  ext
  change algebraMap 𝓀[K] 𝓀[L] (Algebra.norm 𝓀[K] (u : 𝓀[L])) =
    ↑(Finset.univ.prod (fun τ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] =>
      Units.mapEquiv τ.toMulEquiv u))
  rw [Algebra.norm_eq_prod_automorphisms]
  simp

/-- Quotient-level form of
`residueUnitsMap_residueField_norm_eq_prod_algEquiv`. -/
theorem integerUnitsModPrincipalUnitsResidueNorm_base_extend_eq_prod_algEquiv
     
    (x : IntegerUnitsModPrincipalUnits L) :
    residueUnitsMapOfValuationExtension K L
        (integerUnitsModPrincipalUnitsEquivResidueUnits K
          (integerUnitsModPrincipalUnitsResidueNormOfValuationExtension K L x)) =
      Finset.univ.prod (fun τ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] =>
        Units.mapEquiv τ.toMulEquiv (integerUnitsModPrincipalUnitsEquivResidueUnits L x)) := by
  rw [integerUnitsModPrincipalUnitsResidueNorm_residue]
  apply residueUnitsMap_residueField_norm_eq_prod_algEquiv

/-- The residue-field automorphism group has order the finite residue-field
extension degree. -/
theorem residueAlgEquiv_card_eq_finrank   :
    Nat.card (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) = Module.finrank 𝓀[K] 𝓀[L] :=
  IsGalois.card_aut_eq_finrank (F := 𝓀[K]) (E := 𝓀[L])

/-- The mathlib inertia degree of the maximal ideals agrees with the concrete
degree of the canonical residue-field extension supplied by a valuation
extension. -/
theorem maximalIdeal_inertiaDeg_eq_residue_finrank   :
    (𝓂[L] : Ideal 𝒪[L]).inertiaDeg 𝒪[K] =
      Module.finrank 𝓀[K] 𝓀[L] := by
  rw [Ideal.inertiaDeg_eq_of_isMaximal (𝓂[K] : Ideal 𝒪[K]) (𝓂[L] : Ideal 𝒪[L])]
  rfl
end














/-- Finite separable extensions whose valuation ring is the integral closure of
the base valuation ring give a finite module extension of valuation integer
rings. -/
theorem integerRing_moduleFinite_of_isIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Module.Finite 𝒪[K] 𝒪[L] :=
  IsIntegralClosure.finite 𝒪[K] K L 𝒪[L]












section
variable (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L]
include K L
/-- The actual ramification index and inertia degree of the valuation-integer
ring extension satisfy the local ramification identity. -/
theorem maximalIdeal_ramificationIdx_mul_inertiaDeg_eq_finrank   [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] :
    Ideal.ramificationIdx' (𝓂[K] : Ideal 𝒪[K]) (𝓂[L] : Ideal 𝒪[L]) *
      (𝓂[L] : Ideal 𝒪[L]).inertiaDeg 𝒪[K] =
        Module.finrank K L := by
  classical
  have := FaithfulSMul.of_field_isFractionRing 𝒪[K] 𝒪[L] K L
  have hp := IsDiscreteValuationRing.not_a_field 𝒪[K]
  have hprimes := IsLocalRing.primesOver_eq (A := 𝒪[L]) hp
  have hq (q : (𝓂[K] : Ideal 𝒪[K]).primesOver 𝒪[L]) :
      (q : Ideal 𝒪[L]) = 𝓂[L] :=
    Set.mem_singleton_iff.mp (hprimes ▸ q.property)
  let : Unique ((𝓂[K] : Ideal 𝒪[K]).primesOver 𝒪[L]) :=
    { default := ⟨𝓂[L], hprimes ▸ Set.mem_singleton _⟩
      uniq := fun q => Subtype.ext (Set.mem_singleton_iff.mp (hprimes ▸ q.property)) }
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ hp,
    IsFractionRing.finrank_eq 𝒪[K] K 𝒪[L] L]
  simpa only [Fintype.sum_unique, hq] using
    (Ideal.sum_ramification_inertia_eq_finrank (𝓂[K] : Ideal 𝒪[K]) 𝒪[L])

/-- The local ramification identity with the inertia degree rewritten as the
finite-dimensional degree of the canonical residue-field extension. -/
theorem maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank
      [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] :
    Ideal.ramificationIdx' (𝓂[K] : Ideal 𝒪[K]) (𝓂[L] : Ideal 𝒪[L]) *
      Module.finrank 𝓀[K] 𝓀[L] =
        Module.finrank K L := by
  rw [← maximalIdeal_inertiaDeg_eq_residue_finrank K L]
  exact maximalIdeal_ramificationIdx_mul_inertiaDeg_eq_finrank K L

/-- finite extensions of discrete valuations, finite-extension degree formula with
module-finiteness generated from the actual integral-closure hypothesis.

This is the source-producing form used by later local CFT files: the finite
`𝒪[K]`-module structure on `𝒪[L]` is produced from integral closure and
separability, not exposed as a separate theorem-shaped input. -/
theorem maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank_of_isIntegralClosure
      [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Ideal.ramificationIdx' (𝓂[K] : Ideal 𝒪[K]) (𝓂[L] : Ideal 𝒪[L]) *
      Module.finrank 𝓀[K] 𝓀[L] =
        Module.finrank K L := by
  let  :=
    integerRing_moduleFinite_of_isIntegralClosure K L
  exact maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank K L






































/-- The residue-field extension supplied by a local-field valuation extension is separable. -/
theorem residueFieldAlgebra_isSeparable_of_valuationExtension  
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    Algebra.IsSeparable 𝓀[K] 𝓀[L] := by
  infer_instance

/-- The trace map for the canonical residue-field extension supplied by a
valuation extension is surjective. -/
theorem residueField_trace_surjective_of_valuationExtension  
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    Function.Surjective (Algebra.trace 𝓀[K] 𝓀[L]) := by
  let : Algebra.IsSeparable 𝓀[K] 𝓀[L] :=
    residueFieldAlgebra_isSeparable_of_valuationExtension K L
  exact Algebra.trace_surjective 𝓀[K] 𝓀[L]

/-- The finite-field norm on residue-field units is surjective for the canonical
residue extension induced by a valuation extension. -/
theorem residueField_units_norm_surjective_of_valuationExtension  
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    Function.Surjective (Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L]))) := by
  let := Fintype.ofFinite 𝓀[K]
  exact FiniteField.unitsMap_norm_surjective 𝓀[K] 𝓀[L]













/-- The residue norm on integer units modulo first principal units is surjective. -/
theorem integerUnitsModPrincipalUnitsResidueNorm_surjective_of_valuationExtension
     
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    Function.Surjective
      (integerUnitsModPrincipalUnitsResidueNormOfValuationExtension K L) := by
  intro y
  obtain ⟨v, hv⟩ := residueField_units_norm_surjective_of_valuationExtension K L
    (integerUnitsModPrincipalUnitsEquivResidueUnits K y)
  refine ⟨(integerUnitsModPrincipalUnitsEquivResidueUnits L).symm v, ?_⟩
  apply (integerUnitsModPrincipalUnitsEquivResidueUnits K).injective
  rw [integerUnitsModPrincipalUnitsResidueNorm_residue]
  exact (congrArg (Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L])))
    ((integerUnitsModPrincipalUnitsEquivResidueUnits L).apply_symm_apply v)).trans hv
end


end
end LocalFieldTheory
