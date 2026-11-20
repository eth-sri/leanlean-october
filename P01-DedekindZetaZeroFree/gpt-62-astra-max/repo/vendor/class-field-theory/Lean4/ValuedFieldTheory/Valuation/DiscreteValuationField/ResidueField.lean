module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

namespace ValuationTheory

/-!
# Residue-field API for local maps

This file adds reusable local-ring residue-field lemmas that are used by the
Henselian and unramified parts of the DVF library.  It keeps mathlib's
`IsLocalRing.ResidueField.map` and `IsLocalRing.residue` as the primary
objects.
-/

noncomputable section

universe u v w

namespace DiscreteValuationField
namespace ResidueField

variable {R : Type u} {S : Type v} {T : Type w}

section LocalRing

variable [CommRing R] [IsLocalRing R]

/-- Equality in the residue field is equality modulo the maximal ideal. -/
theorem residue_eq_residue_iff_sub_mem_maximalIdeal (x y : R) :
    IsLocalRing.residue R x = IsLocalRing.residue R y ↔
      x - y ∈ IsLocalRing.maximalIdeal R := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]

end LocalRing

section FieldLift

variable [CommRing R] [IsLocalRing R] [Field S]
variable (f : R →+* S) [IsLocalHom f]

end FieldLift

section LocalHom

variable [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
variable (f : R →+* S) [IsLocalHom f]

/-- A local homomorphism pulls back the target maximal ideal to the source
maximal ideal. -/
theorem comap_maximalIdeal_eq :
    (IsLocalRing.maximalIdeal S).comap f = IsLocalRing.maximalIdeal R :=
  IsLocalRing.maximalIdeal_comap f

/-- A local homomorphism induces an injective map on residue fields. -/
theorem map_injective :
    Function.Injective (IsLocalRing.ResidueField.map f) := by
  apply RingHom.injective

/-- The residue-field isomorphism induced by a surjective residue-field map
coming from a local homomorphism. -/
noncomputable def ringEquivOfSurjective
    (hsurj : Function.Surjective (IsLocalRing.ResidueField.map f)) :
    IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField S :=
  RingEquiv.ofBijective (IsLocalRing.ResidueField.map f)
    ⟨map_injective f, hsurj⟩

/-- The residue-ring equivalence induced by a surjective map evaluates by that map. -/
@[simp]
theorem ringEquivOfSurjective_apply
    (hsurj : Function.Surjective (IsLocalRing.ResidueField.map f))
    (x : IsLocalRing.ResidueField R) :
    ringEquivOfSurjective f hsurj x =
      IsLocalRing.ResidueField.map f x :=
  rfl

end LocalHom

section Algebra

variable [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
variable [Algebra R S] [IsLocalHom (algebraMap R S)]

/-- For a local algebra map, mathlib's residue-field algebra map agrees with
the residue-field map induced by the structure homomorphism. -/
theorem algebraMap_eq_map_algebraMap :
    algebraMap (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S) =
      IsLocalRing.ResidueField.map (algebraMap R S) := by
  rfl

/-- The residue-field map induced by a local algebra map is injective. -/
theorem map_algebraMap_injective :
    Function.Injective
      (IsLocalRing.ResidueField.map (algebraMap R S)) :=
  map_injective (algebraMap R S)

end Algebra

section AlgEquiv

variable [CommRing T] [IsLocalRing T]
variable [CommRing R] [IsLocalRing R] [Algebra T R]
variable [CommRing S] [IsLocalRing S] [Algebra T S]
variable [IsLocalHom (algebraMap T R)] [IsLocalHom (algebraMap T S)]

variable (e : R ≃ₐ[T] S)

/-- A local algebra equivalence induces an algebra equivalence on residue
fields over the base residue field. -/
noncomputable def algEquivOfAlgEquiv :
    IsLocalRing.ResidueField R ≃ₐ[IsLocalRing.ResidueField T]
      IsLocalRing.ResidueField S := by
  letI : IsLocalHom (e.toRingEquiv : R →+* S) :=
    IsLocalHom.of_surjective (e.toRingEquiv : R →+* S) e.surjective
  letI : IsLocalHom (e.symm.toRingEquiv : S →+* R) :=
    IsLocalHom.of_surjective (e.symm.toRingEquiv : S →+* R) e.symm.surjective
  exact
    { IsLocalRing.ResidueField.mapEquiv e.toRingEquiv with
      commutes' := by
        intro x
        obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective x
        simp [IsLocalRing.ResidueField.algebraMap_residue,
          IsLocalRing.ResidueField.map_residue, e.commutes t] }

/-- The residue-field equivalence induced by an algebra equivalence acts through
residue representatives. -/
@[simp]
theorem algEquivOfAlgEquiv_apply
    (x : IsLocalRing.ResidueField R) :
    algEquivOfAlgEquiv e x =
      IsLocalRing.ResidueField.map e.toRingEquiv x :=
  rfl

/-- The inverse induced residue equivalence agrees with the inverse quotient-map equivalence. -/
theorem algEquivOfAlgEquiv_symm_apply_eq_mapEquiv
    (x : IsLocalRing.ResidueField S) :
    (algEquivOfAlgEquiv e).symm x =
      IsLocalRing.ResidueField.mapEquiv e.symm.toRingEquiv x :=
  rfl

/-- The induced residue equivalence sends the residue of an integral element to
its transported residue. -/
@[simp]
theorem algEquivOfAlgEquiv_apply_residue (x : R) :
    algEquivOfAlgEquiv e (IsLocalRing.residue R x) =
      IsLocalRing.residue S (e x) := by
  rfl

/-- The inverse induced residue equivalence sends residues back along the inverse
algebra equivalence. -/
@[simp]
theorem algEquivOfAlgEquiv_symm_apply_residue (x : S) :
    (algEquivOfAlgEquiv e).symm (IsLocalRing.residue S x) =
      IsLocalRing.residue R (e.symm x) := by
  rfl

/-- Passing to residue fields commutes with inversion of algebra equivalences. -/
@[simp]
theorem algEquivOfAlgEquiv_symm :
    (algEquivOfAlgEquiv e).symm = algEquivOfAlgEquiv e.symm := by
  ext x
  rfl

end AlgEquiv

end ResidueField
end DiscreteValuationField

end

end ValuationTheory
