module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


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
  intro x y hxy
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective y
  rw [IsLocalRing.ResidueField.map_residue,
    IsLocalRing.ResidueField.map_residue] at hxy
  rw [residue_eq_residue_iff_sub_mem_maximalIdeal]
  have hsubS : f (r - s) ∈ IsLocalRing.maximalIdeal S := by
    rw [map_sub]
    exact
      (residue_eq_residue_iff_sub_mem_maximalIdeal
        (R := S) (f r) (f s)).1 hxy
  have hpre : r - s ∈ (IsLocalRing.maximalIdeal S).comap f := hsubS
  rwa [comap_maximalIdeal_eq f] at hpre

/-- The residue-field isomorphism induced by a surjective residue-field map
coming from a local homomorphism. -/
def ringEquivOfSurjective
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
