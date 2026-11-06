module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.RepresentationTheory.Character
public import DedekindZetaZeroFree.RepresentationTheory.Subrepresentations.Restriction

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/FDRep.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

universe u v w

namespace Representation

@[simp]
theorem char_prod {k : Type u} {G : Type v} {V W : Type*} [Field k] [Monoid G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W) (g : G) :
    (ρ.prod σ).character g = ρ.character g + σ.character g := by
  have hg : (ρ.prod σ) g = LinearMap.prodMap (ρ g) (σ g) := rfl
  rw [character, character, character, hg]
  exact LinearMap.trace_prodMap' (ρ g) (σ g)

end Representation

namespace Subrepresentation

end Subrepresentation

namespace FDRep

open CategoryTheory

instance (priority := 100) forget₂Rep {R : Type u} [Ring R] {G : Type v} [Monoid G] :
    HasForget₂ (FDRep R G) (Rep R G) where
  forget₂ := (forget₂ (FGModuleCat R) (ModuleCat R)).mapAction G ⋙ Rep.ActionToRep R G

@[simp]
theorem finrank_forget₂_obj {R : Type u} {G : Type v} [CommRing R] [Monoid G]
    (A : FDRep R G) :
    Module.finrank R ((forget₂ (FDRep R G) (Rep R G)).obj A) = Module.finrank R A :=
  rfl

@[simp]
theorem character_ρ {k : Type u} {G : Type v} [Field k] [Monoid G] (A : FDRep k G) (g : G) :
    Representation.character A.ρ g = A.character g :=
  rfl

@[simp]
theorem character_of {k : Type u} {G : Type v} {V : Type u} [Field k] [Monoid G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (rho : Representation k G V) :
    (FDRep.of rho).character = rho.character :=
  rfl

instance forget₂_additive {R : Type u} {G : Type v} [CommRing R] [Monoid G] :
    (forget₂ (FDRep R G) (Rep R G)).Additive where
  map_add := by
    intros
    apply Rep.hom_ext
    ext x

    rfl

section Biproduct

open CategoryTheory Limits

variable {k : Type u} {G : Type v} [Field k] [Monoid G]

end Biproduct

section TensorUnit

open CategoryTheory MonoidalCategory

end TensorUnit

section Kernel

variable {k : Type u} {G : Type v} [Field k] [Group G]

end Kernel

section CommonKernel

variable {ι : Type*} {k : Type u} {G : Type v} [CommRing k] [Group G]

instance normal_iInf_ker (W : ι → FDRep k G) : (⨅ i, (W i).ρ.ker).Normal :=
  Subgroup.normal_iInf_normal fun _ => inferInstance
