module

public import Mathlib.RepresentationTheory.Irreducible

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/RepresentationTheory/Subrepresentation.lean`. Original Apache-2.0 copyright and authors retained.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: import/module surface and TauCeti-owned namespace references only;
root Mathlib extensions are retained. Proof bodies otherwise unchanged.
License: vendor root LICENSE.
-/

namespace Subrepresentation

variable {A G W : Type*} [Semiring A] [Monoid G] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G W}

@[simp]
lemma mem_toSubmodule {ρ' : Subrepresentation ρ} {v : W} : v ∈ ρ'.toSubmodule ↔ v ∈ ρ' := Iff.rfl

@[simp]
lemma toSubmodule_bot : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := rfl

@[simp]
lemma toSubmodule_top : (⊤ : Subrepresentation ρ).toSubmodule = ⊤ := rfl

instance instNontrivial [Nontrivial W] : Nontrivial (Subrepresentation ρ) :=
  ⟨⟨⊥, ⊤, fun hc => _root_.bot_ne_top (α := Submodule A W) (by
    rw [← toSubmodule_bot (ρ := ρ), ← toSubmodule_top (ρ := ρ), hc])⟩⟩



































section AsSubmodule

open scoped MonoidAlgebra

variable {A G W : Type*} [CommRing A] [Monoid G] [AddCommGroup W] [Module A W]
  {ρ : Representation A G W}






end AsSubmodule

section Splitting

variable {A G W : Type*} [Ring A] [Monoid G] [AddCommGroup W] [Module A W]
  {ρ : Representation A G W}























end Splitting

end Subrepresentation

namespace MonoidHom

variable {k : Type*} [Semiring k] {H K : Type*} [Monoid H] [Monoid K]
  {V : Type*} [AddCommMonoid V] [Module k V]

def resSubrepresentationOrderIso (f : H →* K) (hf : Function.Surjective f)
    (ρ : Representation k K V) :
    Subrepresentation (ρ.comp f) ≃o Subrepresentation ρ where
  toFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun h v hv ↦ by
        obtain ⟨g, rfl⟩ := hf h
        exact S.apply_mem_toSubmodule g hv }
  invFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun h v hv ↦ S.apply_mem_toSubmodule (f h) hv }
  left_inv S := by ext; rfl
  right_inv S := by ext; rfl
  map_rel_iff' := by rfl













end MonoidHom

section Irreducible

variable {k : Type*} [Field k] {H K : Type*} [Monoid H] [Monoid K]
  {V : Type*} [AddCommGroup V] [Module k V]

@[simp]
theorem MonoidHom.isIrreducible_comp_surjective_iff (f : H →* K) (hf : Function.Surjective f)
    (ρ : Representation k K V) :
    Representation.IsIrreducible (ρ.comp f) ↔ Representation.IsIrreducible ρ :=
  (f.resSubrepresentationOrderIso hf ρ).isSimpleOrder_iff

@[simp]
theorem MulEquiv.isIrreducible_comp_equiv_iff (e : H ≃* K) (ρ : Representation k K V) :
    Representation.IsIrreducible (ρ.comp (e : H →* K)) ↔ Representation.IsIrreducible ρ :=
  e.toMonoidHom.isIrreducible_comp_surjective_iff e.surjective ρ

end Irreducible
