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
lemma toSubmodule_bot : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := rfl

@[simp]
lemma toSubmodule_top : (⊤ : Subrepresentation ρ).toSubmodule = ⊤ := rfl

instance instNontrivial [Nontrivial W] : Nontrivial (Subrepresentation ρ) :=
  ⟨⟨⊥, ⊤, fun hc => _root_.bot_ne_top (α := Submodule A W) (by
    rw [← toSubmodule_bot (ρ := ρ), ← toSubmodule_top (ρ := ρ), hc])⟩⟩



end Subrepresentation

namespace MonoidHom
