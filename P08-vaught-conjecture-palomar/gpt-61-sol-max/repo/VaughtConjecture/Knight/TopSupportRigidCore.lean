/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.FiniteCoverReceivingCore
import VaughtConjecture.Knight.OrdinaryFiniteCutReceiving
import VaughtConjecture.Knight.BlockCode
import VaughtConjecture.Knight.TopSupportRigidCoreCap

/-! # Classification from globally rigid top-support cores

Model-level chart extension, isomorphism, and countability results for globally rigid cores.
-/

namespace VaughtConjecture.Knight.TopSupportRigidCore
universe w
variable {α : LimitStage} {M M₁ M₂ : Type w} {R : KnightRealization α M}
  {R₁ : KnightRealization α M₁} {R₂ : KnightRealization α M₂}

/-- **Classification**: two countable models at the same stage with globally rigid cores of the
same finite type are isomorphic. -/
theorem nonempty_iso_of_rigidCores [Countable M₁] [Countable M₂] (hM₁ : R₁.IsModel)
    (hM₂ : R₂.IsModel) {k : ℕ} {B₁ : Fin k ↪ M₁} {B₂ : Fin k ↪ M₂} {b : S α.1 k}
    (h₁ : R₁.eval B₁ = some b) (h₂ : R₂.eval B₂ = some b) (r₁ : RigidCore R₁ B₁)
    (r₂ : RigidCore R₂ B₂) : Nonempty (R₁.Iso R₂) := by
  have := hM₁.nonempty
  have := hM₂.nonempty
  exact nonempty_iso_of_rigidCores_of_receiving hM₁.consistent hM₁.covering
    (OrdinaryModelReceiving.finiteCutReceiving hM₁) hM₂.consistent hM₂.covering
    (OrdinaryModelReceiving.finiteCutReceiving hM₂) h₁ h₂ r₁ r₂

/-- Enlarging a globally rigid core preserves rigidity, whether or not the
initial tuple itself has a label. -/
theorem rigidCore_mono {k m} {B} {C}
    (hB : RigidCore R B) (f : Fin k ↪ Fin m) (hf : f.trans C = B) : RigidCore R C := by
  intro n D d hd e he H hH ht
  apply hB D d hd (f.trans e) (by aesop) H hH
  intro x hx htop
  apply ht x ?_ htop
  intro z hz
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (hx hz)
  exact Finset.mem_image.mpr ⟨f i, Finset.mem_univ _, hi⟩

/-- Any globally rigid tuple has an actual labelled rigid cover. -/
theorem exists_labelled_core (hM : R.IsModel)
    (h : ∃ (k : ℕ) (B : Fin k ↪ M), RigidCore R B) :
    ∃ (k : ℕ) (B : Fin k ↪ M) (b : S α.1 k), R.eval B = some b ∧ RigidCore R B := by
  obtain ⟨k, B, hB⟩ := h
  obtain ⟨j, C, hC, hsome⟩ := hM.covering B
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hsome
  exact ⟨k + j, C, c, hc, rigidCore_mono hB (Fin.castAddEmb j) hC⟩

