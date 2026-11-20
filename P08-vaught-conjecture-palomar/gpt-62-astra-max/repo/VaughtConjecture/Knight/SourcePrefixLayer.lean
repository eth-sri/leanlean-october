/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourcePrefixRows

/-! # Installing one common-prefix controller layer

On an actual finite cell scheme, replace the rows at one maximal full-scope
grade by common-prefix rows. All other rows stay literal. The input profiles
are lawful only on the already constructed lower domains. The new-controller
incidences and their availability are constructed here, not input assumptions.

This is the row-installation half of the coupled grade induction. Existence
of the supported, grid-compatible selected lower profiles is still separate;
no full source-prefix extension or bountifulness theorem is claimed here.
-/

@[expose] public section

namespace VaughtConjecture.Knight.SourcePrefixLayer

open Transform Value ExtOrd SourcePrefixRows

variable {ι X : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {k : ℕ}

abbrev Controller (D : CellScheme A) (k : ℕ) := {c : Cell D // D.cell c = (A, k)}

/-- The actual lower-domain input to one grade step. `lower_lawful` concerns
only old owners. `grid_agreement` is the grid-agreement invariant of the already
constructed whole lower sections, not new-row locality or future completion.
The new-controller source readings are not fields: `profile` constructs them.
-/
structure Data (D : CellScheme A) (k : ℕ) (X : Type*) where
  base : Semantics D
  max_grade : ∀ d : Cell D, D.grade d ≤ k
  grid : Finset ExtOrd
  bot_mem : ⊥ ∈ grid
  ceiling : ExtOrd
  ceiling_mem : ceiling ∈ grid
  grid_bound : ∀ h ∈ grid, h ≤ ceiling
  grid_visible : ∀ h ∈ grid, SelfVis k h
  boundary : Controller D k → X → ExtOrd
  lower : Controller D k → D.Labelling
  lower_bound : ∀ q d, D.cell d ≠ (A, k) → lower q d ≤ ceiling
  lower_lawful : ∀ q c, D.cell c ≠ (A, k) →
    RespectsSemanticsBelow base (D.cell c) (fun d => lower q d.1)
  grid_agreement : ∀ p q h, h ∈ grid → Agree (boundary p) (boundary q) h →
    ∀ d, D.cell d ≠ (A, k) → min (lower p d) h = min (lower q d) h

end VaughtConjecture.Knight.SourcePrefixLayer
