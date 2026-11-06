
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.SourceLayerCarrier

/-! # A source layer admitting retained proper owners at the same grade

Reuse the ordered sum inventory unchanged. Separation is the exact geometric
condition that a new full controller is not below an old owner. Proper scope
supplies it even when the old owner has the new controller's grade.
-/

namespace VaughtConjecture.Knight.SeparatedSourceLayerCarrier

open AmalgamationPlan  Value  SourceLayerCarrier

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
variable (D : CellScheme A) (Q : Type*) [Fintype Q] (k : ℕ)
variable (hk : 0 < k) (hA : k ≤ A.card)

theorem separated_of_proper (hp : AvoidsValue D.scope A) :
    ∀ d , ¬ GradedLe (A, k) (D.cell d) := by
  intro d hd
  exact hp d (Finset.Subset.antisymm
    (D.scope_subset d) hd.1)

variable (hseparated : ∀ d , ¬ GradedLe (A, k) (D.cell d))

omit [Fintype Q] in
local notation "index₀" => index D Q k

include hseparated in
theorem below_old x c
    (h : GradedLe (index₀ x) (D.cell c)) :
    ∃ d : D.belowCell c, x = .inl d.1 := by
  cases x with
  | inl d => exact ⟨⟨d, h⟩, rfl⟩
  | inr q => exact False.elim (hseparated c h)

local notation "scheme₀" => scheme D Q k hk hA

local notation "toCell₀" => toCell D Q k hk hA

local notation "toOcc₀" => toOcc D Q k hk hA

noncomputable def ownerEquiv c : D.belowCell c ≃
    (scheme₀).below ((scheme₀).cell (toCell₀ (.inl c))) :=
  Equiv.ofBijective
    (fun d => ⟨toCell₀ (.inl d.1), by
      simpa only [cell_toCell, index] using d.2⟩)
    ⟨by
      intro d e h
      exact Subtype.ext ((old_order).injective (congrArg Subtype.val h)), by
      intro e
      have he  := by
        simpa only [cell_eq, toOcc_toCell, index] using e.2
      obtain ⟨d, hd⟩ := below_old D Q k hseparated _ c he
      refine ⟨d, Subtype.ext ?_⟩
      change toCell₀ (.inl d.1) = e.1
      rw [← hd, toCell_toOcc]⟩

local notation "ownerEquiv₀" => ownerEquiv D Q k hk hA hseparated

theorem ownerEquiv_val c d :
    (ownerEquiv₀ c d).1 = toCell₀ (.inl d.1) := rfl

include hseparated in
variable {D Q k} in
theorem old_not_full {d : Cell D} :
    (scheme₀).cell (toCell₀ (.inl d)) ≠ (A, k) := by
  rw [cell_toCell]
  exact fun he => hseparated d (he.symm ▸ GradedLe.refl (A, k))

noncomputable def controller (q : Q) :
    SourcePrefixLayer.Controller (scheme₀) k :=
  ⟨toCell₀ (.inr q), cell_toCell D Q k hk hA (.inr q)⟩

noncomputable def controllerEquiv :=
  Equiv.ofBijective (controller D Q k hk hA) ⟨by
    intro p q hpq
    exact Sum.inr.inj ((enumeration).injective (congrArg Subtype.val hpq)), by
    intro c
    have hc := c.2
    rw [cell_eq] at hc
    cases he : toOcc₀ c.1 with
    | inl d =>
      rw [he] at hc
      exact False.elim (hseparated d (hc.symm ▸ GradedLe.refl (A, k)))
    | inr q =>
      refine ⟨q, Subtype.ext ?_⟩
      change toCell₀ (.inr q) = c.1
      rw [← he, toCell_toOcc]⟩

variable (sem : Semantics D)

noncomputable def oldTable : (Cell D ⊕ Q) → (Cell D ⊕ Q) → ExtOrd
  | .inl c, .inl d => AmalgamatedBoundaryRows.total sem c d
  | _, _ => ⊥

omit [Fintype Q] in
local notation "oldTable₀" => oldTable D Q sem

include hseparated in
theorem oldTable_visible c d (h : GradedLe (index₀ d) (index₀ c)) :
    SelfVis (index₀ d).2 (oldTable₀ c d) := by
  cases c with
  | inl c =>
    obtain ⟨e, rfl⟩ := below_old D Q k hseparated d c h
    change SelfVis (D.grade e.1) (AmalgamatedBoundaryRows.total sem c e.1)
    rw [AmalgamatedBoundaryRows.total_below]
    exact (sem.orderly c e).symm
  | inr q => cases d <;> exact selfVis_bot

noncomputable def base : Semantics (scheme₀) where
  E c d := oldTable₀ (toOcc₀ c) (toOcc₀ d.1)
  orderly c d := by
    have h : GradedLe (index₀ (toOcc₀ d.1))
        (index₀ (toOcc₀ c)) := by
      simpa only [← cell_eq] using d.2
    have hv := oldTable_visible D Q k hseparated sem _ _ h
    change oldTable₀ (toOcc₀ c) (toOcc₀ d.1) =
      extVisibilityReplace (oldTable₀ (toOcc₀ c) (toOcc₀ d.1))
        ((scheme₀).cell d.1).2 ((scheme₀).cell d.1).2
    simpa only [cell_eq] using hv.symm

local notation "base₀" => base D Q k hk hA hseparated

theorem base_old {c} d :
    (base₀ sem).E (toCell₀ (.inl c))
      (ownerEquiv₀ c d) = sem.E c d := by
  change oldTable₀ (toOcc₀ (toCell₀ (.inl c)))
    (toOcc₀ (ownerEquiv₀ c d).1) = _
  rw [ownerEquiv_val, toOcc_toCell, toOcc_toCell]
  exact AmalgamatedBoundaryRows.total_below sem c d

variable {D Q k hk hA} in
theorem base_respects_iff c
    p :
    RespectsSemanticsBelow (base₀ sem) _ p ↔
      Semantics.RowLawful sem c (p ∘ ownerEquiv₀ c) := by
  have h := respects_iff_of_equiv (sem' := sem) (sem := base₀ sem)
    (ownerEquiv₀ c)
    (fun d => (congrArg Prod.snd (cell_toCell D Q k hk hA (.inl d.1))).symm)
    (fun d e => ?_) (fun b d hd => ?_) (p ∘ ownerEquiv₀ c)
  · have he : (p ∘ ownerEquiv₀ c) ∘
        (ownerEquiv₀ c).symm = p := by
      grind
    rw [he] at h
    exact h.symm
  · change D.scope d.1 ⊆ D.scope e.1 ↔
      ((scheme₀).cell (toCell₀ (.inl d.1))).1 ⊆
      ((scheme₀).cell (toCell₀ (.inl e.1))).1
    rw [cell_toCell, cell_toCell]
    rfl
  · exact (base_old D Q k hk hA hseparated sem d).symm
