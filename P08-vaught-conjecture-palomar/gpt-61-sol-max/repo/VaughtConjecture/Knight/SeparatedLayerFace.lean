/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.HighLayerBountiful
import VaughtConjecture.Knight.ExactSemanticFace

/-! # Literal face transport through a separated full-scope layer

Proper inherited owners may have grades above the added layer. Only separation
and literal rows are used; no global predecessor grade bound is imposed.
-/

namespace VaughtConjecture.Knight.SeparatedLayerFace
open    CoatomBoundaryExtension SourceLayerCarrier
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B : Finset ι}
  (D : CellScheme A) (Q : Type*) [Fintype Q] (k : ℕ) (hk : 0 < k) (hA : k ≤ A.card)
  (hs : ∀ d , ¬ GradedLe (A, k) (D.cell d))
  (sem : Semantics D) (out : Semantics (scheme D Q k hk hA))
  (hrow : ∀ c d,
    out.E (toCell D Q k hk hA (.inl c))
      (SeparatedSourceLayerCarrier.ownerEquiv D Q k hk hA hs c d) = sem.E c d)

variable {D Q k hk hA hs sem out} in
def face {E : CellScheme B} {old : Semantics E}
    (F : ExactSemanticFace old sem) (hB : ¬ A ⊆ B) : ExactSemanticFace old out where
  map := F.map.trans ⟨fun d => toCell D Q k hk hA (.inl d),
    (old_order).injective⟩
  index d := (cell_toCell D Q k hk hA (.inl (F.map d))).trans (F.index d)
  exhaustive z hz := by
    obtain ⟨x, rfl⟩ := (enumeration).surjective z
    change ((scheme D Q k hk hA).cell (toCell D Q k hk hA x)).1 ⊆ B at hz
    rw [cell_toCell] at hz
    cases x with
    | inl d =>
      obtain ⟨e, rfl⟩ := F.exhaustive d hz
      exact ⟨e, rfl⟩
    | inr q => exact False.elim (hB hz)
  row c d := (hrow (F.map c) ⟨F.map d.1, by rw [F.index, F.index]; exact d.2⟩).trans
    (F.row c d)

local notation "equiv₀" => HighLayerBountiful.equiv D Q k hk hA

include hrow in
theorem respects_iff J (hJ : ¬ GradedLe (A, k) J)
    p :
    RespectsSemanticsBelow sem J p ↔ RespectsSemanticsBelow out J
      (p ∘ (equiv₀ J hJ).symm) := by
  apply respects_iff_of_equiv (equiv₀ J hJ)
    (fun d => (congrArg Prod.snd (HighLayerBountiful.equiv_cell D Q k hk hA)).symm)
    (fun d e => ?_) (fun c d _ => (hrow c.1 d).symm) p
  simp only [CellScheme.scope, HighLayerBountiful.equiv_cell]

local notation "respects_iff₀" => respects_iff D Q k hk hA hs sem out hrow

include hrow in
/-- Transport an already proved lower clause, without assuming any output
bountifulness or bounding the grades of retained proper owners. -/
theorem lift {I J} (h : GradedLe I J)
    (hJ : ¬ GradedLe (A, k) J) (hl : CappedLift sem h) : CappedLift out h := by
  intro p q γ hp hq hγ hag
  have hI : ¬ GradedLe (A, k) I := fun hi => hJ (hi.trans h)
  let eI := equiv₀ I hI
  let eJ := equiv₀ J hJ
  have hp' : RespectsSemanticsBelow sem I (p ∘ eI) := by
    apply (respects_iff₀ I hI _).mpr
    simpa only [eI, Function.comp_def, Equiv.apply_symm_apply] using hp
  have hq' : RespectsSemanticsBelow sem J (q ∘ eJ) := by
    apply (respects_iff₀ J hJ _).mpr
    simpa only [eJ, Function.comp_def, Equiv.apply_symm_apply] using hq
  obtain ⟨r, hr, hcap, hread⟩ := hl (p ∘ eI) (q ∘ eJ) γ hp' hq' hγ (fun d => hag (eI d))
  refine ⟨r ∘ eJ.symm,
    (respects_iff₀ J hJ r).mp hr, ?_, ?_⟩
  · simp_all
  · intro d
    obtain ⟨e, rfl⟩ := eI.surjective d
    change r (eJ.symm (eJ (CellScheme.below.mono h e))) = p (eI e)
    rw [Equiv.symm_apply_apply]
    exact hread e

