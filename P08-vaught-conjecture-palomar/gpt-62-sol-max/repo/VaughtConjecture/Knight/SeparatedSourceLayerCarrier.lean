/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourceLayerCarrier
public import VaughtConjecture.Knight.SemanticPatch

@[expose] public section

namespace VaughtConjecture.Knight.SeparatedSourceLayerCarrier

open AmalgamationPlan Transform Value ExtOrd SourceLayerCarrier

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}

variable (D : CellScheme A) (Q : Type*) [Fintype Q] (k : ℕ)

variable (hk : 0 < k) (hA : k ≤ A.card)

theorem separated_of_proper (hp : ∀ d : Cell D, D.scope d ≠ A) :
    ∀ d : Cell D, ¬ GradedLe (A, k) (D.cell d) := by
  intro d hd
  exact hp d (Finset.Subset.antisymm
    (D.scope_subset d) hd.1)

variable (hseparated : ∀ d : Cell D, ¬ GradedLe (A, k) (D.cell d))

omit [Fintype Q] in
include hseparated in
theorem below_old (x : Cell D ⊕ Q) (c : Cell D)
    (h : GradedLe (index D Q k x) (D.cell c)) :
    ∃ d : D.below (D.cell c), x = .inl d.1 := by
  cases x with
  | inl d => tauto
  | inr q => tauto

noncomputable def patch : SemanticPatch D (scheme D Q k hk hA) where
  map := ⟨fun d => toCell D Q k hk hA (.inl d), (old_order D Q k hk hA).injective⟩
  index d := cell_toCell D Q k hk hA (.inl d)
  closed c e he := by
    obtain ⟨d, hd⟩ := old_occurrence D Q k hk hA e (fun h => hseparated c (h ▸ he))
    exact ⟨d, hd.symm⟩

noncomputable def ownerEquiv (c : Cell D) : D.below (D.cell c) ≃
    (scheme D Q k hk hA).below ((scheme D Q k hk hA).cell (toCell D Q k hk hA (.inl c))) :=
  (patch D Q k hk hA hseparated).ownerEquiv c

theorem ownerEquiv_val (c : Cell D) (d : D.below (D.cell c)) :
    (ownerEquiv D Q k hk hA hseparated c d).1 = toCell D Q k hk hA (.inl d.1) := rfl

include hseparated in
theorem old_not_full (d : Cell D) :
    (scheme D Q k hk hA).cell (toCell D Q k hk hA (.inl d)) ≠ (A, k) := by
  rw [cell_toCell]
  exact fun he => hseparated d (he.symm ▸ GradedLe.refl (A, k))

noncomputable def controller (q : Q) :
    SourcePrefixLayer.Controller (scheme D Q k hk hA) k :=
  ⟨toCell D Q k hk hA (.inr q), cell_toCell D Q k hk hA (.inr q)⟩

noncomputable def controllerEquiv : Q ≃ SourcePrefixLayer.Controller (scheme D Q k hk hA) k :=
  Equiv.ofBijective (controller D Q k hk hA) ⟨by
    intro p q hpq
    exact Sum.inr.inj ((enumeration D Q k hk hA).injective (congrArg Subtype.val hpq)), by
    intro c
    have hc := c.2
    rw [cell_eq] at hc
    cases he : toOcc D Q k hk hA c.1 with
    | inl d =>
      rw [he] at hc
      exact False.elim (hseparated d (hc.symm ▸ GradedLe.refl (A, k)))
    | inr q =>
      refine ⟨q, Subtype.ext ?_⟩
      change toCell D Q k hk hA (.inr q) = c.1
      rw [← he, toCell_toOcc]⟩

variable (sem : Semantics D)

noncomputable def oldTable : (Cell D ⊕ Q) → (Cell D ⊕ Q) → ExtOrd
  | .inl c, .inl d => AmalgamatedBoundaryRows.total sem c d
  | _, _ => ⊥

omit [Fintype Q] in
include hseparated in
theorem oldTable_visible (c d : Cell D ⊕ Q) (h : GradedLe (index D Q k d) (index D Q k c)) :
    SelfVis (index D Q k d).2 (oldTable D Q sem c d) := by
  cases c with
  | inl c =>
    obtain ⟨e, rfl⟩ := below_old D Q k hseparated d c h
    change SelfVis (D.grade e.1) (AmalgamatedBoundaryRows.total sem c e.1)
    rw [AmalgamatedBoundaryRows.total_below]
    exact (sem.orderly c e).symm
  | inr q => cases d <;> exact selfVis_bot _

noncomputable def base : Semantics (scheme D Q k hk hA) where
  E c d := oldTable D Q sem (toOcc D Q k hk hA c) (toOcc D Q k hk hA d.1)
  orderly c d := by
    have h : GradedLe (index D Q k (toOcc D Q k hk hA d.1))
        (index D Q k (toOcc D Q k hk hA c)) := by
      simpa [← cell_eq] using d.2
    have hv := oldTable_visible D Q k hseparated sem _ _ h
    change oldTable D Q sem (toOcc D Q k hk hA c) (toOcc D Q k hk hA d.1) =
      extVisibilityReplace (oldTable D Q sem (toOcc D Q k hk hA c) (toOcc D Q k hk hA d.1))
        ((scheme D Q k hk hA).cell d.1).2 ((scheme D Q k hk hA).cell d.1).2
    simpa only [cell_eq] using hv.symm

theorem base_old (c : Cell D) (d : D.below (D.cell c)) :
    (base D Q k hk hA hseparated sem).E (toCell D Q k hk hA (.inl c))
      (ownerEquiv D Q k hk hA hseparated c d) = sem.E c d := by
  change oldTable D Q sem (toOcc D Q k hk hA (toCell D Q k hk hA (.inl c)))
    (toOcc D Q k hk hA (ownerEquiv D Q k hk hA hseparated c d).1) = _
  rw [ownerEquiv_val, toOcc_toCell, toOcc_toCell]
  exact AmalgamatedBoundaryRows.total_below sem c d

theorem base_respects_iff (c : Cell D)
    (p : (scheme D Q k hk hA).below
      ((scheme D Q k hk hA).cell (toCell D Q k hk hA (.inl c))) → ExtOrd) :
    RespectsSemanticsBelow (base D Q k hk hA hseparated sem) _ p ↔
      RespectsSemanticsBelow sem (D.cell c) (p ∘ ownerEquiv D Q k hk hA hseparated c) :=
  (patch D Q k hk hA hseparated).owner_respects_iff (base_old D Q k hk hA hseparated sem) c p

variable {sem} {out : Semantics (scheme D Q k hk hA)}
  (hrow : (patch D Q k hk hA hseparated).Preserves sem out)

include hrow in
theorem respects_iff (J : Finset ι × ℕ) (hJ : ¬ GradedLe (A, k) J) (p : D.below J → ExtOrd) :
    RespectsSemanticsBelow sem J p ↔ RespectsSemanticsBelow out J
      (p ∘ (inheritedEquiv D Q k hk hA J hJ).symm) :=
  respects_iff_of_index_equiv (inheritedEquiv D Q k hk hA J hJ)
    (inheritedEquiv_cell D Q k hk hA J hJ) (fun c d _ => (hrow c.1 d).symm) p

include hrow in
theorem pullback_respects {J : Finset ι × ℕ} (hJ : ¬ GradedLe (A, k) J)
    {q : (scheme D Q k hk hA).below J → ExtOrd} (hq : RespectsSemanticsBelow out J q) :
    RespectsSemanticsBelow sem J (q ∘ inheritedEquiv D Q k hk hA J hJ) :=
  (iff_comp_symm (inheritedEquiv D Q k hk hA J hJ).symm
    (respects_iff D Q k hk hA hseparated hrow J hJ) q).mp hq

open CoatomBoundaryExtension in
include hrow in
theorem lift {I J : Finset ι × ℕ} (h : GradedLe I J) (hJ : ¬ GradedLe (A, k) J)
    (hl : CappedLift sem h) : CappedLift out h :=
  (patch D Q k hk hA hseparated).lift hrow h (fun d hd => by
    obtain ⟨c, hc⟩ := old_occurrence D Q k hk hA d (fun he => hJ (he ▸ hd))
    exact ⟨c, hc.symm⟩) hl

end VaughtConjecture.Knight.SeparatedSourceLayerCarrier
