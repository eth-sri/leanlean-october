/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrderedScopeSections

/-! # Lifting and owner classification after scope installation

Previously completed targets keep their complete lower domains. The new scope
uses the local operator's proved bountifulness. No bountifulness of the ambient
partial carrier is assumed. These are the per-step receipts for scope iteration,
not a claim that every scope has already been completed.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.OrderedScopeRelocation
open AmalgamationPlan Transform Value ExtOrd CoatomBoundaryExtension

variable {ι : Type*} [DecidableEq ι] {A B : Finset ι}
  {D : CellScheme A} (sem : Semantics D) (hB : B ∈ D.plan) {k : ℕ}
  (S : OrdinaryScopeOperator.Core (ScopeBoundary.rows D B hB sem) k)
  (hsep : Separated (D := D) (B := B))
local notation "K" => carrier sem hB S
local notation "l" => old sem hB S
local notation "r" => localCell sem hB S

/-- All earlier targets not containing this new scope are literally unchanged. -/
def oldLower (J : Finset ι × ℕ) (hJ : ¬ B ⊆ J.1) : D.below J ≃ (K).below J :=
  Equiv.ofBijective (fun d => ⟨l d.1, by rw [old_index]; exact d.2⟩) ⟨by
    intro d e h
    exact Subtype.ext ((old_order sem hB S).injective (congrArg Subtype.val h)), by
    intro z
    rcases classify sem hB S z.1 with ⟨d, hd⟩ | hd
    · refine ⟨⟨d, ?_⟩, Subtype.ext hd⟩
      simpa only [← hd, old_index] using z.2
    · exact False.elim (hJ (hd ▸ z.2.1))⟩

theorem oldLower_respects (J : Finset ι × ℕ) (hJ : ¬ B ⊆ J.1)
    (p : D.below J → ExtOrd) :
    RespectsSemanticsBelow sem J p ↔
      RespectsSemanticsBelow (rows sem hB S hsep) J (p ∘ (oldLower sem hB S J hJ).symm) :=
  respects_iff_of_equiv (oldLower sem hB S J hJ)
    (fun d => (congrArg Prod.snd (old_index sem hB S d.1)).symm)
    (fun d e => by
      change D.scope d.1 ⊆ D.scope e.1 ↔ ((K).cell (l d.1)).1 ⊆ ((K).cell (l e.1)).1
      rw [old_index, old_index]; rfl)
    (fun c d _ => (row_old sem hB S hsep c.1 d).symm) p

theorem old_lift {I J : Finset ι × ℕ} (h : GradedLe I J) (hJ : ¬ B ⊆ J.1)
    (hb : CappedLift sem h) : CappedLift (rows sem hB S hsep) h :=
  have hI : ¬ B ⊆ I.1 := fun hi => hJ (hi.trans h.1)
  hb.of_respects_iff (oldLower sem hB S I hI) (oldLower sem hB S J hJ) (fun _ => rfl)
    (oldLower_respects sem hB S hsep I hI) (oldLower_respects sem hB S hsep J hJ)

theorem local_lift {I J : Finset ι × ℕ} (h : GradedLe I J)
    (hI : I ∈ Plan.gradedPlan D.plan) (hJ : J ∈ Plan.gradedPlan D.plan) (hJB : J.1 ⊆ B) :
    CappedLift (rows sem hB S hsep) h := by
  by_cases he : I = J
  · subst J; exact lift_refl
  · have memLocal : ∀ T ∈ Plan.gradedPlan D.plan, T.1 ⊆ B →
        T ∈ Plan.gradedPlan S.carrier.plan := by
      intro T hT hTB
      obtain ⟨hp, hg, hc⟩ := Plan.mem_gradedPlan.mp hT
      rw [S.plan]
      exact Plan.mem_gradedPlan.mpr
        ⟨Finset.mem_inter.mpr ⟨hp, Finset.mem_powerset.mpr hTB⟩, hg, hc⟩
    exact (localFace sem hB S hsep).lift hJB (memLocal I hI (h.1.trans hJB))
      (memLocal J hJ hJB) h he S.bountiful

/-- The selected-display decoder needs this alternative, not global shortness. -/
def OwnerClassification {X : Type*} (original : X → Cell D) : Prop :=
  ∀ c : Cell D, (∀ d, SharpWitnessComposition.Short (D.grade c) (sem.E c d)) ∨
    ∀ d : D.below (D.cell c), ∃ x, original x = d.1

theorem ownerClassification {X : Type*} (original : X → Cell D)
    (hc : OwnerClassification sem original) :
    OwnerClassification (rows sem hB S hsep) (l ∘ original) := by
  intro z
  rcases classify sem hB S z with ⟨c, rfl⟩ | hz
  · rcases hc c with hshort | horiginal
    · left
      intro d
      obtain ⟨e, rfl⟩ := (oldBelow sem hB S hsep c).surjective d
      change SharpWitnessComposition.Short ((K).cell (l c)).2
        ((rows sem hB S hsep).E (l c) _)
      rw [row_old, old_index]
      exact hshort e
    · right
      intro d
      obtain ⟨e, rfl⟩ := (oldBelow sem hB S hsep c).surjective d
      obtain ⟨x, hx⟩ := horiginal e
      exact ⟨x, congrArg l hx⟩
  · obtain ⟨c, rfl⟩ := local_exhaustive sem hB S z (subset_of_eq hz)
    have hc : S.carrier.scope c = B := by
      simpa only [CellScheme.scope, local_index] using hz
    left
    intro d
    obtain ⟨e, rfl⟩ := (localBelow sem hB S c).surjective d
    change SharpWitnessComposition.Short ((K).cell (r c)).2
      ((rows sem hB S hsep).E (r c) _)
    rw [row_local, local_index]
    exact S.short c hc e

/-- The initial inventory is itself the original-field inventory, regardless
of the lengths of any of its rows. -/
theorem ownerClassification_initial : OwnerClassification sem (id : Cell D → Cell D) :=
  fun _ => Or.inr (fun d => ⟨d.1, rfl⟩)
