
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.FinalGateLayer
import VaughtConjecture.Knight.CoatomBoundaryExtension
import VaughtConjecture.Knight.ExactSemanticFace
import VaughtConjecture.Knight.SingleFaceTailRestoration

/-! # Exact predecessor lifting transport past the final gate layer

Any graded target excluding the new full grade-N index has exactly its old
occurrences and rows. The actual lower-domain equivalence transports arbitrary
local sections and original-cap lifting, not just selected source vectors.
This includes every proper-scope target and every target of grade below N.
-/

namespace VaughtConjecture.Knight.FinalGateLayer.Input
open    CoatomBoundaryExtension
noncomputable section

variable {ι X Q : Type*} [DecidableEq ι] [Fintype Q]
variable {A : Finset ι} {D : CellScheme A} {N : ℕ} (F : Input D N X Q)

local notation "GradedLe₀" => GradedLe (A, N)

/-- All occurrences below a target that excludes the added index are old. -/
def inheritedBelow J (hJ : ¬ GradedLe₀ J) :
    D.below J ≃ F.carrier.below J :=
  Equiv.ofBijective (fun d => ⟨F.old d.1, by rw [F.old_index]; exact d.2⟩) ⟨by
    intro d e he
    exact Subtype.ext (F.old_strictMono.injective (congrArg Subtype.val he)), by
    intro d
    have hn : F.carrier.cell d.1 ≠ (A, N) := fun he => hJ (he ▸ d.2)
    obtain ⟨e, he⟩ := SourceLayerCarrier.old_occurrence D (Node (Q := Q)) N
      F.positive F.height d.1 hn
    have hd  := by simpa only [he, F.old_index] using d.2
    exact ⟨⟨e, hd⟩, Subtype.ext he.symm⟩⟩

theorem inheritedBelow_respects_iff J (hJ : ¬ GradedLe₀ J)
    p :
    RespectsSemanticsBelow F.rows J p ↔
      RespectsSemanticsBelow F.sem J (p ∘ F.inheritedBelow J hJ) := by
  have h := respects_iff_of_equiv (sem' := F.sem) (sem := F.rows)
    (F.inheritedBelow J hJ)
    (fun d => (congrArg Prod.snd (F.old_index d.1)).symm)
    (fun d e => ?_) (fun c d hd => ?_) (p ∘ F.inheritedBelow J hJ)
  · have he : (p ∘ F.inheritedBelow J hJ) ∘ (F.inheritedBelow J hJ).symm = p := by
      aesop
    rw [he] at h
    exact h.symm
  · change D.scope d.1 ⊆ D.scope e.1 ↔
      (F.carrier.cell (F.old d.1)).1 ⊆ (F.carrier.cell (F.old e.1)).1
    rw [F.old_index, F.old_index]
    rfl
  · exact (F.inherited_row c.1 d).symm

/-- Old lifting clauses transport on their actual target-local domains.
No bountifulness of the extended output is assumed. -/
theorem inherited_lift {I J} (h : GradedLe I J)
    (hJ : ¬ GradedLe₀ J) (hlift : CappedLift F.sem h) : CappedLift F.rows h := by
  let hI : ¬ GradedLe₀ I := fun he => hJ (he.trans h)
  let eI := F.inheritedBelow I hI
  let eJ := F.inheritedBelow J hJ
  have hm (d : D.below I) :
      eJ (CellScheme.below.mono h d) = CellScheme.below.mono h (eI d) := rfl
  intro p q γ hp hq hγ hag
  obtain ⟨r, hr, hcaps, hread⟩ := hlift (p ∘ eI) (q ∘ eJ) γ
    ((F.inheritedBelow_respects_iff I hI p).mp hp)
    ((F.inheritedBelow_respects_iff J hJ q).mp hq) hγ (fun d => hag (eI d))
  refine ⟨r ∘ eJ.symm, ?_, ?_, ?_⟩
  · apply (F.inheritedBelow_respects_iff J hJ _).mpr
    have he : (r ∘ eJ.symm) ∘ eJ = r := by
      aesop
    exact he.symm ▸ hr
  · simp_all
  · intro d
    have he : eJ.symm (CellScheme.below.mono h d) =
        CellScheme.below.mono h (eI.symm d) := by
      grind
    rw [Function.comp_apply, he, hread]
    exact congrArg p (eI.apply_symm_apply d)

/-- The predecessor's lower-grade lift is the restoration clause on the
installed carrier, even when old proper grade-N owners remain present. -/
def lower_lift {I J} (h : GradedLe I J) (hJ : J.2 < N)
    (hlift : CappedLift F.sem h) :=
  F.inherited_lift h (fun he => not_le_of_gt hJ he.2) hlift

local notation "RespectsSemanticsBelow₀" => RespectsSemanticsBelow F.rows (A, N)

/-- Literal restoration above an owner cap on the installed rows. Only the
predecessor's lower-grade lifting clause is consumed. -/
theorem restore {S} (hS : S ⊆ A)
    (hlift : CappedLift F.sem
      (show GradedLe (S, N - 1) (A, N - 1) from ⟨hS, le_rfl⟩))
    {p}
    (hp : RespectsSemanticsBelow F.rows (S, N) p)
    {u}
    (hu : RespectsSemanticsBelow₀ u)
    {M} (hM : SelfVis N M)
    (hread : ∀ e, u (CellScheme.below.mono
      (show GradedLe (S, N) (A, N) from ⟨hS, le_rfl⟩) e) = min (p e) M)
    (hhigh : ∀ e , F.carrier.grade e.1 = N → p e ≤ M) :
    ∃ r ,
      RespectsSemanticsBelow₀ r ∧
      (∀ e, r (CellScheme.below.mono
        (show GradedLe (S, N) (A, N) from ⟨hS, le_rfl⟩) e) = p e) ∧
      (CappedEq r u M) ∧
      ∀ d, N - 1 < F.carrier.grade d.1 → r d ≤ M := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt F.positive)
  exact SingleFaceTailRestoration.exists_restore F.rows hS
    (F.lower_lift (show GradedLe (S, j) (A, j) from ⟨hS, le_rfl⟩)
      (Nat.lt_succ_self j) hlift) hp hu hM hread hhigh

/-- The complementary inactive branch needs no catalogue repair. -/
theorem lift_inactive {S} (hS : S ⊆ A)
    (hlift : CappedLift F.sem
      (show GradedLe (S, N - 1) (A, N - 1) from ⟨hS, le_rfl⟩))
    {p}
    (hp : RespectsSemanticsBelow F.rows (S, N) p)
    {q}
    (hq : RespectsSemanticsBelow₀ q)
    {γ} (hγ : SelfVis N γ)
    (hag : ∀ e, min (q (CellScheme.below.mono
      (show GradedLe (S, N) (A, N) from ⟨hS, le_rfl⟩) e)) γ = min (p e) γ)
    (hhigh : ∀ e , F.carrier.grade e.1 = N → p e ≤ γ) :
    ∃ r ,
      RespectsSemanticsBelow₀ r ∧
      (CappedEq r q γ) ∧
      ∀ e, r (CellScheme.below.mono
        (show GradedLe (S, N) (A, N) from ⟨hS, le_rfl⟩) e) = p e := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt F.positive)
  exact SingleFaceTailRestoration.exists_inactive F.rows hS
    (F.lower_lift (show GradedLe (S, j) (A, j) from ⟨hS, le_rfl⟩)
      (Nat.lt_succ_self j) hlift) hp hq hγ hag hhigh

/-- A proper original semantic face stays occurrence-exact after the final
installation, with its full lower domains and long rows unchanged. -/
def inheritedFace {S} {D₀ : CellScheme S} {sem₀ : Semantics D₀}
    (hS : S ⊆ A) (hne : S ≠ A) (E : ExactSemanticFace sem₀ F.sem) :
    ExactSemanticFace sem₀ F.rows where
  map := ⟨F.old ∘ E.map, F.old_strictMono.injective.comp E.map.injective⟩
  index d := (F.old_index (E.map d)).trans (E.index d)
  exhaustive z hz := by
    obtain ⟨d, hd⟩ := F.proper_occurrence hS hne
      (⟨z, hz, le_rfl⟩ : F.carrier.below (S, F.carrier.grade z))
    obtain ⟨e, he⟩ := E.exhaustive d.1 d.2.1
    exact ⟨e, (congrArg F.old he).trans hd.symm⟩
  row c d := (F.inherited_row (E.map c) (E.belowMap c d)).trans (E.row c d)

