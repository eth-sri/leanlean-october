/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FinalGateLayer
public import VaughtConjecture.Knight.CoatomBoundaryExtension
public import VaughtConjecture.Knight.ExactSemanticFace
public import VaughtConjecture.Knight.SingleFaceTailRestoration

@[expose] public section

namespace VaughtConjecture.Knight.FinalGateLayer.Input

open Transform Value ExtOrd CoatomBoundaryExtension

noncomputable section

variable {ι X Q : Type*} [DecidableEq ι] [Fintype Q]

variable {A : Finset ι} {D : CellScheme A} {N : ℕ} (F : Input D N X Q)

/-- All occurrences below a target that excludes the added index are old. -/
def inheritedBelow (J : Finset ι × ℕ) (hJ : ¬ GradedLe (A, N) J) :
    D.below J ≃ F.carrier.below J :=
  SourceLayerCarrier.inheritedEquiv D (Node (Q := Q)) N F.pos F.height J hJ

theorem inheritedBelow_respects_iff (J : Finset ι × ℕ) (hJ : ¬ GradedLe (A, N) J)
    (p : D.below J → ExtOrd) :
    RespectsSemanticsBelow F.sem J p ↔
      RespectsSemanticsBelow F.rows J (p ∘ (F.inheritedBelow J hJ).symm) :=
  respects_iff_of_index_equiv (F.inheritedBelow J hJ)
    (fun d => F.old_index d.1) (fun c d _ => (F.inherited_row c.1 d).symm) p

/-- Old lifting clauses transport on their actual target-local domains.
No bountifulness of the extended output is assumed. -/
theorem inherited_lift {I J : Finset ι × ℕ} (h : GradedLe I J)
    (hJ : ¬ GradedLe (A, N) J) (hlift : CappedLift F.sem h) : CappedLift F.rows h := by
  let hI : ¬ GradedLe (A, N) I := fun he => hJ (he.trans h)
  exact CappedLift.of_equiv (F.inheritedBelow I hI) (F.inheritedBelow J hJ)
    (fun _ => rfl) le_rfl (F.inheritedBelow_respects_iff I hI)
    (F.inheritedBelow_respects_iff J hJ) hlift

/-- The predecessor's lower-grade lift is the restoration clause on the
installed carrier, even when old proper grade-N owners remain present. -/
theorem lower_lift {I J : Finset ι × ℕ} (h : GradedLe I J) (hJ : J.2 < N)
    (hlift : CappedLift F.sem h) : CappedLift F.rows h :=
  F.inherited_lift h (fun he => not_le_of_gt hJ he.2) hlift

/-- A proper original semantic face stays occurrence-exact after the final
installation, with its full lower domains and long rows unchanged. -/
def inheritedFace {S : Finset ι} {D₀ : CellScheme S} {sem₀ : Semantics D₀}
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

end

end VaughtConjecture.Knight.FinalGateLayer.Input
