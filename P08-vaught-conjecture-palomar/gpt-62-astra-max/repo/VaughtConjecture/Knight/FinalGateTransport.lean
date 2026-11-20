/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FinalGateLayer
public import VaughtConjecture.Knight.HighLayerBountiful
public import VaughtConjecture.Knight.ExactSemanticFace
public import VaughtConjecture.Knight.SingleFaceTailRestoration

/-! # Exact predecessor lifting transport past the final gate layer

Any graded target excluding the new full grade-N index has exactly its old
occurrences and rows. The actual lower-domain equivalence transports arbitrary
local sections and original-cap lifting, not just selected source vectors.
This includes every proper-scope target and every target of grade below N.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FinalGateLayer.Input
open Transform Value ExtOrd CoatomBoundaryExtension
noncomputable section

variable {ι X Q : Type*} [DecidableEq ι] [Fintype Q]
variable {A : Finset ι} {D : CellScheme A} {N : ℕ} (F : Input D N X Q)

/-- Old lifting clauses transport on their actual target-local domains.
No bountifulness of the extended output is assumed. -/
theorem inherited_lift {I J} (h : GradedLe I J)
    (hJ : ¬ GradedLe (A, N) J) (hlift : CappedLift F.sem h) : CappedLift F.rows h :=
  HighLayerBountiful.transport_lift D _ N F.positive F.height F.separated F.sem F.rows F.inherited_row h hJ hlift

/-- The predecessor's lower-grade lift is the restoration clause on the
installed carrier, even when old proper grade-N owners remain present. -/
theorem lower_lift {I J} (h : GradedLe I J) (hJ : J.2 < N)
    (hlift : CappedLift F.sem h) : CappedLift F.rows h :=
  F.inherited_lift h (fun he => not_le_of_gt hJ he.2) hlift

/-- The complementary inactive branch needs no catalogue repair. -/
theorem lift_inactive {S} (hS : S ⊆ A)
    (hlift : CappedLift F.sem
      (show GradedLe (S, N - 1) (A, N - 1) from ⟨hS, le_rfl⟩))
    {p}
    (hp : F.rows.Lawful p)
    {q}
    (hq : F.rows.Lawful q)
    {γ} (hγ : SelfVis N γ)
    (hag : CappedEq (q ∘ CellScheme.below.mono (show GradedLe (S, N) (A, N) from ⟨hS, le_rfl⟩)) p γ)
    (hhigh : ∀ e : F.carrier.below (S, N), F.carrier.grade e.1 = N → p e ≤ γ) :
    ∃ r,
      F.rows.Lawful r ∧
      CappedEq r q γ ∧
      ∀ e, r (CellScheme.below.mono
        (show GradedLe (S, N) (A, N) from ⟨hS, le_rfl⟩) e) = p e := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt F.positive)
  exact SingleFaceTailRestoration.exists_inactive F.rows hS
    (F.inherited_lift (show GradedLe (S, j) (A, j) from ⟨hS, le_rfl⟩) (fun he => not_le_of_gt (Nat.lt_succ_self j) he.2) hlift) hp hq hγ hag hhigh

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

end
end VaughtConjecture.Knight.FinalGateLayer.Input
