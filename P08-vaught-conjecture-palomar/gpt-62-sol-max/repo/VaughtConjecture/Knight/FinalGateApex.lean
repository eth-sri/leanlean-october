/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FinalGateCompletion
public import VaughtConjecture.Knight.FinalGateTransport
public import VaughtConjecture.Knight.MaximalFullLayer
public import VaughtConjecture.Knight.SeparatedLayerFace
public import VaughtConjecture.Knight.FullScopeZeroExtension

@[expose] public section

namespace VaughtConjecture.Knight.FinalGateApex

open Transform Value ExtOrd AmalgamationPlan

noncomputable section

variable {ι X Q : Type*} [DecidableEq ι] [Fintype Q]

variable {A : Finset ι} {D : CellScheme A} {N : ℕ}

variable (F : FinalGateLayer.Input D N X Q)

variable (hD : ∀ d : Cell D, D.grade d ≤ N) (hcard : A.card = N + 1)

abbrev scheme := MaximalFullLayer.scheme F.carrier N (N + 1) (Nat.lt_succ_self N) hcard.ge

abbrev old := MaximalFullLayer.old F.carrier N (N + 1) (Nat.lt_succ_self N) hcard.ge

abbrev apex := MaximalFullLayer.apex F.carrier N (N + 1) (Nat.lt_succ_self N) hcard.ge

abbrev rows := MaximalFullLayer.base F.carrier F.rows N (N + 1) (F.grade_bound hD)
  (Nat.lt_succ_self N) hcard.ge

abbrev ownerEquiv := MaximalFullLayer.ownerEquiv F.carrier N (N + 1) (F.grade_bound hD)
  (Nat.lt_succ_self N) hcard.ge

theorem old_index (d : Cell F.carrier) : (scheme F hcard).cell (old F hcard d) =
    F.carrier.cell d := MaximalFullLayer.old_index _ _ _ _ _ _

theorem apex_index : (scheme F hcard).cell (apex F hcard) = (A, N + 1) :=
  MaximalFullLayer.apex_index _ _ _ _ _

theorem old_row (c : Cell F.carrier) (d : F.carrier.below (F.carrier.cell c)) :
    (rows F hD hcard).E (old F hcard c) (ownerEquiv F hD hcard c d) = F.rows.E c d :=
  MaximalFullLayer.inherited_row _ _ _ _ _ _ _ c d

theorem complete (seed : Q)
    (hc : ∀ J ∈ Plan.gradedPlan D.plan, J.2 ≤ N → J ≠ (A, N) → ∃ d, D.cell d = J) :
    (scheme F hcard).IsComplete := by
  apply MaximalFullLayer.complete F.carrier N (N + 1) (Nat.lt_succ_self N) hcard.ge
  intro J hJ hne
  apply F.complete_through seed hc J hJ
  obtain ⟨hmem, _, hj⟩ := Plan.mem_gradedPlan.mp hJ
  have hs := F.carrier.isPlan.subset_of_mem hmem
  have hc' := Finset.card_le_card hs
  by_contra hn
  have hsz : J.1.card = A.card := by lia
  have he : J.1 = A := Finset.eq_of_subset_of_card_le hs hsz.ge
  grind

theorem consistent (hc : F.sem.IsConsistent) : (rows F hD hcard).IsConsistent :=
  MaximalFullLayer.consistent _ _ _ _ _ _ _ (F.consistent hc)

theorem coded (hc : F.rows.IsCoded) : (rows F hD hcard).IsCoded :=
  MaximalFullLayer.coded _ _ _ _ _ _ _ hc

/-- The final-layer pair theorem is consumed here, not assumed in a scope
operator or hidden in the selected display. -/
theorem bountiful (hb : F.rows.IsBountiful) : (rows F hD hcard).IsBountiful :=
  MaximalFullLayer.bountiful _ _ _ _ _ _ _ F.pos hb

abbrev lowerEquiv : F.carrier.below (A, N) ≃ (scheme F hcard).below (A, N) :=
  SourceLayerCarrier.inheritedEquiv F.carrier Unit (N + 1) (by omega) hcard.ge (A, N)
    (fun h => (Nat.not_succ_le_self N) h.2)

def display (p : F.carrier.below (A, N) → ExtOrd) : Cell (scheme F hcard) → ExtOrd :=
  CellScheme.zeroAbove (p ∘ (lowerEquiv F hcard).symm)

theorem display_old (p : F.carrier.below (A, N) → ExtOrd) (d : F.carrier.below (A, N)) :
    display F hcard p (old F hcard d.1) = p d := by
  change CellScheme.zeroAbove (p ∘ (lowerEquiv F hcard).symm)
    ((lowerEquiv F hcard) d).1 = p d
  rw [CellScheme.zeroAbove_low]
  aesop

theorem display_apex (p : F.carrier.below (A, N) → ExtOrd) :
    display F hcard p (apex F hcard) = ⊥ := by
  apply CellScheme.zeroAbove_high
  change ¬ ((scheme F hcard).cell (apex F hcard)).2 ≤ N
  rw [apex_index]
  exact Nat.not_succ_le_self N

theorem display_lawful {p : F.carrier.below (A, N) → ExtOrd}
    (hp : RespectsSemanticsBelow F.rows (A, N) p) :
    RespectsSemantics (rows F hD hcard) (display F hcard p) := by
  apply RespectsSemanticsBelow.zeroAbove
  exact (SeparatedSourceLayerCarrier.respects_iff F.carrier Unit (N + 1) (by omega) hcard.ge
    (HighLayerBountiful.separated F.carrier (N + 1) N (F.grade_bound hD) (Nat.lt_succ_self N))
    (old_row F hD hcard) (A, N) (fun h => (Nat.not_succ_le_self N) h.2) p).mp hp

/-- Any lawful whole section restricts to the actual final active layer.
This applies to arbitrary ambients, not only constructed displays. -/
theorem restrict_lawful {q : Cell (scheme F hcard) → ExtOrd}
    (hq : RespectsSemantics (rows F hD hcard) q) :
    RespectsSemanticsBelow F.rows (A, N) (fun d => q (old F hcard d.1)) := by
  exact SeparatedSourceLayerCarrier.pullback_respects F.carrier Unit (N + 1) (by omega) hcard.ge
    (HighLayerBountiful.separated F.carrier (N + 1) N (F.grade_bound hD) (Nat.lt_succ_self N))
    (old_row F hD hcard) (fun h => (Nat.not_succ_le_self N) h.2) (hq.toBelow (A, N))

/-- Any proper original face survives the apex with every row and occurrence. -/
def properFace {S : Finset ι} {D₀ : CellScheme S} {sem₀ : Semantics D₀}
    (hS : ¬ A ⊆ S) (E : ExactSemanticFace sem₀ F.rows) :
    ExactSemanticFace sem₀ (rows F hD hcard) :=
  SeparatedLayerFace.face F.carrier Unit (N + 1) (by omega) hcard.ge
    (HighLayerBountiful.separated F.carrier (N + 1) N (F.grade_bound hD) (Nat.lt_succ_self N))
    F.rows (rows F hD hcard) (old_row F hD hcard) E hS

end

end VaughtConjecture.Knight.FinalGateApex
