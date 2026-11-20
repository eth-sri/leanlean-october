/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowFrame
public import VaughtConjecture.Knight.LowOnlyPaddedEndpoints

/-! # Exact earlier lower sets inside every later recursive LOW layer

New full-scope owners have strictly larger grades. Thus every earlier lower
set is literally inherited, with a constructed occurrence equivalence and
lawfulness transport. These are row facts, independent of higher lifting.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyPaddedRestriction
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open LowOnlyPaddedContract LowOnlyPaddedIteration
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  (frame : I.LowFrame F)
  (t : ℕ) (ht : t + 2 ≤ A.card) (J : Finset ι × ℕ) (hJ : J.2 ≤ t + 2)

def belowEquiv : (r : ℕ) → (hr : t + r + 2 ≤ A.card) →
    (build frame t ht).carrier.below J ≃
      (build frame (t + r) hr).carrier.below J
  | 0, _ => Equiv.refl _
  | r + 1, hr =>
    (belowEquiv r (by omega)).trans
      (HighLayerBountiful.equiv (build frame (t + r) (by omega)).carrier
        (F.Anchor (t + r + 2 + 1)) (t + r + 2 + 1) (by omega) (by omega) J
        (fun h => by have := h.2; omega))

/-- Pullback of an arbitrary lawful section along the actual occurrence map.
No agreement of independently selected renderings is used. -/
theorem pullback r (hr : t + r + 2 ≤ A.card)
    {q : (build frame (t + r) hr).carrier.below J → ExtOrd}
    (hq : RespectsSemanticsBelow (build frame (t + r) hr).rows J q) :
    RespectsSemanticsBelow (build frame t ht).rows J
      (q ∘ belowEquiv frame t ht J hJ r hr) := by
  induction r with
  | zero => exact hq
  | succ r ih =>
    let P := build frame (t + r) (by omega)
    have hnot : ¬ GradedLe (A, t + r + 2 + 1) J := fun h => by have := h.2; omega
    let e := HighLayerBountiful.equiv P.carrier (F.Anchor (t + r + 2 + 1))
      (t + r + 2 + 1) (by omega) (by omega) J hnot
    have hp : RespectsSemanticsBelow P.rows J (q ∘ e) := by
      apply (HighLayerBountiful.respects_iff P.carrier (F.Anchor (t + r + 2 + 1))
        (t + r + 2 + 1) (by omega) (by omega)
        (P.separated (by omega)) P.rows
        (PaddedTower.Step.rows P (by omega) (by omega))
        (PaddedTower.Step.inherited_row P (by omega) (by omega)) J hnot _).mpr
      change RespectsSemanticsBelow (PaddedTower.Step.rows P (by omega) (by omega))
        J (fun x => q (e (e.symm x)))
      simp only [Equiv.apply_symm_apply]
      exact hq
    exact ih (by omega) hp

/-- A whole lawful section restricts lawfully to every earlier native target. -/
theorem whole_pullback r (hr : t + r + 2 ≤ A.card)
    {q : Cell (build frame (t + r) hr).carrier → ExtOrd}
    (hq : RespectsSemantics (build frame (t + r) hr).rows q) :
    RespectsSemanticsBelow (build frame t ht).rows J
      (fun d => q (belowEquiv frame t ht J hJ r hr d).1) :=
  pullback frame t ht J hJ r hr (hq.toBelow J)

variable {t ht J hJ}

/-- Earlier original occurrences remain the same original occurrences after
transport through all later layers. -/
theorem belowEquiv_original t (ht : t + 2 ≤ A.card) J
    (hJ : J.2 ≤ t + 2) r (hr : t + r + 2 ≤ A.card)
    (d : I.boundary.below J) :
    (belowEquiv frame t ht J hJ r hr
      ⟨LowOnlyPaddedEndpoints.original frame t ht d.1,
        by rw [LowOnlyPaddedEndpoints.original_index]; exact d.2⟩).1 =
      LowOnlyPaddedEndpoints.original frame (t + r) hr d.1 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change PaddedTower.Step.old (build frame (t + r) (by omega))
      (by omega) (belowEquiv frame t ht J hJ r (by omega)
        ⟨LowOnlyPaddedEndpoints.original frame t ht d.1,
          by rw [LowOnlyPaddedEndpoints.original_index]; exact d.2⟩).1 = _
    exact congrArg (PaddedTower.Step.old
      (build frame (t + r) (by omega)) (by omega)) (ih (by omega))

/-- The retained long grade-one base of any constructed layer is lawful on
restriction. Availability is supplied by an actual full-scope base tip. -/
theorem base_pullback {k} (P : Layer frame k)
    {q} (hq : RespectsSemantics P.rows q) :
    RespectsSemanticsBelow (baseRows frame) (A, 1)
      (fun d => q (P.baseMap d.1)) := by
  obtain ⟨a, _⟩ := F.exists_rank_anchor le_rfl (F.zero_admissible 1)
  let c : Cell (base frame) :=
    RelativeLadderLayer.added I.boundary frame.positive (SupportLadderRows.leaf (Nat.succ_pos _) a)
  have hc : (base frame).cell c = (A, 1) :=
    RelativeLadderLayer.added_index I.boundary frame.positive _
  have hp := (P.base_respects c q).mp (hq.toBelow _)
  exact GradeCutLayerRows.cast_respects (base frame)
    (baseRows frame) hc hp

end
end VaughtConjecture.Knight.LowOnlyPaddedRestriction
