/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowFrame
public import VaughtConjecture.Knight.LowOnlyPaddedSelectedChart
public import VaughtConjecture.Knight.PaddedTowerChart
public import VaughtConjecture.Knight.LowSeparatorPaired
public import VaughtConjecture.Knight.LowOnlyPaddedRankReadback

/-! # Simultaneous paired separators in whole LOW displays

The displayed negative leaf is the rounded non-top donor maximum and the
positive leaf is top. Both readings use the same composed numerical native
chart. This is a whole lawful, supported display, not a model occurrence.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyPaddedSelectedPair
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open LowOnlyPaddedContract LowOnlyPaddedIteration LowOnlyPaddedEndpoints
open LowOnlyPaddedRestriction LowOnlyPaddedRenderChart LowOnlyPaddedSelectedChart
open SourcePrefixRows SharpWitnessComposition PairedSlotComparison
noncomputable section

section Scalar
variable {X : Type*} [Fintype X] (N : X → Prop) [DecidablePred N]

theorem map_donorMax {k : ℕ} {σ : ExtOrd → ExtOrd} (hσ : BoundedMap k σ)
    {a s : X → ExtOrd} (hf : ∀ f, σ (a f) = s f) :
    σ (LowSeparator.donorMax N a) = LowSeparator.donorMax N s := by
  apply le_antisymm
  · rcases LowSeparator.donorMax_cases N a with hz | ⟨d, hd, he⟩
    · rw [hz, hσ.bot]
      exact bot_le
    · rw [← he, hf]
      exact LowSeparator.le_donorMax N s hd
  · apply LowSeparator.donorMax_le
    intro d hd
    rw [← hf]
    exact hσ.mono (LowSeparator.le_donorMax N a hd)

theorem map_cutoffCut {k : ℕ} {σ : ExtOrd → ExtOrd} (hσ : BoundedMap k σ)
    {a s : X → ExtOrd} (hf : ∀ f, σ (a f) = s f) :
    σ (LowSeparator.cutoffCut k N a) = LowSeparator.cutoffCut k N s := by
  unfold LowSeparator.cutoffCut
  rw [hσ.comm _ k k le_rfl le_rfl, map_donorMax N hσ hf]
end Scalar

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  (frame : I.LowFrame F)
  (hroot : I.RootAgreement F) (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

def leafAt (t : ℕ) (ht : t+2 ≤ A.card) (a : F.Anchor (t+2)) : (build frame t ht).carrier.below (A,t+2) :=
  let c := PaddedTower.Step.controller (before frame t (by omega)) ht a
  ⟨c.1, by change GradedLe ((PaddedTower.Step.carrier (before frame t (by omega)) ht).cell c.1) _; rw [c.2]; exact GradedLe.refl _⟩

theorem source_leaf (t : ℕ) (ht : t + 2 ≤ A.card) (a b : F.Anchor (t + 2)) :
    nativeSource frame t ht a (leafAt frame t ht b).1 =
      cut (LowSeparator.grid (X := Field I.left I.right) (t + 2)) a.val b.val := by
  exact PaddedTower.Step.source_new _ _ _ a b

theorem source_self (t : ℕ) (ht : t + 2 ≤ A.card) (a : F.Anchor (t + 2)) :
    nativeSource frame t ht a (leafAt frame t ht a).1 =
      CanonicalFieldLayer.ceiling (t + 2) (Field I.left I.right) := by
  rw [source_leaf]
  exact cut_refl (sourceGrid_endpoint le_rfl)
    (fun z hz => CanonicalFieldLayer.grid_bound (t + 2) (Field I.left I.right) hz) a.val

def partner (t : ℕ) (ht : K = t + 2) (a : F.Anchor K)
    (hlt : LowSeparator.cutoffCut K (LowSeparator.donorField F) (state F a).profile <
      (state F a).b) : F.Anchor K :=
  ⟨(LowSeparator.partnerState F (state F a)).profile,
    by
      rw [LowSeparator.partnerState_profile]
      exact LowSeparator.partner_mem K (LowSeparator.donorField F) LowSeparator.cutoffField (by rw [state_profile]; exact a.property.1),
    LowSeparator.partnerState F (state F a),
    LowSeparator.partnerState_admissible F (state_admissible F a) hlt (by omega), rfl⟩

variable {frame}

variable (F) in
/-- Native grades at least two have a simultaneous selected pair on the
whole carrier, with all original fields and stage support retained. -/
theorem exists_whole_pair (t : ℕ) (F : LowOnly.Family I.left I.right (t + 2))
    (hroot : I.RootAgreement F)
    (ht : t + 2 ≤ A.card) (r : ℕ) (hr : t + r + 2 ≤ A.card)
    (hfull : t + r + 2 = A.card)
    {S : State I.left I.right} (hS : F.Admissible (t + r + 2) S)
    (htop : ∃ f, S.profile f = ⊤)
    (hactive : LowSeparator.cutoffCut (t + 2) (LowSeparator.donorField F) S.profile < S.b) :
    ∃ w : Cell (build (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) (t + r) hr).carrier → ExtOrd,
      RespectsSemantics (build (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) (t + r) hr).rows w ∧
      (∀ d, w (original (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) (t + r) hr d) = S.profile (field I d)) ∧
      (∀ d, OrbitPrefixSupport.Supported (t + r + 2) {⊤} S.profile (w d)) ∧
      ∃ a : F.Anchor (t + 2), ∃ hlt :
          LowSeparator.cutoffCut (t + 2) (LowSeparator.donorField F) (state F a).profile <
            (state F a).b,
        w (belowEquiv (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht (A, t + 2) le_rfl r hr
          (leafAt (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht a)).1 = ⊤ ∧
        w (belowEquiv (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht (A, t + 2) le_rfl r hr
          (leafAt (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht (partner t rfl a hlt))).1 =
            LowSeparator.cutoffCut (t + 2) (LowSeparator.donorField F) S.profile := by
  obtain ⟨w, hw, ho, hsupp, a, σ, hσ, hf, hc, hd⟩ :=
    exists_whole_chart (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht r hr hfull hS htop
  have hf' (f) : σ ((state F a).profile f) = S.profile f := by
    rw [state_profile]
    exact hf f
  have hcut := map_cutoffCut (LowSeparator.donorField F) hσ hf'
  have hb := hf' LowSeparator.cutoffField
  have hlt : LowSeparator.cutoffCut (t + 2) (LowSeparator.donorField F)
      (state F a).profile < (state F a).b := by
    apply lt_of_not_ge
    intro h
    exact (not_le_of_gt hactive) ((hb.symm.trans_le (hσ.mono h)).trans_eq hcut)
  refine ⟨w, hw, ho, hsupp, a, hlt, ?_, ?_⟩
  · exact (hd (leafAt (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht a)).trans
      ((congrArg σ (source_self (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht a)).trans hc)
  · refine (hd (leafAt (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht (partner t rfl a hlt))).trans ?_
    rw [source_leaf]
    change σ (cut (LowSeparator.grid (t + 2)) a.val
      (LowSeparator.partnerState F (state F a)).profile) = _
    rw [← show (state F a).profile = a.val from state_profile F a,
      LowSeparator.partnerState_profile,
      LowSeparator.cut_partner (t + 2) (LowSeparator.donorField F) LowSeparator.cutoffField
        (by rw [state_profile]; exact a.property.1) hlt]
    exact hcut

variable (F) in
/-- The separate grade-one mechanism survives terminal collapse and every
later layer as well: use rank partners, not paired-slot source cuts. -/
theorem exists_whole_rank_pair (F : LowOnly.Family I.left I.right 1)
    (hroot : I.RootAgreement F)
    (t : ℕ) (ht : t + 2 ≤ A.card) (hfull : t + 2 = A.card)
    {S : State I.left I.right} (hS : F.Admissible (t + 2) S)
    (htop : ∃ f, S.profile f = ⊤)
    (hactive : LowSeparator.donorMax (LowSeparator.donorField F) S.profile < S.b) :
    ∃ w : Cell (build (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht).carrier → ExtOrd,
      RespectsSemantics (build (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht).rows w ∧
      (∀ d, w (original (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht d) = S.profile (field I d)) ∧
      (∀ d, OrbitPrefixSupport.Supported (t + 2) {⊤} S.profile (w d)) ∧
      ∃ T : State I.left I.right, F.Admissible 1 T ∧
        LowSeparator.donorMax (LowSeparator.donorField F) T.profile < T.b ∧
        ∃ qs qt : F.Anchor 1,
          RelativeLadderLayer.ranks (F.fields 1) qs = LadderScalarRendering.fieldRank T.profile ∧
          RelativeLadderLayer.ranks (F.fields 1) qt = LadderScalarRendering.fieldRank
            (LowSeparatorRank.rankPartner (LowSeparator.donorField F)
              LowSeparator.cutoffField T.profile) ∧
          w ((build (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht).baseMap
            (RelativeLadderLayer.leafOccurrence I.boundary (by omega) qs).1) = ⊤ ∧
          w ((build (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht).baseMap
            (RelativeLadderLayer.leafOccurrence I.boundary (by omega) qt).1) =
              LowSeparator.donorMax (LowSeparator.donorField F) S.profile := by
  obtain ⟨w, hw, ho, hsupp, a, σ, hσ, hf, hc, hd⟩ :=
    exists_whole_chart (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht 0 ht hfull hS htop
  let T := state F a
  have hT : F.Admissible 1 T :=
    LowOnlyRecursiveCoverage.admissible_down F (by omega) (by omega) (state_admissible F a)
  have hf' (f) : σ (T.profile f) = S.profile f := by
    rw [state_profile]
    exact hf f
  have hm := map_donorMax (LowSeparator.donorField F) hσ hf'
  have hlt : LowSeparator.donorMax (LowSeparator.donorField F) T.profile < T.b := by
    apply lt_of_not_ge
    intro h
    exact (not_le_of_gt hactive)
      (((hf' LowSeparator.cutoffField).symm.trans_le (hσ.mono h)).trans_eq hm)
  obtain ⟨qs, hqs, hbase⟩ := native_source_base (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht a
  have hqs' : RelativeLadderLayer.ranks (F.fields 1) qs =
      LadderScalarRendering.fieldRank T.profile := hqs.trans (congrArg LadderScalarRendering.fieldRank (state_profile F a).symm)
  obtain ⟨_, qt, _, hqt⟩ := LowOnlyPaddedRankReadback.exists_anchors F hT
  have hread (b : F.Anchor 1) :
      w ((build (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht).baseMap
        (RelativeLadderLayer.leafOccurrence I.boundary (by omega) b).1) =
      σ (LadderScalarRendering.render (RelativeLadderLayer.ranks (F.fields 1)) qs T.profile
        (CanonicalFieldLayer.ceiling (t + 2) (Field I.left I.right))
        (SupportLadderRows.leaf (Nat.succ_pos (Fintype.card (Field I.left I.right))) b)) := by
    let d : Cell (base (⟨hroot, hA, hB, hC⟩ : I.LowFrame F)) :=
      (RelativeLadderLayer.leafOccurrence I.boundary (by omega) b).1
    have hdb : (base (⟨hroot, hA, hB, hC⟩ : I.LowFrame F)).cell d = (A, 1) :=
      RelativeLadderLayer.added_index I.boundary (by omega) _
    have hd' : GradedLe ((build (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht).carrier.cell
        ((build (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht).baseMap d)) (A, t + 2) := by
      rw [(build (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht).base_index, hdb]
      exact ⟨Finset.Subset.refl _, by omega⟩
    refine (hd ⟨_, hd'⟩).trans ((congrArg σ (hbase d)).trans ?_)
    apply congrArg σ
    change LadderScalarRendering.level (LadderScalarRendering.values a.val)
      (CanonicalFieldLayer.ceiling (t + 2) (Field I.left I.right))
      (RelativeLadderLayer.rankIndex I.boundary (by omega) (field I) (F.fields 1) qs
        (RelativeLadderLayer.added I.boundary (by omega)
          (SupportLadderRows.leaf (Nat.succ_pos _) b))) = _
    rw [RelativeLadderLayer.rankIndex_added]
    exact congrArg (fun s => LadderScalarRendering.render
      (RelativeLadderLayer.ranks (F.fields 1)) qs s
      (CanonicalFieldLayer.ceiling (t + 2) (Field I.left I.right))
      (SupportLadderRows.leaf (Nat.succ_pos _) b)) (state_profile F a).symm
  refine ⟨w, hw, ho, hsupp, T, hT, hlt, qs, qt, hqs', hqt, ?_, ?_⟩
  · exact (hread qs).trans ((congrArg σ (LowSeparatorRank.render_tip_self
      (RelativeLadderLayer.ranks (F.fields 1)) (Nat.succ_pos _) T.profile
      (Nat.lt_succ_self _) qs _)).trans hc)
  · exact (hread qt).trans ((congrArg σ (LowSeparatorRank.render_tip_partner
      (LowSeparator.donorField F) LowSeparator.cutoffField
      (RelativeLadderLayer.ranks (F.fields 1)) (Nat.succ_pos _) hlt
      (Nat.le_succ _) hqs' hqt _)).trans hm)

end
end VaughtConjecture.Knight.LowOnlyPaddedSelectedPair
