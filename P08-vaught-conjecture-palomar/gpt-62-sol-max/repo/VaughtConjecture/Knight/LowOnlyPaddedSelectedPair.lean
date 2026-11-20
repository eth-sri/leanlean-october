/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedSelectedChart
public import VaughtConjecture.Knight.LowSeparatorPaired
public import VaughtConjecture.Knight.LowOnlyPaddedRankReadback

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyPaddedSelectedPair

open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder

open LowOnlyPaddedContract LowOnlyPaddedIteration

open LowOnlyPaddedRenderChart LowOnlyPaddedSelectedChart

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
section Layers

variable (L : BuildContext A B C R m n K)

abbrev leafAt (t : ℕ) (ht : t + 2 ≤ A.card) := (L.tower t ht).leafAt

theorem source_leaf (t : ℕ) (ht : t + 2 ≤ A.card) (a b : L.F.Anchor (t + 2)) :
    (L.tower t ht).source a (leafAt L t ht b).1 =
      cut (LowSeparator.grid (X := Field L.I.left L.I.right) (t + 2)) a.val b.val :=
  (L.tower t ht).source_leaf a b

end Layers

def partner {t : ℕ} {P C : SemScheme n} {F : LowOnly.Family P C (t + 2)}
    (a : F.Anchor (t + 2))
    (hlt : LowSeparator.cutoffCut (t + 2) (LowSeparator.donorField F) (state F a).profile <
      (state F a).b) : F.Anchor (t + 2) :=
  ⟨(LowSeparator.partnerState F (state F a)).profile,
    LowSeparator.partnerState_mem F (by rw [state_profile]; exact a.property.1),
    LowSeparator.partnerState F (state F a),
    LowSeparator.partnerState_admissible F (state_admissible F a) hlt (by omega), rfl⟩

/-- Native grades at least two have a simultaneous selected pair on the
whole carrier, with all original fields and stage support retained. -/
theorem exists_whole_pair (t : ℕ) (L : BuildContext A B C R m n (t + 2))
    (ht : t + 2 ≤ A.card) (r : ℕ) (hr : t + r + 2 ≤ A.card)
    (hfull : t + r + 2 = A.card)
    {S : State L.I.left L.I.right} (hS : L.F.Admissible (t + r + 2) S)
    (htop : ∃ f, S.profile f = ⊤)
    (hactive : LowSeparator.cutoffCut (t + 2) (LowSeparator.donorField L.F) S.profile < S.b) :
    ∃ w : Cell (L.tower (t + r) hr).carrier → ExtOrd,
      RespectsSemantics (L.tower (t + r) hr).rows w ∧
      (∀ d, w ((L.tower (t + r) hr).original d) = S.profile (field L.I d)) ∧
      (∀ d, OrbitPrefixSupport.Supported (t + r + 2) ({⊤} : Set ExtOrd) S.profile (w d)) ∧
      ∃ a : L.F.Anchor (t + 2), ∃ hlt :
          LowSeparator.cutoffCut (t + 2) (LowSeparator.donorField L.F) (state L.F a).profile <
            (state L.F a).b,
        w (L.advance t ht r hr
          (leafAt L t ht a)).1 = ⊤ ∧
        w (L.advance t ht r hr
          (leafAt L t ht (partner a hlt))).1 =
            LowSeparator.cutoffCut (t + 2) (LowSeparator.donorField L.F) S.profile := by
  obtain ⟨w, hw, ho, hsupp, a, σ, hσ, hf, hc, hd⟩ :=
    exists_whole_chart L t ht r hr hfull hS htop
  have hf' (f) : σ ((state L.F a).profile f) = S.profile f := by
    rw [state_profile]
    exact hf f
  have hcut := map_cutoffCut (LowSeparator.donorField L.F) hσ hf'
  have hb := hf' LowSeparator.cutoffField
  have hlt : LowSeparator.cutoffCut (t + 2) (LowSeparator.donorField L.F)
      (state L.F a).profile < (state L.F a).b := by
    apply lt_of_not_ge
    intro h
    exact (not_le_of_gt hactive) ((hb.symm.trans_le (hσ.mono h)).trans_eq hcut)
  refine ⟨w, hw, ho, hsupp, a, hlt, ?_, ?_⟩
  · exact (hd (leafAt L t ht a)).trans
      ((congrArg σ ((L.tower t ht).source_diagonal a)).trans hc)
  · refine (hd (leafAt L t ht (partner a hlt))).trans ?_
    rw [source_leaf]
    change σ (cut (LowSeparator.grid (t + 2)) a.val
      (LowSeparator.partnerState L.F (state L.F a)).profile) = _
    rw [← show (state L.F a).profile = a.val from state_profile L.F a,
      LowSeparator.partnerState_profile,
      LowSeparator.cut_partner (t + 2) (LowSeparator.donorField L.F) LowSeparator.cutoffField
        (by rw [state_profile]; exact a.property.1) hlt]
    exact hcut

/-- The separate grade-one mechanism survives terminal collapse and every
later layer as well: use rank partners, not paired-slot source cuts. -/
theorem exists_whole_rank_pair (L : BuildContext A B C R m n 1)
    (t : ℕ) (ht : t + 2 ≤ A.card) (hfull : t + 2 = A.card)
    {S : State L.I.left L.I.right} (hS : L.F.Admissible (t + 2) S)
    (htop : ∃ f, S.profile f = ⊤)
    (hactive : LowSeparator.donorMax (LowSeparator.donorField L.F) S.profile < S.b) :
    ∃ w : Cell (L.tower t ht).carrier → ExtOrd,
      RespectsSemantics (L.tower t ht).rows w ∧
      (∀ d, w ((L.tower t ht).original d) = S.profile (field L.I d)) ∧
      (∀ d, OrbitPrefixSupport.Supported (t + 2) ({⊤} : Set ExtOrd) S.profile (w d)) ∧
      ∃ T : State L.I.left L.I.right, L.F.Admissible 1 T ∧
        LowSeparator.donorMax (LowSeparator.donorField L.F) T.profile < T.b ∧
        ∃ qs qt : L.F.Anchor 1,
          RelativeLadderLayer.ranks (L.F.fields 1) qs = LadderScalarRendering.fieldRank T.profile ∧
          RelativeLadderLayer.ranks (L.F.fields 1) qt = LadderScalarRendering.fieldRank
            (LowSeparatorRank.rankPartner (LowSeparator.donorField L.F)
              LowSeparator.cutoffField T.profile) ∧
          w ((L.tower t ht).baseMap
            (RelativeLadderLayer.leafOccurrence L.I.boundary (L.pos) qs).1) = ⊤ ∧
          w ((L.tower t ht).baseMap
            (RelativeLadderLayer.leafOccurrence L.I.boundary (L.pos) qt).1) =
              LowSeparator.donorMax (LowSeparator.donorField L.F) S.profile := by
  obtain ⟨w, hw, ho, hsupp, a, σ, hσ, hf, hc, hd⟩ :=
    exists_whole_chart L t ht 0 ht hfull hS htop
  let T := state L.F a
  have hT : L.F.Admissible 1 T :=
    LowOnlyRecursiveCoverage.admissible_down L.F (by omega) (by omega) (state_admissible L.F a)
  have hf' (f) : σ (T.profile f) = S.profile f := by
    change σ ((state L.F a).profile f) = _
    rw [state_profile]
    exact hf f
  have hm := map_donorMax (LowSeparator.donorField L.F) hσ hf'
  have hlt : LowSeparator.donorMax (LowSeparator.donorField L.F) T.profile < T.b := by
    apply lt_of_not_ge
    intro h
    exact (not_le_of_gt hactive)
      (((hf' LowSeparator.cutoffField).symm.trans_le (hσ.mono h)).trans_eq hm)
  let P := L.tower t ht
  let qs := P.baseAnchor a
  have hbase := P.source_base a
  have hqs := funext (P.anchor_ranks a)
  have hqs' : RelativeLadderLayer.ranks (L.F.fields 1) qs =
      LadderScalarRendering.fieldRank T.profile := by
    exact hqs.trans (congrArg LadderScalarRendering.fieldRank (state_profile L.F a).symm)
  obtain ⟨_, qt, _, hqt⟩ := LowOnlyPaddedRankReadback.exists_anchors L.F hT
  have hread (b : L.F.Anchor 1) :
      w ((L.tower t ht).baseMap
        (RelativeLadderLayer.leafOccurrence L.I.boundary (L.pos) b).1) =
      σ (LadderScalarRendering.render (RelativeLadderLayer.ranks (L.F.fields 1)) qs T.profile
        (CanonicalFieldLayer.ceiling (t + 2) (Field L.I.left L.I.right))
        (SupportLadderRows.leaf (Nat.succ_pos (Fintype.card (Field L.I.left L.I.right))) b)) := by
    let d : Cell (LowOnlyPaddedContract.base L.I L.F L.root L.height L.leftProper L.rightProper) :=
      (RelativeLadderLayer.leafOccurrence L.I.boundary (L.pos) b).1
    have hdb : (LowOnlyPaddedContract.base L.I L.F L.root L.height L.leftProper L.rightProper).cell d = (A, 1) :=
      RelativeLadderLayer.added_index L.I.boundary (by omega) _
    have hd' : GradedLe ((L.tower t ht).carrier.cell
        ((L.tower t ht).baseMap d)) (A, t + 2) := by
      rw [(L.tower t ht).base_index, hdb]
      exact ⟨Finset.Subset.refl _, by omega⟩
    refine (hd ⟨_, hd'⟩).trans (congrArg σ ((hbase d).trans ?_))
    refine (RelativeLadderLayer.renderWith_added L.I.boundary _ (field L.I) (L.F.fields 1)
      qs a.val _ _).trans ?_
    rw [show T.profile = a.val from state_profile L.F a]
    rfl

  refine ⟨w, hw, ho, hsupp, T, hT, hlt, qs, qt, hqs', hqt, ?_, ?_⟩
  · exact (hread qs).trans ((congrArg σ (LowSeparatorRank.render_tip_self
      (RelativeLadderLayer.ranks (L.F.fields 1)) (Nat.succ_pos _) T.profile
      (Nat.lt_succ_self _) qs _)).trans hc)
  · exact (hread qt).trans ((congrArg σ (LowSeparatorRank.render_tip_partner
      (LowSeparator.donorField L.F) LowSeparator.cutoffField
      (RelativeLadderLayer.ranks (L.F.fields 1)) (Nat.succ_pos _) hlt
      (Nat.le_succ _) hqs' hqt _)).trans hm)

end

end VaughtConjecture.Knight.LowOnlyPaddedSelectedPair
