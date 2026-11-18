/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteCoverReceivingCore
public import VaughtConjecture.Knight.LawfulCapping
public import VaughtConjecture.Knight.TopGradeStableCore
public import VaughtConjecture.Knight.ExpansionUniqueness
public import VaughtConjecture.Knight.CanonicalCoatomFiniteSupply
public import VaughtConjecture.Knight.CoatomFaceLift
public import VaughtConjecture.Knight.OrdinaryFiniteCutReceiving
public import VaughtConjecture.Knight.BlockCode
public import VaughtConjecture.Knight.ModelEmpty
public import VaughtConjecture.Knight.CountableTerminalFibres
public import Mathlib.Data.Set.Countable

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyPaddedModelReceiving
open TypeTower StageType KnightRealization
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open LowOnlyPaddedContract LowOnlyPaddedIteration LowOnlyPaddedInstallation
open LowOnlyPaddedEndpoints SourcePrefixRows SharpWitnessComposition
open PairedSlotComparison LadderScalarRendering FiniteProfileControllers SupportLadderRows
open LowSeparator CellScheme.restrictFace
noncomputable section
universe w

section RankSeparator
variable {X : Type*} [Fintype X] (N : X → Prop) [DecidablePred N] (b : X)

private def rankPartner [DecidableEq X] (s : X → ExtOrd) : X → ExtOrd :=
  Function.update s b (donorMax N s)

private def rankCut (s : X → ExtOrd) : ℕ :=
  LadderScalarRendering.rank (values s) (donorMax N s)

private theorem donorMax_mem_values {s : X → ExtOrd} (hne : donorMax N s ≠ ⊥) :
    donorMax N s ∈ values s := by
  rcases donorMax_cases N s with h | ⟨d, -, hd⟩
  · exact absurd h hne
  · exact mem_values.mpr ⟨hne, d, hd⟩

section Partner
variable [DecidableEq X] {s : X → ExtOrd} (hlt : donorMax N s < s b)
include hlt

private theorem values_rankPartner_below (y : ExtOrd) (hy : y < s b) :
    y ∈ values (rankPartner N b s) ↔ y ∈ values s := by
  simp only [mem_values, rankPartner]
  refine ⟨fun ⟨hz, d, hd⟩ => ⟨hz, ?_⟩, fun ⟨hz, d, hd⟩ => ⟨hz, ?_⟩⟩
  · by_cases hdb : d = b
    · rw [hdb, Function.update_self] at hd
      obtain ⟨_, e, he⟩ := mem_values.mp (donorMax_mem_values N (hd ▸ hz))
      exact ⟨e, he.trans hd⟩
    · rw [Function.update_of_ne hdb] at hd; exact ⟨d, hd⟩
  · by_cases hdb : d = b
    · subst hdb; exact absurd (hd ▸ hy) (lt_irrefl _)
    · exact ⟨d, by rw [Function.update_of_ne hdb]; exact hd⟩

private theorem rankPartner_cutoff : fieldRank (rankPartner N b s) b = rankCut N s := by
  unfold fieldRank rankCut rankPartner
  rw [Function.update_self]
  exact rank_congr_below (values_rankPartner_below N b hlt) hlt

private theorem cut_rankPartner {H : ℕ} (hH : Fintype.card X ≤ H) :
    FiniteProfileControllers.cut H (fieldRank s) (fieldRank (rankPartner N b s)) = rankCut N s := by
  have hlt_c : rankCut N s < fieldRank s b :=
    rank_strict (mem_values.mpr ⟨ne_of_gt (bot_le.trans_lt hlt), b, rfl⟩) hlt
  apply le_antisymm
  · apply le_of_not_gt fun hgt => ?_
    have hag := agree_cut H (fieldRank s) (fieldRank (rankPartner N b s)) b
    rw [rankPartner_cutoff N b hlt, min_eq_left hgt.le] at hag
    have := lt_min hlt_c hgt; omega
  · refine le_cut (((rank_le_card _ _).trans (values_card_le s)).trans hH) fun d => ?_
    by_cases hdb : d = b
    · rw [hdb, rankPartner_cutoff N b hlt, min_self, min_eq_right hlt_c.le]
    · unfold fieldRank
      rw [show rankPartner N b s d = s d from Function.update_of_ne hdb _ _]
      by_cases hsd : s d < s b
      · rw [rank_congr_below (values_rankPartner_below N b hlt) hsd]
      · have h1 : rankCut N s ≤ LadderScalarRendering.rank (values s) (s d) :=
          hlt_c.le.trans (rank_mono _ (not_lt.mp hsd))
        have h2 : rankCut N s ≤ LadderScalarRendering.rank (values (rankPartner N b s)) (s d) := by
          have hk := rankPartner_cutoff N b hlt
          unfold fieldRank rankPartner at hk; rw [Function.update_self] at hk
          exact hk ▸ rank_mono _ (hlt.le.trans (not_lt.mp hsd))
        rw [min_eq_right h1, min_eq_right h2]

private theorem activation_of_cut_lt {H : ℕ} (hH : Fintype.card X ≤ H) (a : X → ExtOrd)
    (h : FiniteProfileControllers.cut H (fieldRank a) (fieldRank (rankPartner N b s)) <
      FiniteProfileControllers.cut H (fieldRank a) (fieldRank s)) :
    donorMax N a < a b := by
  have hst := cut_rankPartner N b hlt hH
  have h1 := cut_triangle H (fieldRank a) (fieldRank s) (fieldRank (rankPartner N b s))
  have h2 := cut_triangle H (fieldRank s) (fieldRank a) (fieldRank (rankPartner N b s))
  rw [hst] at h1 h2; rw [FiniteProfileControllers.cut_symm H (fieldRank s) (fieldRank a)] at h2
  have hu : rankCut N s < FiniteProfileControllers.cut H (fieldRank a) (fieldRank s) := by omega
  have hag := agree_cut H (fieldRank a) (fieldRank s)
  have hlt_c : rankCut N s < fieldRank s b :=
    rank_strict (mem_values.mpr ⟨ne_of_gt (bot_le.trans_lt hlt), b, rfl⟩) hlt
  have hb : rankCut N s < fieldRank a b := by have := hag b; omega
  have hab : ⊥ < a b := bot_lt_iff_ne_bot.mpr fun hz => by
    have : fieldRank a b = 0 := by unfold fieldRank; rw [hz]; exact rank_bot (bot_not_values a)
    omega
  refine (Finset.sup_lt_iff hab).mpr fun d hd => ?_
  have hd' : N d := (Finset.mem_filter.mp hd).2
  have hsd : fieldRank s d ≤ rankCut N s := rank_mono _ (le_donorMax N s hd')
  have hlow : fieldRank a d ≤ rankCut N s := by have := hag d; omega
  by_contra hn
  have := rank_mono (values a) (not_lt.mp hn)
  unfold fieldRank at *; omega
end Partner

private theorem render_tip_partner [DecidableEq X] {Q : Type*} {H : ℕ}
    (profile : Q → X → ℕ) (hH : 0 < H) {s : X → ExtOrd} (hlt : donorMax N s < s b)
    (hHX : Fintype.card X ≤ H) {qs qt : Q} (hqs : profile qs = fieldRank s)
    (hqt : profile qt = fieldRank (rankPartner N b s)) (C : ExtOrd) :
    render profile qs s C (leaf hH qt) = donorMax N s := by
  unfold render
  rw [image, index_leaf, hqs, hqt, cut_rankPartner N b hlt hHX]
  by_cases hM : donorMax N s = ⊥
  · unfold rankCut; rw [hM, rank_bot (bot_not_values s), level_zero]
  · exact level_rank (donorMax_mem_values N hM) C

private theorem render_tip_self {Q : Type*} {H : ℕ} (profile : Q → X → ℕ) (hH : 0 < H)
    (s : X → ExtOrd) (hHX : Fintype.card X < H) (qs : Q) (C : ExtOrd) :
    render profile qs s C (leaf hH qs) = C := by
  classical
  unfold render
  rw [image, index_leaf, FiniteProfileControllers.cut_refl, LadderScalarRendering.level,
    ite_eq_left ((values_card_le s).trans_lt hHX)]

private theorem low_min_le {n : ℕ} {P C : SemScheme n} (F : LowOnly.Family P C 1)
    {A : State P C} (hA : F.Admissible 1 A) (hm : F.maximum A < A.b)
    (d : Cell P.scheme) (hd : F.p d = ⊤) : min (A.v F.gap.c) (A.v F.gap.r.1) ≤ A.u d := by
  have hlow := hA.low le_rfl hm d hd
  change max A.b (min (A.v F.gap.c) (extVisibilityReplace (A.v F.gap.r.1) 1 1)) ≤ A.u d at hlow
  have hvis : SelfVis 1 (A.v F.gap.r.1) := by
    have h := (hA.lawfulC.orderly (CellScheme.below.mono (F.gap.domLe le_rfl) F.gap.r)).symm
    change SelfVis (C.scheme.grade F.gap.r.1) (A.v F.gap.r.1) at h
    exact h.mono (C.scheme.grade_pos _)
  rw [evr_eq_self_of_selfVis hvis] at hlow
  exact (le_max_right _ _).trans hlow
end RankSeparator

section Scalar
variable {X : Type*} [Fintype X] (N : X → Prop) [DecidablePred N]

private theorem map_donorMax {k : ℕ} {σ : ExtOrd → ExtOrd} (hσ : BoundedMap k σ)
    {a s : X → ExtOrd} (hf : ∀ f, σ (a f) = s f) :
    σ (donorMax N a) = donorMax N s := by
  refine le_antisymm ?_ (donorMax_le N fun d hd => by rw [← hf]; exact hσ.mono (le_donorMax N a hd))
  rcases donorMax_cases N a with hz | ⟨d, hd, he⟩
  · rw [hz, hσ.bot]; exact bot_le
  · rw [← he, hf]; exact le_donorMax N s hd

private theorem map_cutoffCut {k : ℕ} {σ : ExtOrd → ExtOrd} (hσ : BoundedMap k σ)
    {a s : X → ExtOrd} (hf : ∀ f, σ (a f) = s f) :
    σ (cutoffCut k N a) = cutoffCut k N s := by
  unfold cutoffCut; rw [hσ.comm _ k k le_rfl le_rfl, map_donorMax N hσ hf]

private theorem separator_of_cap {D : Type*} {w q : D → ExtOrd} {lo hi : D} {a δ : ExtOrd}
    (hwlo : w lo = a) (hwhi : w hi = ⊤) (hδ : a < δ)
    (hcap : ∀ d, min (q d) δ = min (w d) δ) : q lo < q hi := by
  have hlo : q lo = a := (AmbientGradeCharts.eq_of_cap_below (hcap lo) (hwlo.trans_lt hδ)).trans hwlo
  have he := hcap hi; rw [hwhi, min_top_left] at he
  exact hlo.trans_lt (hδ.trans_le (min_eq_right_iff.mp he))

private theorem exact_of_cap_and_top {D Y : Type*} {w q : D → ExtOrd} {p : Y → ExtOrd}
    (f : Y → D) {δ : ExtOrd} (hw : ∀ d, w (f d) = p d)
    (hcap : ∀ d, min (q d) δ = min (w d) δ)
    (hproper : ∀ d, p d ≠ ⊤ → p d < δ)
    (htop : ∀ d, p d = ⊤ → q (f d) = ⊤) (d : Y) : q (f d) = p d := by
  by_cases hd : p d = ⊤
  · exact (htop d hd).trans hd.symm
  · exact (AmbientGradeCharts.eq_of_cap_below (hcap (f d))
      ((hw d).trans_lt (hproper d hd))).trans (hw d)
end Scalar

private theorem exists_anchors {n : ℕ} {P C : SemScheme n} (F : LowOnly.Family P C 1)
    {S : State P C} (hS : F.Admissible 1 S) :
    ∃ a b : F.Anchor 1,
      RelativeLadderLayer.ranks (F.fields 1) a = fieldRank S.profile ∧
      RelativeLadderLayer.ranks (F.fields 1) b =
        fieldRank (rankPartner (donorField F) cutoffField S.profile) := by
  let S' : State P C := ⟨S.u, S.v, F.maximum S⟩
  have hS' : F.Admissible 1 S' :=
    { lawfulP := hS.lawfulP, lawfulC := hS.lawfulC, shared := hS.shared,
      futureP := hS.futureP, futureC := hS.futureC,
      cutoff := by
        change SelfVis 1 (F.maximum S); rw [maximum_eq_donorMax]
        rcases donorMax_cases (donorField F) S.profile with hz | ⟨d, _, hd⟩
        · rw [hz]; exact selfVis_bot 1
        · rw [← hd]; exact LowOnlyRecursiveCharts.profile_visible_one F le_rfl hS d,
      low := fun _ hm _ _ => (lt_irrefl (F.maximum S) hm).elim }
  have hp : S'.profile = rankPartner (donorField F) cutoffField S.profile := by
    classical
    funext d; unfold rankPartner; rcases d with d | d | d
    · exact (Function.update_of_ne (by simp) _ _).symm
    · exact (Function.update_of_ne (by simp) _ _).symm
    · cases d
      exact (maximum_eq_donorMax F S).trans (Function.update_self cutoffField _ S.profile).symm
  obtain ⟨a, ha⟩ := F.exists_rank_anchor le_rfl hS
  obtain ⟨b, hb⟩ := F.exists_rank_anchor le_rfl hS'
  exact ⟨a, b, funext ha, (funext hb).trans (congrArg fieldRank hp)⟩

section TowerCert
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)} {m n : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

section FixedFamily
variable {K : ℕ} (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)

private def belowEquiv (t : ℕ) (ht : t + 2 ≤ A.card) (J : Finset ι × ℕ) (hJ : J.2 ≤ t + 2) :
    (r : ℕ) → (hr : t + r + 2 ≤ A.card) →
      (build I F hroot hA hB hC t ht).carrier.below J ≃
        (build I F hroot hA hB hC (t + r) hr).carrier.below J
  | 0, _ => Equiv.refl _
  | r + 1, hr =>
    (belowEquiv t ht J hJ r (by omega)).trans
      (HighLayerBountiful.equiv (build I F hroot hA hB hC (t + r) (by omega)).carrier
        (F.Anchor (t + r + 2 + 1)) (t + r + 2 + 1) (by omega) (by omega) J
        (fun h => by have := h.2; omega))

private theorem pullback (t : ℕ) (ht : t + 2 ≤ A.card) (J : Finset ι × ℕ) (hJ : J.2 ≤ t + 2)
    (r : ℕ) (hr : t + r + 2 ≤ A.card)
    {q : (build I F hroot hA hB hC (t + r) hr).carrier.below J → ExtOrd}
    (hq : RespectsSemanticsBelow (build I F hroot hA hB hC (t + r) hr).rows J q) :
    RespectsSemanticsBelow (build I F hroot hA hB hC t ht).rows J
      (q ∘ belowEquiv I hA hB hC F hroot t ht J hJ r hr) := by
  induction r with
  | zero => exact hq
  | succ r ih =>
    let P := build I F hroot hA hB hC (t + r) (by omega)
    have hnot : ¬ GradedLe (A, t + r + 2 + 1) J := fun h => by have := h.2; omega
    let e := HighLayerBountiful.equiv P.carrier (F.Anchor (t + r + 2 + 1))
      (t + r + 2 + 1) (by omega) (by omega) J hnot
    have hp : RespectsSemanticsBelow P.rows J (q ∘ e) := by
      apply (SeparatedLayerFace.respects_iff P.carrier (F.Anchor (t + r + 2 + 1))
        (t + r + 2 + 1) (by omega) (by omega) (P.separated (by omega)) P.rows
        (LowOnlyPaddedStepRows.rows P (by omega) (by omega))
        (LowOnlyPaddedStepRows.inherited_row P (by omega) (by omega)) J hnot _).mpr
      change RespectsSemanticsBelow _ J (fun x => q (e (e.symm x)))
      simp only [Equiv.apply_symm_apply]; exact hq
    exact ih (by omega) hp

private theorem belowEquiv_original (t : ℕ) (ht : t + 2 ≤ A.card) (J : Finset ι × ℕ)
    (hJ : J.2 ≤ t + 2) (r : ℕ) (hr : t + r + 2 ≤ A.card) (d : I.boundary.below J) :
    (belowEquiv I hA hB hC F hroot t ht J hJ r hr
      ⟨original I F hroot hA hB hC t ht d.1, by rw [original_index]; exact d.2⟩).1 =
      original I F hroot hA hB hC (t + r) hr d.1 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    exact congrArg (LowOnlyPaddedStepRows.old
      (build I F hroot hA hB hC (t + r) (by omega)) (by omega)) (ih (by omega))

private def nativeSource : (t : ℕ) → (ht : t + 2 ≤ A.card) → F.Anchor (t + 2) →
    Cell (build I F hroot hA hB hC t ht).carrier → ExtOrd
  | 0, _, a => LowOnlyPaddedSuccessor.source I F hroot hA hB hC a
  | t + 1, ht, a => LowOnlyPaddedStepRows.source
      (build I F hroot hA hB hC t (by omega)) (by omega) ht a

private theorem native_source_original (t : ℕ) (ht : t + 2 ≤ A.card)
    (a : F.Anchor (t + 2)) (d : Cell I.boundary) :
    nativeSource I hA hB hC F hroot t ht a (original I F hroot hA hB hC t ht d) =
      a.val (field I d) := by
  cases t with
  | zero => exact LowOnlyPaddedSuccessor.original_readback I F hroot hA hB hC a d
  | succ t => exact LowOnlyPaddedStepDecode.source_original _ _ _ a d

private theorem later_chart (t : ℕ) (ht : t + 2 ≤ A.card) (r : ℕ)
    (hr : t + r + 2 ≤ A.card) {j : ℕ} (hj : t + r + 2 ≤ j)
    (S : State I.left I.right) (hS : F.Admissible j S) (hp : ∀ f, S.profile f ≠ ⊤)
    {G : Finset ExtOrd} {H : ExtOrd} (hG : ∀ z ∈ G, SelfVis (t + r + 2) z)
    (hH : SelfVis (t + r + 2) H) (hb : ∀ f, S.profile f ≤ H) :
    ∃ a : F.Anchor (t + 2), ∃ σ : ExtOrd → ExtOrd,
      BoundedMap (t + 2) σ ∧
      (∀ f, σ (a.val f) = S.profile f) ∧
      σ (CanonicalFieldLayer.ceiling (t + 2) (Field I.left I.right)) = H ∧
      ∀ d : (build I F hroot hA hB hC t ht).carrier.below (A, t + 2),
        (build I F hroot hA hB hC (t + r) hr).render hj S hS hp G H
          (belowEquiv I hA hB hC F hroot t ht (A, t + 2) le_rfl r hr d).1 =
            σ (nativeSource I hA hB hC F hroot t ht a d.1) := by
  induction r generalizing j S G H with
  | zero =>
    let a := LowOnlyRecursiveCoverage.normalizedAnchor F (by omega) hj hS hp
    let σ := PairedSlotDecoder.decode (t + 2) (PairedSlotEncoding.values S.profile) G H
    refine ⟨a, σ, boundedMap_of_witness (PairedSlotDecoder.decode_witness hG hH), fun f => ?_,
      decode_reserved_ceiling hH hb, fun _ => by cases t <;> rfl⟩
    change σ (F.fields (t + 2) a f) = _
    rw [LowOnlyRecursiveCoverage.normalizedAnchor_fields F (by omega) hj hS hp]
    exact PairedSlotDecoder.decode_normalize hG hH hp f
  | succ r ih =>
    let P := build I F hroot hA hB hC (t + r) (by omega)
    let a₁ := LowOnlyPaddedStepRendering.normalized hj S hS hp
    let T := state F a₁
    obtain ⟨a, τ, hτ, hf, hc, hd⟩ := ih (by omega) (Nat.le_succ _) T
      (state_admissible F a₁) (state_proper F a₁)
      (G := LowOnlyPaddedStepRows.grid P) (H := LowOnlyPaddedStepRows.ceiling P)
      (fun _ hz => (sourceGrid_visible hz).mono (Nat.le_succ _))
      ((sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono (Nat.le_succ _))
      (fun f => by rw [show T.profile = F.fields _ a₁ from state_profile F a₁]; exact LowOnlyRecursiveCharts.anchor_bound F a₁ f)
    let δ := PairedSlotDecoder.decode (t + r + 2 + 1) (PairedSlotEncoding.values S.profile) G H
    have hδb : BoundedMap (t + r + 2 + 1) δ :=
      boundedMap_of_witness (PairedSlotDecoder.decode_witness hG hH)
    refine ⟨a, δ ∘ τ, ⟨by simp only [Function.comp_apply, hτ.bot, hδb.bot], hδb.mono.comp hτ.mono,
      fun x k i hk hi => by
        simp only [Function.comp_apply]
        rw [hτ.comm x k i hk hi, hδb.comm _ k i (by omega) hi]⟩,
      fun f => (congrArg δ (hf f)).trans (by
        change δ ((state F a₁).profile f) = _
        rw [state_profile, LowOnlyPaddedStepRendering.normalized_fields]
        exact PairedSlotDecoder.decode_normalize hG hH hp f),
      (congrArg δ hc).trans (decode_reserved_ceiling hH hb), fun d => ?_⟩
    change δ (LowOnlyPaddedStepRows.source P (by omega) (by omega) a₁
      (LowOnlyPaddedStepRows.old P (by omega) _)) = _
    rw [LowOnlyPaddedStepRows.source_old]
    exact congrArg δ (hd d)

private theorem native_decoded_lawful (u : ℕ) (hu : u + 2 ≤ A.card)
    (a : F.Anchor (u + 2)) {δ : ExtOrd → ExtOrd} (hδ : Witness (gTop (u + 2)) δ)
    (hreflect : ∀ f, δ (a.val f) = ⊥ → a.val f = ⊥)
    (horiginal : RespectsSemanticsBelow I.rows (A, u + 2) (fun d => δ (a.val (field I d.1)))) :
    RespectsSemanticsBelow (build I F hroot hA hB hC u hu).rows (A, u + 2)
      (fun d => δ (nativeSource I hA hB hC F hroot u hu a d.1)) := by
  cases u with
  | zero => exact LowOnlyPaddedSupply.decoded_lawful I F hroot hA hB hC a hδ hreflect horiginal
  | succ _ => exact LowOnlyPaddedStepSupply.decoded_lawful _ _ _ a hδ hreflect horiginal

private theorem exists_whole_chart (t : ℕ) (ht : t + 2 ≤ A.card) (r : ℕ)
    (hr : t + r + 2 ≤ A.card) (hfull : t + r + 2 = A.card)
    {S : State I.left I.right} (hS : F.Admissible (t + r + 2) S)
    (htop : ∃ f, S.profile f = ⊤) :
    ∃ w : Cell (build I F hroot hA hB hC (t + r) hr).carrier → ExtOrd,
      RespectsSemantics (build I F hroot hA hB hC (t + r) hr).rows w ∧
      (∀ d, w (original I F hroot hA hB hC (t + r) hr d) = S.profile (field I d)) ∧
      ∃ a : F.Anchor (t + 2), ∃ σ : ExtOrd → ExtOrd,
        BoundedMap (t + 2) σ ∧
        (∀ f, σ (a.val f) = S.profile f) ∧
        σ (CanonicalFieldLayer.ceiling (t + 2) (Field I.left I.right)) = ⊤ ∧
        ∀ d : (build I F hroot hA hB hC t ht).carrier.below (A, t + 2),
          w (belowEquiv I hA hB hC F hroot t ht (A, t + 2) le_rfl r hr d).1 =
            σ (nativeSource I hA hB hC F hroot t ht a d.1) := by
  obtain ⟨Q, hQ, hcanon, δ, hδ, hread, hreflect, _⟩ :=
    F.exists_supported_decoder (by omega) hS
  let b : F.Anchor (t + r + 2) := ⟨Q.profile, hcanon, Q, hQ, rfl⟩
  have horiginal : RespectsSemanticsBelow I.rows (A, t + r + 2)
      (fun d => δ (b.val (field I d.1))) := by
    simpa only [b, hread] using LowOnlyOrderedSources.boundary_lawful_at I F hroot (t + r + 2) S hS
  have hw := native_decoded_lawful I hA hB hC F hroot (t + r) hr b hδ hreflect horiginal
  have hall (d : Cell (build I F hroot hA hB hC (t + r) hr).carrier) :
      GradedLe ((build I F hroot hA hB hC (t + r) hr).carrier.cell d) (A, t + r + 2) := by
    let D := (build I F hroot hA hB hC (t + r) hr).carrier
    have hs := D.isPlan.subset_of_mem (D.scope_mem_plan d)
    exact ⟨hs, ((D.grade_le_card_scope d).trans (Finset.card_le_card hs)).trans_eq hfull.symm⟩
  obtain ⟨a, τ, hτ, hf, hc, hd⟩ : ∃ a : F.Anchor (t + 2), ∃ σ : ExtOrd → ExtOrd,
      BoundedMap (t + 2) σ ∧ (∀ f, σ (a.val f) = b.val f) ∧
      σ (CanonicalFieldLayer.ceiling (t + 2) (Field I.left I.right)) =
        CanonicalFieldLayer.ceiling (t + r + 2) (Field I.left I.right) ∧
      ∀ d : (build I F hroot hA hB hC t ht).carrier.below (A, t + 2),
        nativeSource I hA hB hC F hroot (t + r) hr b
          (belowEquiv I hA hB hC F hroot t ht (A, t + 2) le_rfl r hr d).1 =
            σ (nativeSource I hA hB hC F hroot t ht a d.1) := by
    cases r with
    | zero => exact ⟨b, id, ⟨rfl, monotone_id, fun _ _ _ _ _ => rfl⟩, fun _ => rfl, rfl, fun _ => rfl⟩
    | succ r =>
      let P := build I F hroot hA hB hC (t + r) (by omega)
      obtain ⟨a, σ, hσ, hf, hc, hd⟩ := later_chart I hA hB hC F hroot t ht r
        (by omega) (Nat.le_succ _) (state F b) (state_admissible F b) (state_proper F b)
        (G := LowOnlyPaddedStepRows.grid P) (H := LowOnlyPaddedStepRows.ceiling P)
        (fun _ hz => (sourceGrid_visible hz).mono (Nat.le_succ _))
        ((sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono (Nat.le_succ _))
        (fun f => by rw [state_profile]; exact LowOnlyRecursiveCharts.anchor_bound F b f)
      refine ⟨a, σ, hσ, fun f => (hf f).trans (congrFun (state_profile F b) f), hc, fun d => ?_⟩
      change LowOnlyPaddedStepRows.source P (by omega) (by omega) b
        (LowOnlyPaddedStepRows.old P (by omega) _) = _
      rw [LowOnlyPaddedStepRows.source_old]; exact hd d
  obtain ⟨f, hft⟩ := htop
  have hceiling : δ (CanonicalFieldLayer.ceiling (t + r + 2) (Field I.left I.right)) = ⊤ :=
    top_le_iff.mp ((hft.symm.trans (hread f).symm).le.trans
      (hδ.mono (LowOnlyRecursiveCharts.anchor_bound F b f)))
  exact ⟨fun d => δ (nativeSource I hA hB hC F hroot (t + r) hr b d), hw.toRespects hall,
    fun d => (congrArg δ (native_source_original I hA hB hC F hroot (t + r) hr b d)).trans (hread _),
    a, δ ∘ τ, ⟨by simp only [Function.comp_apply, hτ.bot, hδ.bot], hδ.mono.comp hτ.mono,
      fun x k i hk hi => by
        simp only [Function.comp_apply]
        rw [hτ.comm x k i hk hi, (boundedMap_of_witness hδ).comm _ k i (by omega) hi]⟩,
    fun f => (congrArg δ (hf f)).trans (hread f), (congrArg δ hc).trans hceiling,
    fun d => congrArg δ (hd d)⟩

private def leafAt : (t : ℕ) → (ht : t + 2 ≤ A.card) → F.Anchor (t + 2) →
    (build I F hroot hA hB hC t ht).carrier.below (A, t + 2)
  | 0, _, a => ⟨LowOnlyPaddedSuccessor.leaf I F hroot hA hB hC a,
      (LowOnlyPaddedSuccessor.leaf_index I F hroot hA hB hC a).symm ▸ GradedLe.refl _⟩
  | t + 1, ht, a => LowOnlyPaddedStepChart.leafAt
      (build I F hroot hA hB hC t (by omega)) ht a

private theorem source_leaf (t : ℕ) (ht : t + 2 ≤ A.card) (a b : F.Anchor (t + 2)) :
    nativeSource I hA hB hC F hroot t ht a (leafAt I hA hB hC F hroot t ht b).1 =
      SourcePrefixRows.cut (LowSeparator.grid (X := Field I.left I.right) (t + 2)) a.val b.val := by
  cases t with
  | zero => exact LowOnlyPaddedSuccessor.source_leaf I F hroot hA hB hC a b
  | succ t => exact LowOnlyPaddedStepRows.source_new _ _ _ a b

end FixedFamily

private theorem rank_certificate (F : LowOnly.Family I.left I.right 1)
    (hroot : ∀ i : Cell I.common.scheme,
      ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
        a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
    (t : ℕ) (ht : t + 2 ≤ A.card) (hfull : t + 2 = A.card)
    {S : State I.left I.right} (hS : F.Admissible (t + 2) S)
    (hdonor : S.u = F.p) (htop : S.v F.gap.c = ⊤)
    (hactive : donorMax (donorField F) S.profile < S.b) :
    ∃ w : Cell (build I F hroot hA hB hC t ht).carrier → ExtOrd,
      RespectsSemantics (build I F hroot hA hB hC t ht).rows w ∧
      (∀ d, w (original I F hroot hA hB hC t ht d) = S.profile (field I d)) ∧
      ∀ q : Cell (build I F hroot hA hB hC t ht).carrier → ExtOrd,
        RespectsSemantics (build I F hroot hA hB hC t ht).rows q →
        q (original I F hroot hA hB hC t ht (I.rightFace.map F.gap.c)) = ⊤ →
        q (original I F hroot hA hB hC t ht (I.rightFace.map F.gap.r.1)) = ⊤ →
        ∀ δ, donorMax (donorField F) S.profile < δ →
          (∀ d, min (q d) δ = min (w d) δ) →
          ∀ d, q (original I F hroot hA hB hC t ht (I.leftFace.map d)) = F.p d := by
  obtain ⟨w, hw, ho, a, σ, hσ, hf, hc, hd⟩ :=
    exists_whole_chart I hA hB hC F hroot t ht 0 ht hfull hS ⟨Sum.inr (Sum.inl F.gap.c), htop⟩
  let T := state F a
  have hT : F.Admissible 1 T :=
    LowOnlyRecursiveCoverage.admissible_down F (by omega) (by omega) (state_admissible F a)
  have hf' (f) : σ (T.profile f) = S.profile f := by rw [state_profile]; exact hf f
  have hm := map_donorMax (donorField F) hσ hf'
  have hlt : donorMax (donorField F) T.profile < T.b :=
    lt_of_not_ge fun h => (not_le_of_gt hactive)
      (((hf' cutoffField).symm.trans_le (hσ.mono h)).trans_eq hm)
  obtain ⟨qs, hqs, hbase⟩ : ∃ b : F.Anchor 1,
      RelativeLadderLayer.ranks (F.fields 1) b = fieldRank a.val ∧
      ∀ d : Cell (base I F hroot hA hB hC),
        nativeSource I hA hB hC F hroot t ht a ((build I F hroot hA hB hC t ht).baseMap d) =
        RelativeLadderLayer.renderWith I.boundary (by omega) (field I) (F.fields 1)
          b a.val (CanonicalFieldLayer.ceiling (t + 2) (Field I.left I.right)) d := by
    cases t with
    | zero =>
      exact ⟨LowOnlyPaddedSuccessor.baseAnchor F a,
        funext (LowOnlyPaddedSuccessor.baseAnchor_ranks F a),
        fun d => (LowOnlyPaddedSuccessor.input I F hroot hA hB hC).source_old a d⟩
    | succ t =>
      let P := build I F hroot hA hB hC t (by omega)
      exact ⟨LowOnlyPaddedStepSupply.birth P a, funext (LowOnlyPaddedStepSupply.birth_ranks P a),
        LowOnlyPaddedStepSupply.source_base P (by omega) ht a⟩
  have hqs' : RelativeLadderLayer.ranks (F.fields 1) qs = fieldRank T.profile :=
    hqs.trans (congrArg fieldRank (state_profile F a).symm)
  obtain ⟨_, qt, _, hqt⟩ := exists_anchors F hT
  let L := build I F hroot hA hB hC t ht
  have hread_tip (b : F.Anchor 1) :
      w (L.baseMap (RelativeLadderLayer.leafOccurrence I.boundary (by omega) b).1) =
      σ (render (RelativeLadderLayer.ranks (F.fields 1)) qs T.profile
        (CanonicalFieldLayer.ceiling (t + 2) (Field I.left I.right))
        (leaf (Nat.succ_pos (Fintype.card (Field I.left I.right))) b)) := by
    let d : Cell (base I F hroot hA hB hC) :=
      (RelativeLadderLayer.leafOccurrence I.boundary (by omega) b).1
    have hdb : (base I F hroot hA hB hC).cell d = (A, 1) :=
      RelativeLadderLayer.added_index I.boundary (by omega) _
    have hd' : GradedLe (L.carrier.cell (L.baseMap d)) (A, t + 2) := by
      rw [L.base_index, hdb]; exact ⟨Finset.Subset.refl _, by omega⟩
    refine (hd ⟨_, hd'⟩).trans ((congrArg σ (hbase d)).trans (congrArg σ ?_))
    change LadderScalarRendering.level (values a.val)
      (CanonicalFieldLayer.ceiling (t + 2) (Field I.left I.right))
      (RelativeLadderLayer.rankIndex I.boundary (by omega) (field I) (F.fields 1) qs
        (RelativeLadderLayer.added I.boundary (by omega) (leaf (Nat.succ_pos _) b))) = _
    rw [RelativeLadderLayer.rankIndex_added]
    exact congrArg (fun s => render (RelativeLadderLayer.ranks (F.fields 1)) qs s
      (CanonicalFieldLayer.ceiling (t + 2) (Field I.left I.right)) (leaf (Nat.succ_pos _) b))
      (state_profile F a).symm
  have hpos : w (L.baseMap (RelativeLadderLayer.leafOccurrence I.boundary (by omega) qs).1) = ⊤ :=
    (hread_tip qs).trans ((congrArg σ (render_tip_self
      (RelativeLadderLayer.ranks (F.fields 1)) (Nat.succ_pos _) T.profile
      (Nat.lt_succ_self _) qs _)).trans hc)
  have hneg : w (L.baseMap (RelativeLadderLayer.leafOccurrence I.boundary (by omega) qt).1) =
      donorMax (donorField F) S.profile :=
    (hread_tip qt).trans ((congrArg σ (render_tip_partner
      (donorField F) cutoffField (RelativeLadderLayer.ranks (F.fields 1)) (Nat.succ_pos _) hlt
      (Nat.le_succ _) hqs' hqt _)).trans hm)
  refine ⟨w, hw, ho, fun q hq hc' hr' δ hδ hcap => ?_⟩
  have hsep := separator_of_cap hneg hpos hδ hcap
  refine exact_of_cap_and_top (fun d => original I F hroot hA hB hC t ht (I.leftFace.map d))
    (fun d => (ho (I.leftFace.map d)).trans ((field_donor I S d).trans (congrFun hdonor d)))
    hcap
    (fun d hd => by
      have hm' := le_donorMax (donorField F) S.profile (d := .inl d) hd
      change S.u d ≤ _ at hm'; rw [hdonor] at hm'; exact hm'.trans_lt hδ)
    (fun d hd => ?_)
  let d' : I.left.scheme.below (effC n 1) :=
    ⟨d, Finset.subset_univ _, le_min (F.top_grade d hd) (gradeC_le d)⟩
  obtain ⟨a₀, _⟩ := F.exists_rank_anchor le_rfl (F.zero_admissible 1)
  have hbase_q : RespectsSemanticsBelow (baseRows I F hroot hA hB hC) (A, 1)
      (fun x => q (L.baseMap x.1)) :=
    GradeCutLayerRows.cast_respects (base I F hroot hA hB hC) (baseRows I F hroot hA hB hC)
      (RelativeLadderLayer.added_index I.boundary (by omega) (leaf (Nat.succ_pos _) a₀))
      ((L.base_respects _ q).mp (hq.toBelow _))
  obtain ⟨a₁, τ, hτ, _, hread_leaf⟩ := RelativeLadderLayer.exists_leaf_chart I.boundary I.rows
    (by omega) (field I) (F.fields 1) (proper I hB hC) qs hbase_q
  let H := RelativeLadderLayer.rungs (X := Field I.left I.right)
  let g : ℕ → ExtOrd := τ ∘ SupportLadderRows.source H
  have hg : Monotone g := hτ.mono.comp (SupportLadderRows.source_mono H)
  have he (x : (base I F hroot hA hB hC).below (A, 1)) :
      q (L.baseMap x.1) =
        g (RelativeLadderLayer.rankIndex I.boundary (by omega) (field I) (F.fields 1) a₁ x.1) := by
    have hx := hread_leaf x
    change τ (SupportLadderRows.source
      (SupportLadderRows.ceiling (RelativeLadderLayer.ranks (F.fields 1))
        (leaf (Nat.succ_pos _) a₁))
      (RelativeLadderLayer.rankIndex I.boundary (by omega) (field I) (F.fields 1) a₁ x.1)) = _ at hx
    rw [SupportLadderRows.ceiling_leaf] at hx; exact hx.symm
  have htip (b : F.Anchor 1) :
      q (L.baseMap (RelativeLadderLayer.leafOccurrence I.boundary (by omega) b).1) =
        g (FiniteProfileControllers.cut H (RelativeLadderLayer.ranks (F.fields 1) a₁)
          (RelativeLadderLayer.ranks (F.fields 1) b)) :=
    (he _).trans (congrArg g
      ((RelativeLadderLayer.rankIndex_added I.boundary (by omega) (field I) (F.fields 1) a₁
        (leaf (Nat.succ_pos _) b)).trans
        (index_leaf (profile := RelativeLadderLayer.ranks (F.fields 1)) (Nat.succ_pos _) a₁ b)))
  have hcut : FiniteProfileControllers.cut H (RelativeLadderLayer.ranks (F.fields 1) a₁)
      (RelativeLadderLayer.ranks (F.fields 1) qt) <
      FiniteProfileControllers.cut H (RelativeLadderLayer.ranks (F.fields 1) a₁)
        (RelativeLadderLayer.ranks (F.fields 1) qs) :=
    lt_of_not_ge fun hh => (not_lt.mpr (hg hh)) ((htip qt).symm.trans_lt (hsep.trans_eq (htip qs)))
  rw [hqs', hqt] at hcut
  have hact := activation_of_cut_lt (donorField F) cutoffField hlt (Nat.le_succ _) a₁.val hcut
  have hm_act : F.maximum (state F a₁) < (state F a₁).b := by
    rw [maximum_eq_donorMax]
    change donorMax (donorField F) (state F a₁).profile < (state F a₁).profile cutoffField
    simpa only [state_profile, Family.fields] using hact
  have hv (e : I.right.scheme.below (effC n 1)) :
      q (L.baseMap (RelativeLadderLayer.old I.boundary (by omega) (I.rightFace.map e.1))) =
        g (fieldRank (state F a₁).profile (.inr (.inl e.1))) :=
    (he ⟨RelativeLadderLayer.old I.boundary (by omega) (I.rightFace.map e.1), by
      rw [RelativeLadderLayer.old_index]; exact (privateIncl I e).2⟩).trans
      (congrArg g ((RelativeLadderLayer.rankIndex_old I.boundary (by omega) (field I)
        (F.fields 1) a₁ _).trans (by
          change fieldRank (F.fields 1 a₁) _ = _; rw [← state_profile]
          exact congrArg (LadderScalarRendering.rank (values (state F a₁).profile))
            (field_private I F hroot (state_admissible F a₁) e.1))))
  have hu : q (L.baseMap (RelativeLadderLayer.old I.boundary (by omega) (I.leftFace.map d))) =
      g (fieldRank (state F a₁).profile (.inl d)) :=
    (he ⟨RelativeLadderLayer.old I.boundary (by omega) (I.leftFace.map d), by
      rw [RelativeLadderLayer.old_index]; exact (donorIncl I d').2⟩).trans
      (congrArg g ((RelativeLadderLayer.rankIndex_old I.boundary (by omega) (field I)
        (F.fields 1) a₁ _).trans (by
          change fieldRank (F.fields 1 a₁) _ = _; rw [← state_profile]
          exact congrArg (LadderScalarRendering.rank (values (state F a₁).profile))
            (field_donor I (state F a₁) d))))
  have hc_g : g (fieldRank (state F a₁).profile (.inr (.inl F.gap.c))) = ⊤ :=
    (hv (F.gap.cC le_rfl)).symm.trans hc'
  have hr_g : g (fieldRank (state F a₁).profile (.inr (.inl F.gap.r.1))) = ⊤ :=
    (hv (F.gap.rC le_rfl)).symm.trans hr'
  rw [show original I F hroot hA hB hC t ht (I.leftFace.map d) =
    L.baseMap (RelativeLadderLayer.old I.boundary (by omega) (I.leftFace.map d)) from rfl, hu]
  rcases min_le_iff.mp (low_min_le F (state_admissible F a₁) hm_act d hd) with hh | hh
  · exact top_le_iff.mp (hc_g ▸ hg (rank_mono (values (state F a₁).profile) hh))
  · exact top_le_iff.mp (hr_g ▸ hg (rank_mono (values (state F a₁).profile) hh))

private theorem paired_certificate (t : ℕ) (F : LowOnly.Family I.left I.right (t + 2))
    (hroot : ∀ i : Cell I.common.scheme,
      ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
        a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
    (ht : t + 2 ≤ A.card) (r : ℕ) (hr : t + r + 2 ≤ A.card) (hfull : t + r + 2 = A.card)
    {S : State I.left I.right} (hS : F.Admissible (t + r + 2) S)
    (hdonor : S.u = F.p) (htop : S.v F.gap.c = ⊤)
    (hactive : cutoffCut (t + 2) (donorField F) S.profile < S.b) :
    ∃ w : Cell (build I F hroot hA hB hC (t + r) hr).carrier → ExtOrd,
      RespectsSemantics (build I F hroot hA hB hC (t + r) hr).rows w ∧
      (∀ d, w (original I F hroot hA hB hC (t + r) hr d) = S.profile (field I d)) ∧
      ∀ q : Cell (build I F hroot hA hB hC (t + r) hr).carrier → ExtOrd,
        RespectsSemantics (build I F hroot hA hB hC (t + r) hr).rows q →
        q (original I F hroot hA hB hC (t + r) hr (I.rightFace.map F.gap.c)) = ⊤ →
        q (original I F hroot hA hB hC (t + r) hr (I.rightFace.map F.gap.r.1)) = ⊤ →
        ∀ δ, cutoffCut (t + 2) (donorField F) S.profile < δ →
          (∀ d, min (q d) δ = min (w d) δ) →
          ∀ d, q (original I F hroot hA hB hC (t + r) hr (I.leftFace.map d)) = F.p d := by
  obtain ⟨w, hw, ho, a, σ, hσ, hf, hc, hd⟩ :=
    exists_whole_chart I hA hB hC F hroot t ht r hr hfull hS ⟨Sum.inr (Sum.inl F.gap.c), htop⟩
  have hf' (f) : σ ((state F a).profile f) = S.profile f := by rw [state_profile]; exact hf f
  have hcut := map_cutoffCut (donorField F) hσ hf'
  have hlt : cutoffCut (t + 2) (donorField F) (state F a).profile < (state F a).b :=
    lt_of_not_ge fun h => (not_le_of_gt hactive)
      (((hf' cutoffField).symm.trans_le (hσ.mono h)).trans_eq hcut)
  let part : F.Anchor (t + 2) :=
    ⟨(partnerState F (state F a)).profile,
      partnerState_mem F (by rw [state_profile]; exact a.property.1),
      partnerState F (state F a),
      partnerState_admissible F (state_admissible F a) hlt (by omega), rfl⟩
  let eqv := belowEquiv I hA hB hC F hroot t ht (A, t + 2) le_rfl r hr
  have hpos : w (eqv (leafAt I hA hB hC F hroot t ht a)).1 = ⊤ :=
    (hd (leafAt I hA hB hC F hroot t ht a)).trans
      ((congrArg σ ((source_leaf I hA hB hC F hroot t ht a a).trans
        (SourcePrefixRows.cut_refl (sourceGrid_endpoint le_rfl)
          (fun z hz => CanonicalFieldLayer.grid_bound (t + 2) (Field I.left I.right) hz)
          a.val))).trans hc)
  have hneg : w (eqv (leafAt I hA hB hC F hroot t ht part)).1 =
      cutoffCut (t + 2) (donorField F) S.profile := by
    refine (hd (leafAt I hA hB hC F hroot t ht part)).trans ?_
    rw [source_leaf]
    change σ (SourcePrefixRows.cut (LowSeparator.grid (t + 2)) a.val
      (partnerState F (state F a)).profile) = _
    rw [← show (state F a).profile = a.val from state_profile F a, partnerState_profile,
      cut_partner (t + 2) (donorField F) cutoffField
        (by rw [state_profile]; exact a.property.1) hlt]
    exact hcut
  refine ⟨w, hw, ho, fun q hq hc' hr' δ hδ hcap => ?_⟩
  have hsep := separator_of_cap hneg hpos hδ hcap
  refine exact_of_cap_and_top
    (fun d => original I F hroot hA hB hC (t + r) hr (I.leftFace.map d))
    (fun d => (ho (I.leftFace.map d)).trans ((field_donor I S d).trans (congrFun hdonor d)))
    hcap
    (fun d hd => by
      have hm := le_donorMax (donorField F) S.profile (d := .inl d) hd
      change S.u d ≤ _ at hm; rw [hdonor] at hm
      exact (hm.trans (donorMax_le_cutoffCut (t + 2) (donorField F) S.profile)).trans_lt hδ)
    (fun d hd => ?_)
  let origAt (e : I.boundary.below (A, t + 2)) :
      (build I F hroot hA hB hC t ht).carrier.below (A, t + 2) :=
    ⟨original I F hroot hA hB hC t ht e.1, by rw [original_index]; exact e.2⟩
  let pIncl (e : I.right.scheme.below (effC n (t + 2))) : I.boundary.below (A, t + 2) :=
    ⟨I.rightFace.map e.1, I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
      (congrArg Prod.snd (I.rightFace.index e.1)).le.trans (e.2.2.trans (min_le_left _ _))⟩
  let dIncl (e : I.left.scheme.below (effC n (t + 2))) : I.boundary.below (A, t + 2) :=
    ⟨I.leftFace.map e.1, I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
      (congrArg Prod.snd (I.leftFace.index e.1)).le.trans (e.2.2.trans (min_le_left _ _))⟩
  have hm_eq (e : I.boundary.below (A, t + 2)) :
      q (eqv (origAt e)).1 = q (original I F hroot hA hB hC (t + r) hr e.1) :=
    congrArg q (belowEquiv_original I hA hB hC F hroot t ht (A, t + 2) le_rfl r hr e)
  let q₀ := fun x => q (eqv x).1
  have hq₀ : RespectsSemanticsBelow (build I F hroot hA hB hC t ht).rows (A, t + 2) q₀ :=
    pullback I hA hB hC F hroot t ht (A, t + 2) le_rfl r hr (hq.toBelow _)
  have hc₀ : q₀ (origAt (pIncl (F.gap.cC le_rfl))) = ⊤ :=
    (hm_eq (pIncl (F.gap.cC le_rfl))).trans hc'
  have hr₀ : q₀ (origAt (pIncl (F.gap.rC le_rfl))) = ⊤ :=
    (hm_eq (pIncl (F.gap.rC le_rfl))).trans hr'
  have hg₀ : (build I F hroot hA hB hC t ht).carrier.grade
      (origAt (pIncl (F.gap.cC le_rfl))).1 = t + 2 :=
    (congrArg Prod.snd ((original_index I F hroot hA hB hC t ht _).trans
      (I.rightFace.index _))).trans F.gap.c_grade
  obtain ⟨b, σ', hσ', hread⟩ : ∃ b : F.Anchor (t + 2), ∃ σ' : ExtOrd → ExtOrd,
      Witness (gTop (t + 2)) σ' ∧
      ∀ x, σ' (nativeSource I hA hB hC F hroot t ht b x.1) = q₀ x := by
    cases t with
    | zero => exact LowOnlyPaddedTwoReadback.exists_top_chart I F hroot hA hB hC hq₀ ⟨_, hg₀, hc₀⟩
    | succ t => exact LowOnlyPaddedStepChart.exists_top_chart _ _ _ hq₀ ⟨_, hg₀, hc₀⟩
  have hv (e : I.right.scheme.below (effC n (t + 2))) :
      σ' ((state F b).v e.1) = q₀ (origAt (pIncl e)) := by
    have hs := (native_source_original I hA hB hC F hroot t ht b (I.rightFace.map e.1)).trans
      ((congrFun (state_profile F b).symm _).trans
        (field_private I F hroot (LowOnlyRecursiveCoverage.admissible_down F (by omega)
          (by omega) (state_admissible F b)) e.1))
    exact (congrArg σ' hs).symm.trans (hread (origAt (pIncl e)))
  have hs_lf := hread (leafAt I hA hB hC F hroot t ht a)
  have hp_lf := hread (leafAt I hA hB hC F hroot t ht part)
  rw [source_leaf] at hs_lf hp_lf
  have hcmp : σ' (SourcePrefixRows.cut (LowSeparator.grid (X := Field I.left I.right) (t + 2))
      (state F b).profile (partnerState F (state F a)).profile) <
      σ' (SourcePrefixRows.cut (LowSeparator.grid (X := Field I.left I.right) (t + 2))
        (state F b).profile (state F a).profile) := by
    simpa only [state_profile, Family.fields, part] using hp_lf.trans_lt (hsep.trans_eq hs_lf.symm)
  let d' : I.left.scheme.below (effC n (t + 2)) :=
    ⟨d, Finset.subset_univ _, le_min (F.top_grade d hd) (gradeC_le d)⟩
  have htop_d := serving_readback F (state_admissible F b)
    (by rw [state_profile]; exact a.property.1) hlt hσ' hcmp
    ((hv (F.gap.cC le_rfl)).trans hc₀) ((hv (F.gap.rC le_rfl)).trans hr₀) d hd
  have hs_d := (native_source_original I hA hB hC F hroot t ht b (I.leftFace.map d)).trans
    ((congrFun (state_profile F b).symm _).trans (field_donor I (state F b) d))
  exact (hm_eq (dIncl d')).symm.trans
    ((hread (origAt (dIncl d'))).symm.trans ((congrArg σ' hs_d).trans htop_d))

private theorem certificate {K : ℕ} (F : LowOnly.Family I.left I.right K)
    (hroot : ∀ i : Cell I.common.scheme,
      ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
        a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
    {S : State I.left I.right} (hS : F.Admissible A.card S)
    (hdonor : S.u = F.p) (htop : S.v F.gap.c = ⊤)
    (hactive : cutoffCut K (donorField F) S.profile < S.b) :
    ∃ w : Cell (build I F hroot hA hB hC (A.card - 2) (by omega)).carrier → ExtOrd,
      RespectsSemantics (build I F hroot hA hB hC (A.card - 2) (by omega)).rows w ∧
      (∀ d, w (original I F hroot hA hB hC (A.card - 2) (by omega) d) =
        S.profile (field I d)) ∧
      ∀ q : Cell (build I F hroot hA hB hC (A.card - 2) (by omega)).carrier → ExtOrd,
        RespectsSemantics (build I F hroot hA hB hC (A.card - 2) (by omega)).rows q →
        q (original I F hroot hA hB hC (A.card - 2) (by omega) (I.rightFace.map F.gap.c)) = ⊤ →
        q (original I F hroot hA hB hC (A.card - 2) (by omega) (I.rightFace.map F.gap.r.1)) = ⊤ →
        ∀ δ, cutoffCut K (donorField F) S.profile < δ →
          (∀ d, min (q d) δ = min (w d) δ) →
          ∀ d, q (original I F hroot hA hB hC (A.card - 2) (by omega)
            (I.leftFace.map d)) = F.p d := by
  have he : A.card - 2 + 2 = A.card := by omega
  by_cases hK : K = 1
  · subst K
    obtain ⟨w, hw, ho, hr⟩ := rank_certificate I hA hB hC F hroot
      (A.card - 2) (by omega) he (he.symm ▸ hS) hdonor htop
      ((donorMax_le_cutoffCut 1 (donorField F) S.profile).trans_lt hactive)
    exact ⟨w, hw, ho, fun q hq hc hrc δ hδ hcap =>
      hr q hq hc hrc δ ((donorMax_le_cutoffCut 1 (donorField F) S.profile).trans_lt hδ) hcap⟩
  · have hpos := F.gap.K_pos
    obtain ⟨t, rfl⟩ : ∃ t, K = t + 2 := ⟨K - 2, by omega⟩
    have hcard : C.card = n := by
      rw [← I.imageRight, Finset.card_image_of_injective _ I.placeRight.injective,
        Finset.card_univ, Fintype.card_fin]
    have hheight : t + 2 ≤ A.card := F.gap.K_le.trans (hcard ▸ Finset.card_le_card hC.subset)
    have hr : t + (A.card - (t + 2)) = A.card - 2 := by omega
    have hh : t + (A.card - (t + 2)) + 2 = A.card := by omega
    have hres := paired_certificate I hA hB hC t F hroot hheight
      (A.card - (t + 2)) (by omega) hh (hh.symm ▸ hS) hdonor htop hactive
    generalize_proofs hheight' at hres
    generalize hu : t + (A.card - (t + 2)) = u at hheight' hres
    have hueq : u = A.card - 2 := hu.symm.trans hr
    clear hu; subst u; exact hres
end TowerCert

private theorem exists_visible_above {α : LimitStage} (K : ℕ) {x : ExtOrd}
    (hx : x < ofOrd α.1) : ∃ b : ExtOrd, SelfVis K b ∧ x < b ∧ b < ofOrd α.1 := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨ν, rfl⟩
  · exact ⟨ofOrd ((K + 1 : ℕ) : Ordinal.{0}),
      by simpa only [zero_add] using
        (FiniteCoverReceiving.selfVis_ofOrd_add_nat 0 (K + 1)).mono (Nat.le_succ K),
      bot_lt_ofOrd _, ofOrd_lt_ofOrd.mpr (by
        simpa only [zero_add] using
          FiniteCoverReceiving.add_nat_lt_limitStage (α := α) α.2.pos (K + 1))⟩
  · exact (not_top_lt hx).elim
  · exact ⟨ofOrd (ν + ((K + 1 : ℕ) : Ordinal.{0})),
      (FiniteCoverReceiving.selfVis_ofOrd_add_nat ν (K + 1)).mono (Nat.le_succ K),
      ofOrd_lt_ofOrd.mpr (lt_add_of_pos_right ν (by positivity)),
      ofOrd_lt_ofOrd.mpr (FiniteCoverReceiving.add_nat_lt_limitStage (ofOrd_lt_ofOrd.mp hx) _)⟩

theorem receive_of_shared_of_receiving {l m n K : ℕ} {B C : Finset (Fin l)}
    {R : Finset (Finset (Fin l))}
    (I : WholeDonorBoundary.Input Finset.univ B C R m n n)
    (F : LowOnly.Family I.left I.right K)
    (hroot : ∀ i : Cell I.common.scheme,
      ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
        a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
    (hA : 2 ≤ (Finset.univ : Finset (Fin l)).card)
    (hB : B ⊂ Finset.univ) (hC : C ⊂ Finset.univ)
    (hcover : ∀ S ∈ R, S ≠ Finset.univ → S ⊆ B ∨ S ⊆ C)
    {M : Type w} {α : LimitStage} {W : KnightRealization α M}
    (hcons : W.IsExactParentConsistent) (hFC : FiniteCutReceiving W)
    (u : Fin n ↪ M) (pC : StageType α.1 n) (hu : W.eval u = some pC)
    (hCs : pC.scheme = I.right)
    (hshared : F.root.Shared F.p (fun d => pC.label (SemScheme.castCell hCs.symm d)))
    (hc : pC.label (SemScheme.castCell hCs.symm F.gap.c) = ⊤)
    (hr : pC.label (SemScheme.castCell hCs.symm F.gap.r.1) = ⊤)
    (hpbound : ∀ d, F.p d ≠ ⊤ → F.p d < ofOrd α.1) :
    ∃ (v : Fin l ↪ M) (pD : StageType α.1 n),
      I.placeRight.trans v = u ∧ W.eval (I.placeLeft.trans v) = some pD ∧
      I.commonLeft.trans (I.placeLeft.trans v) = I.commonRight.trans u ∧
      ∃ h : pD.scheme = I.left, ∀ d, pD.label d = F.p (SemScheme.castCell h d) := by
  classical
  let v₀ : Cell I.right.scheme → ExtOrd := fun d => pC.label (SemScheme.castCell hCs.symm d)
  have hv₀ : RespectsSemantics I.right.rows v₀ := respects_castCell hCs pC.respects
  let S₀ : State I.left I.right := ⟨F.p, v₀, ⊥⟩
  have hm : donorMax (donorField F) S₀.profile < ofOrd α.1 :=
    (Finset.sup_lt_iff (bot_lt_ofOrd _)).mpr fun f hf => by
      have hd := (Finset.mem_filter.mp hf).2
      rcases f with d | d | d; exact hpbound d hd; exact hd.elim; exact hd.elim
  obtain ⟨b, hbvis, hactive₀, hb⟩ := exists_visible_above K
    (evr_lt_of_lt_limit (limitPart_eq_self_of_isNonSuccessor (Or.inr α.2)) hm K K)
  let S : State I.left I.right := ⟨F.p, v₀, b⟩
  have hadm (j : ℕ) : F.Admissible j S :=
    { lawfulP := F.p_lawful.toBelow _
      lawfulC := hv₀.toBelow _
      shared := hshared
      futureP := fun d _ => SelfVis.mono (show SelfVis (I.left.scheme.grade d) (F.p d)
        from (F.p_lawful.orderly d).symm) (I.left.scheme.grade_pos d)
      futureC := fun d _ => SelfVis.mono (show SelfVis (I.right.scheme.grade d) (v₀ d)
        from (hv₀.orderly d).symm) (I.right.scheme.grade_pos d)
      cutoff := hbvis.mono (min_le_right _ _)
      low := fun _ _ d hd => le_top.trans_eq hd.symm }
  have hactive : cutoffCut K (donorField F) S.profile < S.b := by
    refine (?_ : cutoffCut K (donorField F) S.profile = cutoffCut K (donorField F) S₀.profile).trans_lt
      hactive₀
    unfold cutoffCut; congr 1; refine donorMax_congr _ fun d hd => ?_
    rcases d with d | d | d; rfl; exact hd.elim; exact hd.elim
  let E := LowOnlyPaddedLegal.semScheme I F hroot hA hB hC hcover
  let donor := LowOnlyPaddedLegal.donor I F hroot hA hB hC hcover
  let priv := LowOnlyPaddedLegal.privateFace I F hroot hA hB hC hcover
  obtain ⟨w, hw, ho, hread⟩ :=
    certificate I hA hB hC F hroot (hadm _) rfl hc hactive
  have hdmap (d : Cell I.left.scheme) : donor.map d =
      original I F hroot hA hB hC ((Finset.univ : Finset (Fin l)).card - 2) (by omega)
        (I.leftFace.map d) :=
    face_map I F hroot hA hB hC I.leftFace hB.not_ge _ _ d
  have hcmap (d : Cell I.right.scheme) : priv.map d =
      original I F hroot hA hB hC ((Finset.univ : Finset (Fin l)).card - 2) (by omega)
        (I.rightFace.map d) :=
    face_map I F hroot hA hB hC I.rightFace hC.not_ge _ _ d
  have hwp (d : Cell I.right.scheme) : w (priv.map d) = v₀ d :=
    (congrArg w (hcmap d)).trans ((ho (I.rightFace.map d)).trans
      (field_private I F hroot (hadm _) d))
  let Q : StageType α.1 l := ofRespects α.2 E w hw
  have hvC := LowOnlyPaddedLegal.private_visible I F hroot hA hB hC hcover
  have hsC := LowOnlyPaddedLegal.restrict_private I F hroot hA hB hC hcover
  have hoccC (d : Cell I.right.scheme) :
      toCell E.scheme I.placeRight hvC (SemScheme.castCell hsC.symm d) = priv.map d :=
    LowOnlyPaddedLegal.private_occurrence I F hroot hA hB hC hcover d
  have hp : typeMap I.placeRight Q = some pC := by
    apply (typeMap_eq_some_iff_labels I.placeRight Q pC hvC (hsC.trans hCs.symm)).mpr
    intro i
    have hi : toCell E.scheme I.placeRight hvC i = priv.map (SemScheme.castCell hsC i) :=
      (congrArg (toCell E.scheme I.placeRight hvC) (SemScheme.castCell_castCell_symm hsC.symm i)).symm.trans
        (hoccC (SemScheme.castCell hsC i))
    change truncExt α.1 (w (toCell E.scheme I.placeRight hvC i)) = _
    have hv₀_eq : v₀ (SemScheme.castCell hsC i) =
        pC.label (SemScheme.castCell (hsC.trans hCs.symm) i) := by
      dsimp [v₀]; congr 1
    rw [(congrArg w hi).trans ((hwp _).trans hv₀_eq)]
    exact truncExt_id_of_bound (pC.label_bound _)
  obtain ⟨v, Q', hv, hev, hq, hcap⟩ :=
    FiniteCoverReceiving.finiteCoverReceiving_of_receiving hcons hFC Q I.placeRight u pC hp hu S.b
      (lt_of_le_of_lt bot_le hactive) hb
  let q : Cell E.scheme → ExtOrd := fun d => Q'.label (SemScheme.castCell hq.symm d)
  have hqLaw : RespectsSemantics E.rows q := respects_castCell hq Q'.respects
  let T : StageType α.1 l := ⟨E, q, fun _ => Q'.label_bound _, hqLaw⟩
  rw [(StageType.eq_of_label hq (fun _ => rfl) : Q' = T)] at hev
  have hprivate : typeMap I.placeRight T = some pC := by
    have h := hcons v T I.placeRight hev; rw [hv, hu] at h; exact h.symm
  have hretain (d : Cell I.right.scheme) : q (priv.map d) = v₀ d := by
    have h := (typeMap_eq_some_iff_labels I.placeRight T pC hvC
      (hsC.trans hCs.symm)).mp hprivate (SemScheme.castCell hsC.symm d)
    rw [hoccC d] at h
    refine h.trans ?_; dsimp [v₀]; congr 1
  have hcaps (d : Cell E.scheme) : min (q d) S.b = min (w d) S.b :=
    (hcap (SemScheme.castCell hq.symm d)).trans (FiniteCoverReceiving.min_truncExt_of_lt hb (w d))
  have hdon (d : Cell I.left.scheme) : q (donor.map d) = F.p d :=
    (congrArg q (hdmap d)).trans (hread q hqLaw
      (((congrArg q (hcmap F.gap.c)).symm.trans (hretain F.gap.c)).trans hc)
      (((congrArg q (hcmap F.gap.r.1)).symm.trans (hretain F.gap.r.1)).trans hr)
      S.b hactive hcaps d)
  have hvD := LowOnlyPaddedLegal.donor_visible I F hroot hA hB hC hcover
  have hsD := LowOnlyPaddedLegal.restrict_donor I F hroot hA hB hC hcover
  refine ⟨v, T.restrictFace I.placeLeft hvD, hv, ?_, ?_, hsD, fun d => ?_⟩
  · rw [hcons v T I.placeLeft hev]; exact typeMap_eq_some I.placeLeft T hvD
  · rw [← Function.Embedding.trans_assoc, I.commute, Function.Embedding.trans_assoc, hv]
  · have hocc := LowOnlyPaddedLegal.donor_occurrence I F hroot hA hB hC hcover
      (SemScheme.castCell hsD d)
    change q (toCell E.scheme I.placeLeft hvD d) = _
    exact hocc ▸ hdon (SemScheme.castCell hsD d)

end
end VaughtConjecture.Knight.LowOnlyPaddedModelReceiving

namespace VaughtConjecture.Knight.TopSupportRigidCore

open TypeTower StageType KnightRealization Value ExtOrd TopSupport CellScheme.restrictFace

universe w

variable {α : LimitStage} {M : Type w} {R : KnightRealization α M}

/-! ## Support extension through a literal coface -/

/-! ## Globally top-rigid cores -/

/-- **A finite globally top-rigid core**: on every actual finite cover of `B` (a realized tuple
`C` with `B` as the coordinate face `e`), every admissible top support of the cover's type that
contains every top cell of the face `e` is the whole top set. -/
def RigidCore (R : KnightRealization α M) {k : ℕ} (B : Fin k ↪ M) : Prop :=
  ∀ {m : ℕ} (C : Fin m ↪ M) (c : S α.1 m), R.eval C = some c →
    ∀ (e : Fin k ↪ Fin m), e.trans C = B →
      ∀ H : Set (Cell c.scheme.scheme), Admissible c.scheme.rows c.label H →
        (∀ x : Cell c.scheme.scheme, c.scheme.scheme.scope x ⊆ Finset.univ.image e →
          c.label x = ⊤ → x ∈ H) →
        H = topSet c.label

/-- **The residual acquisition**: a root that is not a globally rigid core has an actual finite
cover with a proper admissible top support containing the root's tops. -/
theorem exists_flexible_cover_of_not_rigidCore {k : ℕ} {B : Fin k ↪ M} (h : ¬ RigidCore R B) :
    ∃ (m : ℕ) (C : Fin m ↪ M) (c : S α.1 m), R.eval C = some c ∧
      ∃ (e : Fin k ↪ Fin m), e.trans C = B ∧
        ∃ H : Set (Cell c.scheme.scheme), Admissible c.scheme.rows c.label H ∧
          (∀ x : Cell c.scheme.scheme, c.scheme.scheme.scope x ⊆ Finset.univ.image e →
            c.label x = ⊤ → x ∈ H) ∧ H ≠ topSet c.label := by
  by_contra hcon
  apply h
  intro m C c hc e he H hH htops
  by_contra hne
  exact hcon ⟨m, C, c, hc, e, he, H, hH, htops, hne⟩

/-! ## Classification of models with globally rigid cores -/

section Classification

variable {M₁ M₂ : Type w} {R₁ : KnightRealization α M₁} {R₂ : KnightRealization α M₂}

/-- The chart invariant: both cores are coordinate faces of the common chart, at the same
coordinates. -/
def CoreChart {k : ℕ} (B₁ : Fin k ↪ M₁) (B₂ : Fin k ↪ M₂)
    (nd : CommonChartNode (A₁ := R₁) (A₂ := R₂)) : Prop :=
  ∃ e : Fin k ↪ Fin nd.arity, e.trans nd.tuple₁ = B₁ ∧ e.trans nd.tuple₂ = B₂

/-- A common chart with the sides exchanged. -/
def swapNode (nd : CommonChartNode (A₁ := R₁) (A₂ := R₂)) :
    CommonChartNode (A₁ := R₂) (A₂ := R₁) :=
  ⟨nd.arity, nd.tuple₂, nd.tuple₁, nd.type, nd.eval₂, nd.eval₁⟩

theorem coreChart_swapNode {k : ℕ} {B₁ : Fin k ↪ M₁} {B₂ : Fin k ↪ M₂}
    {nd : CommonChartNode (A₁ := R₁) (A₂ := R₂)} (h : CoreChart B₁ B₂ nd) :
    CoreChart B₂ B₁ (swapNode nd) := by
  obtain ⟨e, h₁, h₂⟩ := h
  exact ⟨e, h₂, h₁⟩

/-- **One forth step**: a common chart containing both cores extends to one containing a
scheduled point of the first model, by covering it in the first model, receiving the cover's
type over the second side above every proper label, and reading the tops back from rigidity of
the first model's core. -/
theorem exists_step_left_of_receiving (hcons₁ : R₁.IsExactParentConsistent) (hcov₁ :
    R₁.IsInitialSegmentCovering)
    (hcons₂ : R₂.IsExactParentConsistent) (hFC₂ : FiniteCutReceiving R₂) {k : ℕ} {B₁ : Fin k ↪ M₁}
    {B₂ : Fin k ↪ M₂} (r₁ : RigidCore R₁ B₁) (nd : CommonChartNode (A₁ := R₁) (A₂ := R₂))
    (hnd : CoreChart B₁ B₂ nd) (x : M₁) :
    ∃ (next : CommonChartNode (A₁ := R₁) (A₂ := R₂)) (emb : Fin nd.arity ↪ Fin next.arity),
      emb.trans next.tuple₁ = nd.tuple₁ ∧ emb.trans next.tuple₂ = nd.tuple₂ ∧
      (∃ i, next.tuple₁ i = x) ∧ CoreChart B₁ B₂ next := by
  obtain ⟨e, he₁, he₂⟩ := hnd
  by_cases hx : x ∈ Set.range nd.tuple₁
  · obtain ⟨i, hi⟩ := hx
    exact ⟨nd, Function.Embedding.refl _, Function.Embedding.refl_trans _,
      Function.Embedding.refl_trans _, ⟨i, hi⟩, e, he₁, he₂⟩
  -- cover `nd.tuple₁ ⌢ x` in the first model
  obtain ⟨j, s, hs, hsome⟩ := hcov₁ (snoc nd.tuple₁ x hx)
  obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hsome
  set f : Fin nd.arity ↪ Fin (nd.arity + 1 + j) := Fin.castSuccEmb.trans (Fin.castAddEmb j)
    with hfdef
  have hfs : f.trans s = nd.tuple₁ := by
    rw [hfdef, Function.Embedding.trans_assoc, hs, castSuccEmb_trans_snoc]
  have hfP : typeMap f P = some nd.type := by
    have h := hcons₁ s P f hP
    rw [hfs, nd.eval₁] at h
    exact h.symm
  -- receive the cover's type over the second side, above every proper label
  obtain ⟨δ, hδbot, hδα, hδgt⟩ := exists_proper_cutoff P
  obtain ⟨u, Q', hfu, hu, h, hagree⟩ := FiniteCoverReceiving.finiteCoverReceiving_of_receiving
    hcons₂ hFC₂ P f
    nd.tuple₂ nd.type hfP nd.eval₂ δ hδbot hδα
  let Q'' : Cell P.scheme.scheme → ExtOrd := fun d => Q'.label (SemScheme.castCell h.symm d)
  have hQ'' : RespectsSemantics P.scheme.rows Q'' := respects_castCell h Q'.respects
  let T' : S α.1 (nd.arity + 1 + j) := ⟨P.scheme, Q'', fun d => Q'.label_bound _, hQ''⟩
  have hT' : Q' = T' := StageType.eq_of_label h (fun _ => rfl)
  have hoff : ∀ d, P.label d ≠ ⊤ → Q'' d = P.label d := fun d hd =>
    label_eq_of_agree h hagree d (hδgt d hd)
  -- the chart is received literally: both types restrict to `nd.type` along `f`
  have hvf : Finset.univ.image f ∈ P.scheme.scheme.plan :=
    (typeMap_isSome_iff f P).mp (by rw [hfP]; rfl)
  have hsP : P.scheme.restrictFace f hvf = nd.type.scheme :=
    congrArg StageType.scheme (Option.some.inj ((typeMap_eq_some f P hvf).symm.trans hfP))
  have hPr := (typeMap_eq_some_iff_labels f P nd.type hvf hsP).mp hfP
  have hT'f : typeMap f T' = some nd.type := by
    have h := hcons₂ u Q' f hu
    rw [hfu, nd.eval₂, hT'] at h
    exact h.symm
  have hQr := (typeMap_eq_some_iff_labels f T' nd.type hvf hsP).mp hT'f
  have hroot : ∀ i, Q'' (toCell P.scheme.scheme f hvf i) =
      P.label (toCell P.scheme.scheme f hvf i) := fun i => (hQr i).trans (hPr i).symm
  -- rigidity of the first model's core on the cover `s`
  set e' : Fin k ↪ Fin (nd.arity + 1 + j) := e.trans f with he'def
  have he's : e'.trans s = B₁ := by rw [he'def, Function.Embedding.trans_assoc, hfs, he₁]
  have hQP : Q'' = P.label := by
    refine eq_of_unique_admissible hQ''
      (TB := {y | P.scheme.scheme.scope y ⊆ Finset.univ.image e' ∧ P.label y = ⊤}) ?_ hoff ?_
    · intro H hTB hH
      exact r₁ s P hP e' he's H hH (fun y hy hytop => hTB ⟨hy, hytop⟩)
    · rintro y ⟨hy, hytop⟩
      have hyf : P.scheme.scheme.scope y ⊆ Finset.univ.image f := hy.trans fun z hz => by
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
        exact Finset.mem_image_of_mem f (Finset.mem_univ _)
      obtain ⟨i, rfl⟩ := exists_toCell_eq (D := P.scheme.scheme) (f := f) (hr := hvf) hyf
      rw [hroot i]
      exact hytop
  have hQ'P : Q' = P := by
    rw [hT']
    exact StageType.eq_of_label rfl (fun d => congrFun hQP d)
  refine ⟨⟨nd.arity + 1 + j, s, u, P, hP, by rw [← hQ'P]; exact hu⟩, f, hfs, hfu,
    ⟨Fin.castAddEmb j (Fin.last nd.arity), ?_⟩, e', he's, ?_⟩
  · have hlast := congrArg (fun g : Fin (nd.arity + 1) ↪ M₁ => g (Fin.last nd.arity)) hs
    simpa only [Function.Embedding.trans_apply, snoc_apply_last] using hlast
  · rw [he'def, Function.Embedding.trans_assoc, hfu, he₂]

/-- The chart invariant is preserved by density on both sides. -/
theorem restrictedStepSupply_of_receiving (hcons₁ : R₁.IsExactParentConsistent) (hcov₁ :
    R₁.IsInitialSegmentCovering)
    (hFC₁ : FiniteCutReceiving R₁) (hcons₂ : R₂.IsExactParentConsistent)
    (hcov₂ : R₂.IsInitialSegmentCovering) (hFC₂ : FiniteCutReceiving R₂) {k : ℕ} {B₁ : Fin k ↪ M₁}
    {B₂ : Fin k ↪ M₂} (r₁ : RigidCore R₁ B₁) (r₂ : RigidCore R₂ B₂) :
    RestrictedCommonChartStepSupply (A₁ := R₁) (A₂ := R₂) (CoreChart B₁ B₂) := by
  intro nd hnd z
  rcases z with x | y
  · obtain ⟨next, emb, h₁, h₂, hx, hgood⟩ := exists_step_left_of_receiving hcons₁ hcov₁ hcons₂
      hFC₂ r₁ nd hnd x
    exact ⟨⟨⟨next, emb, h₁, h₂, fun _ hx' => (Sum.inl.inj hx') ▸ hx,
      fun _ hy => absurd hy Sum.inl_ne_inr⟩, hgood⟩⟩
  · obtain ⟨next, emb, h₁, h₂, hy, hgood⟩ :=
      exists_step_left_of_receiving hcons₂ hcov₂ hcons₁ hFC₁ r₂ (swapNode nd) (coreChart_swapNode
        hnd) y
    exact ⟨⟨⟨swapNode next, emb, h₂, h₁, fun _ hx => absurd hx Sum.inr_ne_inl,
      fun _ hy' => (Sum.inr.inj hy') ▸ hy⟩, coreChart_swapNode hgood⟩⟩

/-- **Root-preserving classification**: two countable models at the same stage with globally
rigid cores of the same finite type are isomorphic by an isomorphism carrying one core onto the
other coordinatewise. -/
theorem exists_iso_of_rigidCores_of_receiving [Countable M₁] [Countable M₂] [Nonempty M₁]
    [Nonempty M₂] (hcons₁ : R₁.IsExactParentConsistent) (hcov₁ : R₁.IsInitialSegmentCovering)
    (hFC₁ : FiniteCutReceiving R₁) (hcons₂ : R₂.IsExactParentConsistent)
    (hcov₂ : R₂.IsInitialSegmentCovering) (hFC₂ : FiniteCutReceiving R₂) {k : ℕ} {B₁ : Fin k ↪ M₁}
      {B₂ : Fin k ↪ M₂} {b : S α.1 k}
    (h₁ : R₁.eval B₁ = some b) (h₂ : R₂.eval B₂ = some b) (r₁ : RigidCore R₁ B₁)
    (r₂ : RigidCore R₂ B₂) : ∃ e : R₁.Iso R₂, ∀ i, e.1 (B₁ i) = B₂ i :=
  exists_iso_of_restrictedCommonChartStepSupply hcons₁ hcons₂ (CoreChart B₁ B₂)
    ⟨k, B₁, B₂, b, h₁, h₂⟩
    ⟨Function.Embedding.refl _, Function.Embedding.refl_trans _, Function.Embedding.refl_trans _⟩
    (restrictedStepSupply_of_receiving hcons₁ hcov₁ hFC₁ hcons₂ hcov₂ hFC₂ r₁ r₂)

/-- **Classification**: two countable models at the same stage with globally rigid cores of the
same finite type are isomorphic. -/
theorem nonempty_iso_of_rigidCores_of_receiving [Countable M₁] [Countable M₂] [Nonempty M₁]
    [Nonempty M₂] (hcons₁ : R₁.IsExactParentConsistent) (hcov₁ : R₁.IsInitialSegmentCovering)
    (hFC₁ : FiniteCutReceiving R₁) (hcons₂ : R₂.IsExactParentConsistent)
    (hcov₂ : R₂.IsInitialSegmentCovering) (hFC₂ : FiniteCutReceiving R₂) {k : ℕ} {B₁ : Fin k ↪ M₁}
      {B₂ : Fin k ↪ M₂} {b : S α.1 k}
    (h₁ : R₁.eval B₁ = some b) (h₂ : R₂.eval B₂ = some b) (r₁ : RigidCore R₁ B₁)
    (r₂ : RigidCore R₂ B₂) : Nonempty (R₁.Iso R₂) :=
  let ⟨e, _⟩ := exists_iso_of_rigidCores_of_receiving hcons₁ hcov₁ hFC₁ hcons₂ hcov₂ hFC₂ h₁ h₂ r₁
    r₂
  ⟨e⟩

end Classification

end VaughtConjecture.Knight.TopSupportRigidCore

namespace VaughtConjecture.Knight.TopGradeTerminalCounting
open TypeTower StageType KnightRealization Value ExtOrd TopSupport Cardinal
open CellScheme.restrictFace AmalgamationPlan CappedDonor LowOnly
noncomputable section
universe w

section FirstLossHelpers
private theorem admissible_gradeTrunc {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {P : Cell D → ExtOrd} {H : Set (Cell D)} (hH : Admissible sem P H)
    (K : ℕ) : Admissible sem P {d | d ∈ H ∧ D.grade d ≤ K} where
  subset _ hd := hH.subset hd.1
  available d hd Xi₀ hsc hgr := by
    obtain ⟨Xi, hcell, hXi⟩ := hH.available d hd.1 Xi₀ hsc hgr
    refine ⟨Xi, hcell, hXi, ?_⟩
    have hg : D.grade Xi = D.grade Xi₀ := congrArg Prod.snd hcell
    rw [hg, ← hgr]; exact hd.2
  separated c hc a ha d hdtop hdH :=
    hH.separated c hc.1 a ha.1 d hdtop fun hdmem => hdH ⟨hdmem, d.2.2.trans hc.2⟩

private def Full {α : LimitStage} {m : ℕ} (Q : S α.1 m) (H : Set (Cell Q.scheme.scheme))
    {n : ℕ} (f : Fin n ↪ Fin m) : Prop :=
  ∀ x : Cell Q.scheme.scheme, Q.scheme.scheme.scope x ⊆ Finset.univ.image f → Q.label x = ⊤ → x ∈ H

private theorem exists_adjacent_loss {α : LimitStage} {m n : ℕ} (Q : S α.1 m)
    {H : Set (Cell Q.scheme.scheme)} (hsub : H ⊆ topSet Q.label)
    (hne : H ≠ topSet Q.label) (f : Fin n ↪ Fin m)
    (hvis : Finset.univ.image f ∈ Q.scheme.scheme.plan) (hfull : Full Q H f) :
    ∃ (k : ℕ) (g : Fin k ↪ Fin m) (c : Fin m) (hc : c ∉ Set.range g) (e : Fin n ↪ Fin k),
      e.trans g = f ∧ Finset.univ.image g ∈ Q.scheme.scheme.plan ∧
      Finset.univ.image (snoc g c hc) ∈ Q.scheme.scheme.plan ∧
      Full Q H g ∧ ¬ Full Q H (snoc g c hc) := by
  classical
  let faces : Finset (Finset (Fin m)) := Finset.univ.filter fun B =>
    B ∈ Q.scheme.scheme.plan ∧ ∃ (k : ℕ) (g : Fin k ↪ Fin m) (e : Fin n ↪ Fin k),
      e.trans g = f ∧ Finset.univ.image g = B ∧ Full Q H g
  obtain ⟨B, hB, hmax⟩ := faces.exists_max_image Finset.card ⟨_, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hvis, n, f, Function.Embedding.refl _,
      Function.Embedding.refl_trans _, rfl, hfull⟩⟩
  obtain ⟨hBvis, k, g, e, he, hBimage, hBg⟩ := (Finset.mem_filter.mp hB).2
  subst B
  have hneB : Finset.univ.image g ≠ (Finset.univ : Finset (Fin m)) := fun h =>
    hne (Set.Subset.antisymm hsub fun d hd => hBg d (by rw [h]; exact Finset.subset_univ _) hd)
  obtain ⟨C, hC, hsubC, hcardC⟩ :=
    Q.scheme.scheme.isPlan.exists_visible_card_succ_superface hBvis hneB
  obtain ⟨c, hcC, hcB⟩ := Finset.exists_of_ssubset hsubC
  have hc : c ∉ Set.range g := fun ⟨i, hi⟩ => hcB (hi ▸ Finset.mem_image_of_mem g (Finset.mem_univ i))
  have himage : Finset.univ.image (snoc g c hc) = C := by
    rw [image_snoc_univ]
    exact Finset.eq_of_subset_of_card_le (Finset.insert_subset hcC hsubC.subset)
      (by rw [Finset.card_insert_of_notMem hcB, hcardC])
  refine ⟨k, g, c, hc, e, he, hBvis, himage ▸ hC, hBg, fun hfullC => ?_⟩
  have hle := hmax C (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC, k + 1, snoc g c hc,
    e.trans Fin.castSuccEmb,
    by rw [Function.Embedding.trans_assoc, castSuccEmb_trans_snoc, he], himage, hfullC⟩)
  omega

private theorem face_top_grade_le {α : LimitStage} {m n : ℕ} {Q : S α.1 m}
    {f : Fin n ↪ Fin m} {p : S α.1 n}
    (h : typeMap f Q = some p) (d : Cell p.scheme.scheme) (hd : p.label d = ⊤) :
    p.scheme.scheme.grade d ≤ Q.topGrade := by
  have hv : Finset.univ.image f ∈ Q.scheme.scheme.plan := (typeMap_isSome_iff f Q).mp (by rw [h]; rfl)
  have hs : Q.scheme.restrictFace f hv = p.scheme :=
    congrArg StageType.scheme (Option.some.inj ((typeMap_eq_some f Q hv).symm.trans h))
  have htop : Q.label (toCell Q.scheme.scheme f hv (SemScheme.castCell hs.symm d)) = ⊤ :=
    ((typeMap_eq_some_iff_labels f Q p hv hs).mp h (SemScheme.castCell hs.symm d)).trans hd
  have hg : (Q.scheme.restrictFace f hv).scheme.grade (SemScheme.castCell hs.symm d) ≤ Q.topGrade :=
    grade_le_topGrade_of_top htop
  rwa [CappedDonor.castCell_grade hs.symm d] at hg

private theorem exists_enlarged_donor {α : LimitStage} {n k : ℕ} (pR : S α.1 k)
    (e : Fin n ↪ Fin k) (p : S α.1 n) (hep : typeMap e pR = some p) {K : ℕ}
    (hR : ∀ d, pR.label d = ⊤ → pR.scheme.scheme.grade d ≤ K)
    (q : S α.1 (n + 1)) (hq : IsCoface p q)
    (hqK : ∀ d, q.label d = ⊤ → q.scheme.scheme.grade d ≤ K) :
    ∃ Q : S α.1 (k + 1), IsCoface pR Q ∧ typeMap (FixedHeight.extendFace e) Q = some q ∧
      ∀ d, Q.label d = ⊤ → Q.scheme.scheme.grade d ≤ K := by
  have hnk : n ≤ k := by simpa only [Fintype.card_fin] using Fintype.card_le_of_embedding e
  obtain ⟨Q₀, hQ₀cof, hQ₀e⟩ := FixedHeight.pinnedCofaceLift (CanonicalCoatomSupply.supply α.2)
    (k - n) (by omega) pR e p hep q hq
  let HK : Set (Cell Q₀.scheme.scheme) :=
    {d | d ∈ topSet Q₀.label ∧ Q₀.scheme.scheme.grade d ≤ K}
  have hHK : Admissible Q₀.scheme.rows Q₀.label HK :=
    admissible_gradeTrunc (admissible_of_respects Q₀.respects fun _ _ => rfl) K
  obtain ⟨b, hb, _, hβ, hβgt⟩ := Q₀.exists_lawful_cutoff α.2.pos (k + 1)
  have hroot : rootTops hQ₀cof ⊆ HK := by
    rintro c ⟨d, rfl, hd⟩
    refine ⟨hd, ?_⟩
    have h1 : (Q₀.scheme.restrictFace Fin.castSuccEmb hQ₀cof.extendsDomain.visible).scheme.grade
        (SemScheme.castCell hQ₀cof.extendsDomain.restrict.symm d) ≤ K := by
      rw [CappedDonor.castCell_grade]
      exact hR _ ((hQ₀cof.label_cellOf d).symm.trans hd)
    exact h1
  refine ⟨lowerType Q₀ HK hb hβ hβgt hHK, isCoface_lowerType hQ₀cof hb hβ hβgt hHK hroot, ?_, ?_⟩
  · have hv' : Finset.univ.image (FixedHeight.extendFace e) ∈ Q₀.scheme.scheme.plan :=
      (typeMap_isSome_iff _ Q₀).mp (by rw [hQ₀e]; rfl)
    have hs' : Q₀.scheme.restrictFace (FixedHeight.extendFace e) hv' = q.scheme :=
      congrArg StageType.scheme (Option.some.inj ((typeMap_eq_some _ Q₀ hv').symm.trans hQ₀e))
    have hlab := (typeMap_eq_some_iff_labels _ Q₀ q hv' hs').mp hQ₀e
    refine (typeMap_eq_some_iff_labels (FixedHeight.extendFace e)
      (lowerType Q₀ HK hb hβ hβgt hHK) q hv' hs').mpr fun i => ?_
    change lower Q₀.label HK _ (toCell Q₀.scheme.scheme (FixedHeight.extendFace e) hv' i) = _
    by_cases htop : Q₀.label (toCell Q₀.scheme.scheme (FixedHeight.extendFace e) hv' i) = ⊤
    · have hmem : toCell Q₀.scheme.scheme (FixedHeight.extendFace e) hv' i ∈ HK := by
        refine ⟨htop, ?_⟩
        have h2 : (Q₀.scheme.restrictFace (FixedHeight.extendFace e) hv').scheme.grade i ≤ K := by
          rw [← CappedDonor.castCell_grade hs' i]
          exact hqK _ ((hlab i).symm.trans htop)
        exact h2
      rw [lower_of_mem htop hmem]; exact ((hlab i).symm.trans htop).symm
    · rw [lower_of_ne_top htop]; exact hlab i
  · intro d hd
    have hmem : d ∈ topSet (lower Q₀.label HK (ofOrd b)) := hd
    rw [topSet_lower hHK.subset (ofOrd_ne_top _)] at hmem
    exact hmem.2

private theorem rows_castCell {n : ℕ} {X Y : SemScheme n} (h : X = Y) (Sig : Cell X.scheme)
    (d : X.scheme.below (X.scheme.cell Sig))
    (hd : GradedLe (Y.scheme.cell (SemScheme.castCell h d.1))
      (Y.scheme.cell (SemScheme.castCell h Sig))) :
    Y.rows.E (SemScheme.castCell h Sig) ⟨SemScheme.castCell h d.1, hd⟩ = X.rows.E Sig d := by
  subst h; rfl

private theorem gradedLe_castCell {n : ℕ} {X Y : SemScheme n} (h : X = Y) {c c' : Cell X.scheme}
    (hc : GradedLe (X.scheme.cell c) (X.scheme.cell c')) :
    GradedLe (Y.scheme.cell (SemScheme.castCell h c))
      (Y.scheme.cell (SemScheme.castCell h c')) := by
  subst h; exact hc

private theorem scope_toCell_castCell {m n : ℕ} {X : SemScheme n} {f : Fin m ↪ Fin n}
    {hv : Finset.univ.image f ∈ X.scheme.plan} {Z : SemScheme m}
    (h : X.restrictFace f hv = Z) (c : Cell Z.scheme) :
    X.scheme.scope (toCell X.scheme f hv (SemScheme.castCell h.symm c)) =
      (Z.scheme.scope c).image f := by
  subst h; exact (image_scope_restrictFace X.scheme f hv c).symm

private theorem E_congr {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    (sem : Semantics D) {Sig Sig' : Cell D} (h : Sig = Sig') (d : D.below (D.cell Sig))
    (d' : D.below (D.cell Sig')) (hd : d.1 = d'.1) : sem.E Sig d = sem.E Sig' d' := by
  subst h; exact congrArg (sem.E Sig) (Subtype.ext hd)
end FirstLossHelpers

section CommonRoot
variable {α : Ordinal.{0}} {k : ℕ} {pR : S α k} {P C : S α (k + 1)}
  (hP : IsCoface pR P) (hC : IsCoface pR C)

private abbrev rootFace (k : ℕ) : Finset (Fin (k + 1)) := Finset.univ.image Fin.castSuccEmb

private def faceOf :
    P.scheme.scheme.below (rootFace k, (rootFace k).card) ≃
      C.scheme.scheme.below (rootFace k, (rootFace k).card) :=
  commonFace Fin.castSuccEmb hP.extendsDomain.visible hP.extendsDomain.restrict
    Fin.castSuccEmb hC.extendsDomain.visible hC.extendsDomain.restrict (rootFace k).card

private def rootCell (a : P.scheme.scheme.below (rootFace k, (rootFace k).card)) :
    Cell pR.scheme.scheme :=
  SemScheme.castCell hP.extendsDomain.restrict
    ((bP Fin.castSuccEmb hP.extendsDomain.visible (rootFace k).card).symm a).1

private theorem toCell_rootCell (a : P.scheme.scheme.below (rootFace k, (rootFace k).card)) :
    toCell P.scheme.scheme Fin.castSuccEmb hP.extendsDomain.visible
      (SemScheme.castCell hP.extendsDomain.restrict.symm (rootCell hP a)) = a.1 :=
  toCell_belowEquiv_symm_val P.scheme.scheme Fin.castSuccEmb hP.extendsDomain.visible
    (BJ' := (Finset.univ, (rootFace k).card)) (BJ := (rootFace k, (rootFace k).card)) rfl a

private theorem faceOf_val (a : P.scheme.scheme.below (rootFace k, (rootFace k).card)) :
    (faceOf hP hC a).1 = toCell C.scheme.scheme Fin.castSuccEmb hC.extendsDomain.visible
      (SemScheme.castCell hC.extendsDomain.restrict.symm (rootCell hP a)) :=
  commonFace_val Fin.castSuccEmb hP.extendsDomain.visible hP.extendsDomain.restrict
    Fin.castSuccEmb hC.extendsDomain.visible hC.extendsDomain.restrict (rootFace k).card a

private def commonRoot_of_cofaces : LowOnly.CommonRoot P.scheme C.scheme where
  A := rootFace k
  B := rootFace k
  A_mem := hP.extendsDomain.visible
  B_mem := hC.extendsDomain.visible
  card := rfl
  face := faceOf hP hC
  grade a := (commonFace_grade Fin.castSuccEmb hP.extendsDomain.visible
    hP.extendsDomain.restrict Fin.castSuccEmb hC.extendsDomain.visible
    hC.extendsDomain.restrict (rootFace k).card a).symm
  scope a b := by
    have hsP (x) : P.scheme.scheme.scope x.1 =
        (pR.scheme.scheme.scope (rootCell hP x)).image Fin.castSuccEmb := by
      rw [← toCell_rootCell hP x]; exact scope_toCell_castCell hP.extendsDomain.restrict _
    have hsC (x) : C.scheme.scheme.scope (faceOf hP hC x).1 =
        (pR.scheme.scheme.scope (rootCell hP x)).image Fin.castSuccEmb := by
      rw [faceOf_val hP hC x]; exact scope_toCell_castCell hC.extendsDomain.restrict _
    rw [hsP a, hsP b, hsC a, hsC b]
  row a d hd := by
    obtain ⟨d'', hd''⟩ := exists_toCell_eq (D := P.scheme.scheme) (f := Fin.castSuccEmb)
      (hr := hP.extendsDomain.visible) (d.2.1.trans a.2.1)
    have hle : GradedLe (P.scheme.scheme.cell (toCell P.scheme.scheme Fin.castSuccEmb
        hP.extendsDomain.visible d''))
        (P.scheme.scheme.cell (toCell P.scheme.scheme Fin.castSuccEmb hP.extendsDomain.visible
          (SemScheme.castCell hP.extendsDomain.restrict.symm (rootCell hP a)))) := by
      rw [hd'', toCell_rootCell hP a]; exact d.2
    have hle' := (gradedLe_restrictFace_iff P.scheme.scheme Fin.castSuccEmb
      hP.extendsDomain.visible).mpr hle
    let dR : pR.scheme.scheme.below (pR.scheme.scheme.cell (rootCell hP a)) :=
      ⟨SemScheme.castCell hP.extendsDomain.restrict d'',
        gradedLe_castCell hP.extendsDomain.restrict hle'⟩
    have hL : P.scheme.rows.E a.1 d = pR.scheme.rows.E (rootCell hP a) dR :=
      (E_congr P.scheme.rows (toCell_rootCell hP a).symm d _ hd''.symm).trans
        (rows_castCell hP.extendsDomain.restrict _ ⟨d'', hle'⟩
          (gradedLe_castCell hP.extendsDomain.restrict hle')).symm
    have hd3 : ((bP Fin.castSuccEmb hP.extendsDomain.visible (rootFace k).card).symm
        ⟨d.1, d.2.trans a.2⟩).1 = d'' :=
      toCell_injective P.scheme.scheme Fin.castSuccEmb hP.extendsDomain.visible (by
        rw [hd'']
        exact toCell_belowEquiv_symm_val P.scheme.scheme Fin.castSuccEmb hP.extendsDomain.visible
          (BJ' := (Finset.univ, (rootFace k).card)) (BJ := (rootFace k, (rootFace k).card)) rfl _)
    have hrc : rootCell hP ⟨d.1, d.2.trans a.2⟩ =
        SemScheme.castCell hP.extendsDomain.restrict d'' := by unfold rootCell; rw [hd3]
    have hleC := gradedLe_castCell hC.extendsDomain.restrict.symm dR.2
    have hR : C.scheme.rows.E (faceOf hP hC a).1 ⟨(faceOf hP hC ⟨d.1, d.2.trans a.2⟩).1, hd⟩ =
        pR.scheme.rows.E (rootCell hP a) dR :=
      (E_congr C.scheme.rows (faceOf_val hP hC a) _
        ⟨_, gradedLe_of_restrictFace C.scheme.scheme Fin.castSuccEmb hC.extendsDomain.visible hleC⟩
        (by rw [faceOf_val hP hC ⟨d.1, d.2.trans a.2⟩, hrc])).trans
        (rows_castCell hC.extendsDomain.restrict.symm (rootCell hP a) dR hleC)
    exact hL.trans hR.symm

private theorem shared_of_cofaces : (commonRoot_of_cofaces hP hC).Shared P.label C.label := by
  intro a
  change P.label a.1 = C.label (faceOf hP hC a).1
  have hPl := (typeMap_eq_some_iff_labels Fin.castSuccEmb P pR hP.extendsDomain.visible
    hP.extendsDomain.restrict).mp hP
    (SemScheme.castCell hP.extendsDomain.restrict.symm (rootCell hP a))
  have hCl := (typeMap_eq_some_iff_labels Fin.castSuccEmb C pR hC.extendsDomain.visible
    hC.extendsDomain.restrict).mp hC
    (SemScheme.castCell hC.extendsDomain.restrict.symm (rootCell hP a))
  rw [← toCell_rootCell hP a, faceOf_val hP hC a]
  exact hPl.trans hCl.symm
end CommonRoot

section CofaceAttach
private theorem faceMap_eq {m n : ℕ} (D : SemScheme n) (Q : SemScheme m)
    (f : Fin m ↪ Fin n) (hv : Finset.univ.image f ∈ D.scheme.plan)
    (h : D.restrictFace f hv = Q) (d : Cell Q.scheme) :
    SemSchemeBoundaryInput.faceMap D Q f hv h d =
      toCell D.scheme f hv (SemScheme.castCell h.symm d) := by subst Q; rfl

private theorem receive_coface {α : LimitStage} {k K : ℕ} {p : StageType α.1 k}
    {P C : StageType α.1 (k + 1)} (hP : IsCoface p P) (hC : IsCoface p C)
    {M : Type w} {W : KnightRealization α M}
    (hcons : W.IsExactParentConsistent) (hFC : FiniteCutReceiving W)
    (u : Fin (k + 1) ↪ M) (hu : W.eval u = some C)
    (F : LowOnly.Family P.scheme C.scheme K)
    (hF : F.root = commonRoot_of_cofaces hP hC) (hp : F.p = P.label)
    (hc : C.label F.gap.c = ⊤) (hr : C.label F.gap.r.1 = ⊤) :
    ∃ t : Fin (k + 1) ↪ M,
      W.eval t = some P ∧ Fin.castSuccEmb.trans t = Fin.castSuccEmb.trans u := by
  let pair : CoatomPair k := CoatomPair.step Fin.castSuccEmb
  let D : CoatomBoundaryPresentation.Data pair :=
    { left := P.scheme, right := C.scheme, common := p.scheme,
      visibleLeft := hP.extendsDomain.visible, visibleRight := hC.extendsDomain.visible,
      faceLeft := hP.extendsDomain.restrict, faceRight := hC.extendsDomain.restrict }
  let s := CoatomBoundaryPresentation.Data.step D
  let I : WholeDonorBoundary.Input Finset.univ (Finset.univ.erase s.a) (Finset.univ.erase s.b)
      s.plan k (k + 1) (k + 1) :=
    { isPlan := AmalgamatedBoundaryPlan.isPlan s, left := P.scheme, right := C.scheme,
      common := p.scheme, placeLeft := pair.f₁, placeRight := pair.f₂,
      imageLeft := D.input.imageLeft, imageRight := D.input.imageRight,
      commonLeft := Fin.castSuccEmb, commonRight := Fin.castSuccEmb,
      visibleLeft := hP.extendsDomain.visible, visibleRight := hC.extendsDomain.visible,
      faceLeft := hP.extendsDomain.restrict, faceRight := hC.extendsDomain.restrict,
      commute := pair.comm, intersection := D.input.intersection,
      planLeft := (AmalgamatedBoundaryPlan.restrict_left s).trans D.input.planLeft.symm,
      planRight := (AmalgamatedBoundaryPlan.restrict_right s).trans D.input.planRight.symm }
  have hroot : ∀ i : Cell I.common.scheme,
      ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
        a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i := fun i => by
    have hrootcard : (rootFace k).card = k := by
      simp only [rootFace, Finset.card_image_of_injective _ Fin.castSuccEmb.injective,
        Finset.card_univ, Fintype.card_fin]
    have hleft := faceMap_eq P.scheme p.scheme Fin.castSuccEmb
      hP.extendsDomain.visible hP.extendsDomain.restrict i
    have hright := faceMap_eq C.scheme p.scheme Fin.castSuccEmb
      hC.extendsDomain.visible hC.extendsDomain.restrict i
    let a : P.scheme.scheme.below (rootFace k, (rootFace k).card) :=
      ⟨I.shared.f i, by
        change GradedLe (P.scheme.scheme.cell
          (SemSchemeBoundaryInput.faceMap P.scheme p.scheme Fin.castSuccEmb
            hP.extendsDomain.visible hP.extendsDomain.restrict i)) _
        have hi := SemSchemeBoundaryInput.faceMap_index P.scheme p.scheme Fin.castSuccEmb
          hP.extendsDomain.visible hP.extendsDomain.restrict i
        exact hi.symm ▸ ⟨Finset.image_subset_image (Finset.subset_univ _),
          (FiniteCoverReceiving.grade_le_points p.scheme i).trans_eq hrootcard.symm⟩⟩
    have hi : rootCell hP a = i := congrArg (SemScheme.castCell hP.extendsDomain.restrict)
      ((toCell P.scheme.scheme Fin.castSuccEmb hP.extendsDomain.visible).injective
        ((toCell_rootCell hP a).trans hleft))
    rw [hF]; refine ⟨a, rfl, ?_⟩
    change (faceOf hP hC a).1 = I.shared.g i; rw [faceOf_val, hi]; exact hright.symm
  obtain ⟨v, pD, -, heval, htuple, heq, hlabel⟩ :=
    LowOnlyPaddedModelReceiving.receive_of_shared_of_receiving I F hroot
      (by simp) (Finset.erase_ssubset s.ha) (Finset.erase_ssubset s.hb)
      (LowOnlyPaddedPairLift.cover_two_cofaces s rfl rfl rfl)
      hcons hFC u C hu rfl (by rw [hF, hp]; exact shared_of_cofaces hP hC) hc hr
      (fun d hd => by rw [hp] at hd ⊢; exact (P.label_bound d).resolve_right hd)
  have htype : pD = P := StageType.eq_of_label heq fun d =>
    ((hlabel (SemScheme.castCell heq.symm d)).trans (congrFun hp _)).trans
      (congrArg P.label (SemScheme.castCell_castCell_symm heq d))
  exact ⟨I.placeLeft.trans v, htype ▸ heval, htuple⟩
end CofaceAttach

section ResidualReceiving
private theorem receive_of_tail {M : Type w} {α : LimitStage} {W : KnightRealization α M}
    (hcons : W.IsExactParentConsistent) (hFC : FiniteCutReceiving W) {K : ℕ}
    (hcoin : KnightRealization.IsCoinitial {x : W.LabelledExt | x.type.topGrade = K}) (hKpos : 0 < K)
    (hres : ∀ {k : ℕ} (B : Fin k ↪ M), ¬ TopSupportRigidCore.RigidCore W B)
    {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n) (hp : W.eval t = some p)
    (q : S α.1 (n + 1)) (hq : IsCoface p q)
    (hqK : ∀ d, q.label d = ⊤ → q.scheme.scheme.grade d ≤ K) :
    ∃ (y : M) (hy : y ∉ Set.range t), W.eval (snoc t y hy) = some q := by
  obtain ⟨y, ⟨f₀, hf₀, -⟩, hy⟩ := hcoin ⟨n, t, p, hp⟩
  have hyK : y.type.topGrade = K := hy (le_refl y)
  obtain ⟨m, Cov, Q, hQ, e₀, he₀, H, hH, htops, hne⟩ :=
    TopSupportRigidCore.exists_flexible_cover_of_not_rigidCore (hres y.tuple)
  have htyp : typeMap e₀ Q = some y.type := by
    have h := hcons Cov Q e₀ hQ; rw [he₀, y.eval_eq] at h; exact h.symm
  have hQK : Q.topGrade = K := hy (show y ≤ ⟨m, Cov, Q, hQ⟩ from ⟨e₀, he₀, htyp⟩)
  have hve : Finset.univ.image e₀ ∈ Q.scheme.scheme.plan :=
    (typeMap_isSome_iff e₀ Q).mp (by rw [htyp]; rfl)
  have hse : Q.scheme.restrictFace e₀ hve = y.type.scheme :=
    congrArg StageType.scheme (Option.some.inj ((typeMap_eq_some e₀ Q hve).symm.trans htyp))
  obtain ⟨k, g, c, hc, e', he', hvg, hvg', hfull, hnot⟩ :=
    exists_adjacent_loss Q hH.subset hne e₀ hve htops
  let e := f₀.trans e'
  have het : (e.trans g).trans Cov = t := by
    dsimp only [e]
    rw [Function.Embedding.trans_assoc, Function.Embedding.trans_assoc,
      ← Function.Embedding.trans_assoc e' g Cov, he', he₀]; exact hf₀
  obtain ⟨x, hxs, hxtop, hxH⟩ : ∃ x : Cell Q.scheme.scheme,
      Q.scheme.scheme.scope x ⊆ Finset.univ.image (snoc g c hc) ∧ Q.label x = ⊤ ∧ x ∉ H := by
    by_contra hall
    exact hnot fun x hx hxt => by by_contra hxH; exact hall ⟨x, hx, hxt, hxH⟩
  obtain ⟨Θ, _, hΘg, hΘt⟩ := exists_topCell_of_topGrade_pos y.type (hyK ▸ hKpos)
  let a₀ : Cell Q.scheme.scheme := toCell Q.scheme.scheme e₀ hve (SemScheme.castCell hse.symm Θ)
  have ha₀t : Q.label a₀ = ⊤ :=
    ((typeMap_eq_some_iff_labels e₀ Q y.type hve hse).mp htyp _).trans hΘt
  have ha₀g : Q.scheme.scheme.grade a₀ = K := by
    change (Q.scheme.restrictFace e₀ hve).scheme.grade (SemScheme.castCell hse.symm Θ) = K
    rw [CappedDonor.castCell_grade hse.symm Θ, hΘg, hyK]
  have heg : Finset.univ.image e₀ ⊆ Finset.univ.image g := by
    rw [← he']; intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image_of_mem g (Finset.mem_univ _)
  let g₁ : Fin (k + 1) ↪ Fin m := snoc g c hc
  have hgg₁ : Finset.univ.image g ⊆ Finset.univ.image g₁ := by
    intro z hz; obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    rw [← snoc_apply_castSucc g c hc i]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have ha₀s : Q.scheme.scheme.scope a₀ ⊆ Finset.univ.image g :=
    (scope_toCell_subset (D := Q.scheme.scheme) e₀ hve _).trans heg
  have hKcard : K ≤ (Finset.univ.image g₁).card :=
    ha₀g ▸ (CellScheme.grade_le_card_scope _ a₀).trans (Finset.card_le_card (ha₀s.trans hgg₁))
  obtain ⟨Xi₀, hXi₀⟩ := Q.scheme.complete (Finset.univ.image g₁, K)
    (Plan.mem_gradedPlan.mpr ⟨hvg', hKpos, hKcard⟩)
  have hXi₀s : Q.scheme.scheme.scope Xi₀ = Finset.univ.image g₁ := congrArg Prod.fst hXi₀
  have hXi₀g : Q.scheme.scheme.grade Xi₀ = K := congrArg Prod.snd hXi₀
  obtain ⟨o, hocell₀, hoH⟩ := hH.available a₀ (hfull a₀ ha₀s ha₀t) Xi₀
    (by rw [hXi₀s]; exact ha₀s.trans hgg₁) (by rw [ha₀g, hXi₀g])
  have hocell : Q.scheme.scheme.cell o = (Finset.univ.image g₁, K) := hocell₀.trans hXi₀
  have hos : Q.scheme.scheme.scope o = Finset.univ.image g₁ := congrArg Prod.fst hocell
  have hog : Q.scheme.scheme.grade o = K := congrArg Prod.snd hocell
  have hxo : GradedLe (Q.scheme.scheme.cell x) (Q.scheme.scheme.cell o) :=
    hocell ▸ ⟨hxs, hQK ▸ grade_le_topGrade_of_top hxtop⟩
  have hgap (a : Q.scheme.scheme.below (Q.scheme.scheme.cell o)) (ha : a.1 ∈ H) :
      extVisibilityReplace (Q.scheme.rows.E o ⟨x, hxo⟩) K K < Q.scheme.rows.E o a :=
    hog ▸ hH.separated o hoH a ha ⟨x, hxo⟩ hxtop hxH
  have hg : Fin.castSuccEmb.trans g₁ = g := castSuccEmb_trans_snoc g c hc
  let pR : S α.1 k := Q.restrictFace g hvg
  let CT : S α.1 (k + 1) := Q.restrictFace g₁ hvg'
  have hpR : typeMap g Q = some pR := typeMap_eq_some g Q hvg
  have hCT : typeMap g₁ Q = some CT := typeMap_eq_some g₁ Q hvg'
  have hcofCT : IsCoface pR CT := by
    change typeMap Fin.castSuccEmb CT = some pR
    rw [typeMap_trans Fin.castSuccEmb g₁ Q CT hCT, hg]; exact hpR
  have hep : typeMap e pR = some p := by
    rw [typeMap_trans e g Q pR hpR]
    have h := hcons Cov Q (e.trans g) hQ; rw [het, hp] at h; exact h.symm
  obtain ⟨Q', hcofQ', hQ'e, hQ'K⟩ := exists_enlarged_donor pR e p hep
    (fun d hd => (face_top_grade_le hpR d hd).trans_eq hQK) q hq hqK
  obtain ⟨oC, hoC⟩ := exists_toCell_eq (D := Q.scheme.scheme) (f := g₁) (hr := hvg')
    (Finset.subset_of_eq (congrArg Prod.fst hocell))
  obtain ⟨xC, hxC⟩ := exists_toCell_eq (D := Q.scheme.scheme) (f := g₁) (hr := hvg') hxs
  have hxoC : GradedLe (CT.scheme.scheme.cell xC) (CT.scheme.scheme.cell oC) :=
    (gradedLe_restrictFace_iff Q.scheme.scheme g₁ hvg').mpr (by rw [hoC, hxC]; exact hxo)
  have hoCg : CT.scheme.scheme.grade oC = K := by
    change Q.scheme.scheme.grade (toCell Q.scheme.scheme g₁ hvg' oC) = K; rwa [hoC]
  have hb1 := gradedLe_of_restrictFace Q.scheme.scheme g₁ hvg' hxoC
  have hb2 := gradedLe_of_restrictFace Q.scheme.scheme g₁ hvg'
    (GradedLe.refl (CT.scheme.scheme.cell oC))
  let root := commonRoot_of_cofaces hcofQ' hcofCT
  have hroot_sub : root.B ⊆ CT.scheme.scheme.scope oC := fun y _ => by
    change y ∈ Finset.univ.filter (fun j => g₁ j ∈ Q.scheme.scheme.scope
      (toCell Q.scheme.scheme g₁ hvg' oC))
    rw [Finset.mem_filter, hoC, hos]
    exact ⟨Finset.mem_univ _, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have hface_scope (a : Q'.scheme.scheme.below (rootFace k, (rootFace k).card)) :
      Q.scheme.scheme.scope (toCell Q.scheme.scheme g₁ hvg' (root.face a).1) ⊆
        Finset.univ.image g := by
    rw [← image_scope_restrictFace Q.scheme.scheme g₁ hvg' (root.face a).1]
    intro z hz; obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ((root.face a).2.1 hz')
    rw [← hg]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  let gap : LowOnly.SourceGap CT.scheme K :=
    { c := oC, c_grade := hoCg, r := ⟨xC, hxoC⟩
      gap_c := by
        change extVisibilityReplace (Q.scheme.rows.E (toCell Q.scheme.scheme g₁ hvg' oC)
          ⟨toCell Q.scheme.scheme g₁ hvg' xC, hb1⟩) K K <
          Q.scheme.rows.E (toCell Q.scheme.scheme g₁ hvg' oC)
            ⟨toCell Q.scheme.scheme g₁ hvg' oC, hb2⟩
        exact (congrArg (fun z => extVisibilityReplace z K K)
          (E_congr Q.scheme.rows hoC _ _ hxC)).trans_lt
            ((hgap ⟨o, GradedLe.refl _⟩ hoH).trans_eq (E_congr Q.scheme.rows hoC _ _ hoC).symm) }
  let F : LowOnly.Family Q'.scheme CT.scheme K :=
    { root := root, gap := gap,
      p := Q'.label, p_lawful := Q'.respects, top_grade := hQ'K, root_sub := hroot_sub,
      root_gap := fun a ht => by
        have hlab : Q.label (toCell Q.scheme.scheme g₁ hvg' (root.face a).1) = ⊤ :=
          (shared_of_cofaces hcofQ' hcofCT a).symm.trans ht
        have hbelow : GradedLe (Q.scheme.scheme.cell
            (toCell Q.scheme.scheme g₁ hvg' (root.face a).1)) (Q.scheme.scheme.cell o) :=
          hocell ▸ ⟨(hface_scope a).trans hgg₁, hQK ▸ grade_le_topGrade_of_top hlab⟩
        have hb3 : GradedLe (CT.scheme.scheme.cell (root.face a).1) (CT.scheme.scheme.cell oC) :=
          ⟨(root.face a).2.1.trans hroot_sub,
            (root.grade a).symm.trans_le ((hQ'K a.1 ht).trans_eq hoCg.symm)⟩
        have hb3' := gradedLe_of_restrictFace Q.scheme.scheme g₁ hvg' hb3
        change extVisibilityReplace (Q.scheme.rows.E (toCell Q.scheme.scheme g₁ hvg' oC)
          ⟨toCell Q.scheme.scheme g₁ hvg' xC, hb1⟩) K K <
          Q.scheme.rows.E (toCell Q.scheme.scheme g₁ hvg' oC)
            ⟨toCell Q.scheme.scheme g₁ hvg' (root.face a).1, hb3'⟩
        exact (congrArg (fun z => extVisibilityReplace z K K)
          (E_congr Q.scheme.rows hoC _ _ hxC)).trans_lt
            ((hgap ⟨_, hbelow⟩ (hfull _ (hface_scope a) hlab)).trans_eq
              (E_congr Q.scheme.rows hoC _ _ rfl).symm) }
  obtain ⟨v, hv, hroot_eq⟩ := receive_coface hcofQ' hcofCT hcons hFC (g₁.trans Cov)
    ((hcons Cov Q g₁ hQ).trans hCT) F rfl rfl
    (by change Q.label (toCell Q.scheme.scheme g₁ hvg' oC) = ⊤; rw [hoC]; exact mem_topSet.mp (hH.subset hoH))
    (by change Q.label (toCell Q.scheme.scheme g₁ hvg' xC) = ⊤; rw [hxC]; exact hxtop)
  let v₀ : Fin (n + 1) ↪ M := (FixedHeight.extendFace e).trans v
  have hval : W.eval v₀ = some q := (hcons v Q' (FixedHeight.extendFace e) hv).trans hQ'e
  have hprefix : Fin.castSuccEmb.trans v₀ = t := by
    change Fin.castSuccEmb.trans ((FixedHeight.extendFace e).trans v) = t
    rw [← Function.Embedding.trans_assoc, FixedHeight.castSuccEmb_trans_extendFace,
      Function.Embedding.trans_assoc, hroot_eq, ← Function.Embedding.trans_assoc,
      Function.Embedding.trans_assoc, ← Function.Embedding.trans_assoc Fin.castSuccEmb, hg,
      ← Function.Embedding.trans_assoc, het]
  have hy' : v₀ (Fin.last n) ∉ Set.range t := fun ⟨i, hi⟩ =>
    (Fin.castSucc_lt_last i).ne (v₀.injective ((congrArg (fun f : Fin n ↪ M => f i) hprefix).trans hi))
  have heq : snoc t (v₀ (Fin.last n)) hy' = v₀ := by
    ext i; induction i using Fin.lastCases with
    | last => exact snoc_apply_last _ _ _
    | cast j =>
      exact (snoc_apply_castSucc _ _ _ j).trans
        (congrArg (fun f : Fin n ↪ M => f j) hprefix).symm
  exact ⟨v₀ (Fin.last n), hy', heq.symm ▸ hval⟩

private theorem receive_cover_steps_of_tail {M : Type w} {α : LimitStage}
    {W : KnightRealization α M} (hcons : W.IsExactParentConsistent) (hFC : FiniteCutReceiving W)
    {K : ℕ} (hcoin : KnightRealization.IsCoinitial {x : W.LabelledExt | x.type.topGrade = K})
    (hKpos : 0 < K) (hres : ∀ {k : ℕ} (B : Fin k ↪ M), ¬ TopSupportRigidCore.RigidCore W B)
    (r : ℕ) : ∀ {n m : ℕ} (Q : S α.1 m),
      (∀ d, Q.label d = ⊤ → Q.scheme.scheme.grade d ≤ K) →
      ∀ (f : Fin n ↪ Fin m), n + r = m →
      ∀ (t : Fin n ↪ M) (p : S α.1 n), typeMap f Q = some p → W.eval t = some p →
        ∃ u : Fin m ↪ M, f.trans u = t ∧ W.eval u = some Q := by
  induction r with
  | zero =>
    intro n m Q _ f hcard t p hp ht
    subst hcard
    let e : Fin n ≃ Fin (n + 0) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp f.injective)
    let g : Fin (n + 0) ↪ Fin n := e.symm.toEmbedding
    have hfg : f.trans g = Function.Embedding.refl _ := Function.Embedding.ext e.symm_apply_apply
    have hgf : g.trans f = Function.Embedding.refl _ := Function.Embedding.ext e.apply_symm_apply
    refine ⟨g.trans t, by rw [← Function.Embedding.trans_assoc, hfg, Function.Embedding.refl_trans], ?_⟩
    rw [hcons t p g ht]; change typeMap g p = some Q
    rw [typeMap_trans g f Q p hp, hgf, typeMap_refl]
  | succ r ih =>
    intro n m Q hQK f hcard t p hp ht
    have hvis : Finset.univ.image f ∈ Q.scheme.scheme.plan :=
      (typeMap_isSome_iff f Q).mp (by rw [hp]; rfl)
    have hcardF : (Finset.univ.image f).card = n := by
      rw [Finset.card_image_of_injective _ f.injective, Finset.card_univ, Fintype.card_fin]
    have hne : Finset.univ.image f ≠ (Finset.univ : Finset (Fin m)) := fun heq => by
      rw [heq, Finset.card_univ, Fintype.card_fin] at hcardF; omega
    obtain ⟨C, hC, hsub, hcardC⟩ :=
      Q.scheme.scheme.isPlan.exists_visible_card_succ_superface hvis hne
    obtain ⟨c, hcC, hcF⟩ := Finset.exists_of_ssubset hsub
    have hcf : c ∉ Set.range f := fun ⟨i, hi⟩ => hcF (hi ▸ Finset.mem_image_of_mem f (Finset.mem_univ i))
    have himage : Finset.univ.image (snoc f c hcf) = C := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx; obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
        induction i using Fin.lastCases with
        | last => rw [snoc_apply_last]; exact hcC
        | cast j => rw [snoc_apply_castSucc]; exact hsub.subset (Finset.mem_image_of_mem _ (Finset.mem_univ j))
      · rw [hcardC, hcardF, Finset.card_image_of_injective _ (snoc f c hcf).injective,
          Finset.card_univ, Fintype.card_fin]
    let g : Fin (n + 1) ↪ Fin m := snoc f c hcf
    have hvg : Finset.univ.image g ∈ Q.scheme.scheme.plan := himage ▸ hC
    let p' : S α.1 (n + 1) := Q.restrictFace g hvg
    have hp' : typeMap g Q = some p' := typeMap_eq_some g Q hvg
    have hcof : IsCoface p p' := by
      change typeMap Fin.castSuccEmb p' = some p
      rw [typeMap_trans Fin.castSuccEmb g Q p' hp',
        show Fin.castSuccEmb.trans g = f from castSuccEmb_trans_snoc f c hcf]; exact hp
    obtain ⟨y, hy, hq⟩ := receive_of_tail hcons hFC hcoin hKpos hres t p ht p' hcof
      fun d hd => (congrArg Prod.snd (pushGraded_cell Q.scheme.scheme g hvg d)).trans_le (hQK _ hd)
    obtain ⟨u, hgu, hu⟩ := ih Q hQK g (by omega) (snoc t y hy) p' hp' hq
    refine ⟨u, ?_, hu⟩
    rw [← castSuccEmb_trans_snoc f c hcf, Function.Embedding.trans_assoc, hgu, castSuccEmb_trans_snoc]
end ResidualReceiving

private theorem topGrade_le_of_isCoinitial {M : Type w} {α : LimitStage} {R : KnightRealization α M}
    {K : ℕ} (hcoin : KnightRealization.IsCoinitial {x : R.LabelledExt | x.type.topGrade = K})
    (x : R.LabelledExt) : x.type.topGrade ≤ K := by
  obtain ⟨y, hxy, hy⟩ := hcoin x
  exact (LabelledExt.topGrade_mono hxy).trans_eq (hy (le_refl y))

private theorem exists_step_left {α : LimitStage} {M₁ M₂ : Type w}
    {W₁ : KnightRealization α M₁} {W₂ : KnightRealization α M₂}
    (hcons₁ : W₁.IsExactParentConsistent) (hcov₁ : W₁.IsInitialSegmentCovering)
    (hcons₂ : W₂.IsExactParentConsistent) (hFC₂ : FiniteCutReceiving W₂) {K : ℕ}
    (hbound₁ : ∀ x : W₁.LabelledExt, x.type.topGrade ≤ K)
    (hcoin₂ : KnightRealization.IsCoinitial {x : W₂.LabelledExt | x.type.topGrade = K})
    (hKpos : 0 < K) (hres₂ : ∀ {k : ℕ} (B : Fin k ↪ M₂), ¬ TopSupportRigidCore.RigidCore W₂ B)
    (nd : CommonChartNode (A₁ := W₁) (A₂ := W₂)) (x : M₁) :
    ∃ (next : CommonChartNode (A₁ := W₁) (A₂ := W₂)) (emb : Fin nd.arity ↪ Fin next.arity),
      emb.trans next.tuple₁ = nd.tuple₁ ∧ emb.trans next.tuple₂ = nd.tuple₂ ∧
      ∃ i, next.tuple₁ i = x := by
  classical
  by_cases hx : x ∈ Set.range nd.tuple₁
  · obtain ⟨i, hi⟩ := hx
    exact ⟨nd, Function.Embedding.refl _, Function.Embedding.refl_trans _,
      Function.Embedding.refl_trans _, i, hi⟩
  obtain ⟨r, u₀, hg, hsome⟩ := hcov₁ (snoc nd.tuple₁ x hx)
  obtain ⟨P₀, hP₀⟩ := Option.isSome_iff_exists.mp hsome
  let c : W₁.LabelledExt := ⟨_, u₀, P₀, hP₀⟩
  let g : Fin (nd.arity + 1) ↪ Fin c.arity := Fin.castAddEmb r
  let f : Fin nd.arity ↪ Fin c.arity := Fin.castSuccEmb.trans g
  have hfs : f.trans c.tuple = nd.tuple₁ := by
    change (Fin.castSuccEmb.trans g).trans c.tuple = _
    rw [Function.Embedding.trans_assoc, hg, castSuccEmb_trans_snoc]
  have hfp : typeMap f c.type = some nd.type := by
    have h := hcons₁ c.tuple c.type f c.eval_eq; rw [hfs, nd.eval₁] at h; exact h.symm
  have hnm : nd.arity ≤ c.arity := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_embedding f
  obtain ⟨u, hfu, hu⟩ := receive_cover_steps_of_tail hcons₂ hFC₂ hcoin₂ hKpos hres₂
    (c.arity - nd.arity) c.type
    (fun _ hd => (le_csSup c.type.topGrades_bddAbove (grade_mem_topGrades hd)).trans (hbound₁ c))
    f (by omega) nd.tuple₂ nd.type hfp nd.eval₂
  refine ⟨⟨c.arity, c.tuple, u, c.type, c.eval_eq, hu⟩, f, hfs, hfu, g (Fin.last nd.arity), ?_⟩
  simpa only [Function.Embedding.trans_apply, snoc_apply_last] using
    congrArg (fun t : Fin (nd.arity + 1) ↪ M₁ => t (Fin.last nd.arity)) hg

private theorem rigidCore_of_isCoinitial_zero {α : LimitStage} {M : Type w}
    {W : KnightRealization α M}
    (hcoin : KnightRealization.IsCoinitial {x : W.LabelledExt | x.type.topGrade = 0})
    {k : ℕ} (B : Fin k ↪ M) : TopSupportRigidCore.RigidCore W B := by
  intro m C c hc e he H hH ht
  refine Set.Subset.antisymm hH.subset fun d hd => ?_
  have hg : c.scheme.scheme.grade d ≤ 0 :=
    (le_csSup c.topGrades_bddAbove (grade_mem_topGrades (mem_topSet.mp hd))).trans
      (topGrade_le_of_isCoinitial hcoin ⟨m, C, c, hc⟩)
  exact ((c.scheme.scheme.grade_pos d).ne' (Nat.le_zero.mp hg)).elim

private theorem nonempty_iso_of_isCoinitial {α : LimitStage} {M₁ M₂ : Type w}
    [Countable M₁] [Countable M₂] {W₁ : KnightRealization α M₁} {W₂ : KnightRealization α M₂}
    (hM₁ : W₁.IsModel) (hM₂ : W₂.IsModel) {K : ℕ}
    (hcoin₁ : KnightRealization.IsCoinitial {x : W₁.LabelledExt | x.type.topGrade = K})
    (hcoin₂ : KnightRealization.IsCoinitial {x : W₂.LabelledExt | x.type.topGrade = K})
    (hres₁ : ∀ {k : ℕ} (B : Fin k ↪ M₁), ¬ TopSupportRigidCore.RigidCore W₁ B)
    (hres₂ : ∀ {k : ℕ} (B : Fin k ↪ M₂), ¬ TopSupportRigidCore.RigidCore W₂ B) :
    Nonempty (W₁.Iso W₂) := by
  have := hM₁.nonempty
  have := hM₂.nonempty
  have hKpos : 0 < K := by
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · exact (hres₁ (Function.Embedding.ofIsEmpty : Fin 0 ↪ M₁)
        (rigidCore_of_isCoinitial_zero hcoin₁ _)).elim
    · exact hK
  obtain ⟨p₁, hp₁⟩ := exists_eval_empty_of_structural hM₁.consistent hM₁.covering
  obtain ⟨p₂, hp₂⟩ := exists_eval_empty_of_structural hM₂.consistent hM₂.covering
  have hp : p₁ = p₂ := Subsingleton.elim _ _; subst hp
  obtain ⟨e, -⟩ := exists_iso_of_commonChartStepSupply hM₁.consistent hM₂.consistent
    ⟨0, Function.Embedding.ofIsEmpty, Function.Embedding.ofIsEmpty, p₁, hp₁, hp₂⟩
    (fun nd z => by
      rcases z with x | y
      · obtain ⟨next, emb, h₁, h₂, hx⟩ := exists_step_left hM₁.consistent hM₁.covering
          hM₂.consistent (OrdinaryModelReceiving.finiteCutReceiving hM₂)
          (topGrade_le_of_isCoinitial hcoin₁) hcoin₂ hKpos hres₂ nd x
        exact ⟨⟨next, emb, h₁, h₂, fun _ hx' => (Sum.inl.inj hx') ▸ hx,
          fun _ hy => absurd hy Sum.inl_ne_inr⟩⟩
      · obtain ⟨next, emb, h₂, h₁, hy⟩ := exists_step_left hM₂.consistent hM₂.covering
          hM₁.consistent (OrdinaryModelReceiving.finiteCutReceiving hM₁)
          (topGrade_le_of_isCoinitial hcoin₂) hcoin₁ hKpos hres₁
          (TopSupportRigidCore.swapNode nd) y
        exact ⟨⟨TopSupportRigidCore.swapNode next, emb, h₁, h₂,
          fun _ hx => absurd hx Sum.inr_ne_inl, fun _ hy' => (Sum.inr.inj hy') ▸ hy⟩⟩)
  exact ⟨e⟩

theorem countableTerminalFibres_of_growth_results
    (hprolong : ∀ (ρ : Ordinal.{0}), ρ < (aleph 1).ord → ∀ W : TerminalModel ρ,
      ¬ W.1.IsHollow → W.1.HasTopGradeGrowth →
        W.1.ProlongsToIn IsModelClass (blockStage_le_succ ρ))
    (hcompare : ∀ (ρ : Ordinal.{0}), ρ < (aleph 1).ord →
      ∀ W V : TerminalModel ρ,
        W.1.HasTopGradeGrowth → V.1.HasTopGradeGrowth → W.1.IsHollow → V.1.IsHollow →
          Nonempty (W.1.Iso V.1)) : CountableTerminalFibres := by
  intro ρ hρ
  apply Cardinal.mk_le_aleph0_iff.mpr
  let α := blockStage ρ
  have hα : α.1.card ≤ Cardinal.aleph0 :=
    Cardinal.lt_aleph_one_iff.mp (Cardinal.lt_ord.mp (blockLevel_lt_ord_aleph_one hρ))
  haveI : ∀ n, Countable (S α.1 n) := fun n => StageType.countable_S hα n
  let W : TerminalClass ρ → KnightRealization α ℕ := fun q => q.out.1
  have hW : ∀ i, (W i).IsModel := fun q => q.out.2.1
  have heq : ∀ i j, Nonempty ((W i).Iso (W j)) → i = j := fun i j h => by
    by_contra hne
    exact hne (Quotient.out_equiv_out.mp h)
  let P : ((Σ n : ℕ, S α.1 n) ⊕ ℕ ⊕ Unit) → TerminalClass ρ → Prop :=
    Sum.elim
      (fun p i => ∃ B : Fin p.1 ↪ ℕ,
        (W i).eval B = some p.2 ∧ TopSupportRigidCore.RigidCore (W i) B)
      (Sum.elim
        (fun K i => (∀ {k : ℕ} (B : Fin k ↪ ℕ), ¬ TopSupportRigidCore.RigidCore (W i) B) ∧
          KnightRealization.IsCoinitial {x : (W i).LabelledExt | x.type.topGrade = K})
        (fun _ i => (W i).HasTopGradeGrowth ∧ (W i).IsHollow))
  have hcover : ∀ i, ∃ c, P c i := fun i => by
    by_cases hcore : ∃ (k : ℕ) (B : Fin k ↪ ℕ), TopSupportRigidCore.RigidCore (W i) B
    · obtain ⟨k, B, hB⟩ := hcore
      obtain ⟨j, C, hC, hsome⟩ := (hW i).covering B
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsome
      refine ⟨.inl ⟨k + j, b⟩, C, hb, fun D d hd e he H hH ht => ?_⟩
      refine hB D d hd ((Fin.castAddEmb j).trans e)
        (by rw [Function.Embedding.trans_assoc, he, hC]) H hH fun x hx htop => ht x (fun z hz => ?_) htop
      obtain ⟨idx, -, hi⟩ := Finset.mem_image.mp (hx hz)
      exact Finset.mem_image.mpr ⟨Fin.castAddEmb j idx, Finset.mem_univ _, hi⟩
    · rcases (hW i).hasTopGradeGrowth_or_coinitial_constant with hg | ⟨K, hK⟩
      · exact ⟨.inr (.inr ()), hg, by by_contra hn; exact i.out.2.2 (hprolong ρ hρ i.out hn hg)⟩
      · exact ⟨.inr (.inl K), fun B hB => hcore ⟨_, B, hB⟩, hK⟩
  choose c hc using hcover
  refine Function.Injective.countable (f := c) fun i j h => ?_
  have hcj : P (c i) j := h ▸ hc j
  rcases hci : c i with ⟨k, p⟩ | K | ⟨⟩
  · obtain ⟨B₁, h₁, r₁⟩ := hci ▸ hc i
    obtain ⟨B₂, h₂, r₂⟩ := hci ▸ hcj
    have := (hW i).nonempty; have := (hW j).nonempty
    exact heq i j (TopSupportRigidCore.nonempty_iso_of_rigidCores_of_receiving
      (hW i).consistent (hW i).covering (OrdinaryModelReceiving.finiteCutReceiving (hW i))
      (hW j).consistent (hW j).covering (OrdinaryModelReceiving.finiteCutReceiving (hW j))
      h₁ h₂ r₁ r₂)
  · have hi' := hci ▸ hc i
    have hj' := hci ▸ hcj
    exact heq i j (nonempty_iso_of_isCoinitial (hW i) (hW j) hi'.2 hj'.2 hi'.1 hj'.1)
  · have hi' := hci ▸ hc i
    have hj' := hci ▸ hcj
    exact heq i j (hcompare ρ hρ i.out j.out hi'.1 hj'.1 hi'.2 hj'.2)

end
end VaughtConjecture.Knight.TopGradeTerminalCounting
