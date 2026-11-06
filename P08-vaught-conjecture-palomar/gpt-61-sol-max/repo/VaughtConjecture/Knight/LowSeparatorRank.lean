/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.LowSeparatorPaired
import VaughtConjecture.Knight.LadderScalarRendering

/-! # The LOW separator on the rank ladder (grade `K = 1`)

The grade-one regime of newapproach19 new45 §5, kept distinct from the paired-slot regime: the
grade-one base is the actual long rank ladder (`SupportLadderRows`), whose anchors are rank
profiles (`LadderScalarRendering.fieldRank`) and whose spare tips are `SupportLadderRows.leaf`.
No paired-profile leaf is identified with a ladder tip.

* **The rank partner** (`rankPartner`): lower only the cutoff to the non-top maximum `M(s)` and
  re-rank.  Its cutoff rank is `k := rank_s(M(s))` (`rankPartner_cutoff`; `k = 0` for a bottom
  maximum), it agrees with `s`'s rank profile through `k` (`rankPartner_agree`, ties and future
  fields included since ranks are over the complete field type), and the **common rank cut** is
  exactly `k` (`cut_rankPartner`).
* **Strict comparison activates LOW** (`activation_of_cut_lt`, `activation_of_source`): a rank
  profile `a` with `Δ(a, t) < Δ(a, ŝ)` has `Δ(a, t) = k < Δ(a, ŝ)`, so every non-top donor rank
  is at most `k` and the cutoff rank exceeds `k`; for the actual source `a'` with ranks `a`,
  every non-top donor field lies strictly below the cutoff: `M(a') < a' b`.
* **The two-spare-tip separator on the actual ladder** (`ladder_separator`,
  `ladder_readback`): a lawful ladder section reading the partner's tip strictly below `s`'s tip
  is served by one anchor with a positive monotone table (`Lawful.exists_shape`); the tip
  readings are the table at the two common rank cuts, so LOW is active at the serving source,
  and a monotone rank table reading the private owner and low source as `⊤` reads every
  designated donor top as `⊤` (`readout_image`).
* **The selected readings** (`render_tip_partner`, `render_tip_self`): the ceiling-filled
  rendering of `s` reads the partner's tip at `M(s)` and its own tip at the ceiling, a strict
  comparison whenever the ceiling exceeds the cutoff.

The family section instantiates the activation and readback on KVC's `LowOnly.Family` at
`K = 1`.  No physical installation, bountifulness or model application is asserted. -/

namespace VaughtConjecture.Knight.LowSeparatorRank

open  Value  LadderScalarRendering FiniteProfileControllers SupportLadderRows
  LowSeparator

noncomputable section

section

variable {X : Type*} [Fintype X] (N : X → Prop) [DecidablePred N] (b : X)

/-- The rank partner: only the cutoff is lowered, to the non-top maximum. -/
def rankPartner [DecidableEq X] s :=
  Function.update s b (donorMax N s)

theorem rankPartner_apply_self [DecidableEq X] s :
    rankPartner N b s b = donorMax N s := Function.update_self b _ s

theorem rankPartner_apply_of_ne [DecidableEq X] s {d} (hdb : d ≠ b) :
    rankPartner N b s d = s d := Function.update_of_ne hdb _ s

/-- The cutoff rank of the partner: the rank of the non-top maximum in `s`. -/
def rankCut s := LadderScalarRendering.rank (values s) (donorMax N s)

theorem donorMax_mem_values {s} (hne : donorMax N s ≠ ⊥) :
    donorMax N s ∈ values s := by
  rcases donorMax_cases N s with h | ⟨d, -, hd⟩
  · exact absurd h hne
  · exact mem_values.mpr ⟨hne, d, hd⟩

theorem rankCut_le s : rankCut N s ≤ Fintype.card X :=
  (rank_le_card _ _).trans (values_card_le s)

variable {s : X → ExtOrd} (hlt : donorMax N s < s b)

include hlt in
def sb_mem_values :=
  mem_values.mpr ⟨ne_of_gt (bot_le.trans_lt hlt), b, rfl⟩

local notation "fieldRank₀₀" => fieldRank s

local notation "rankCut₀" => rankCut N s

include hlt in
theorem rankCut_lt_cutoff : rankCut₀ < fieldRank₀₀ b :=
  rank_strict (sb_mem_values N b hlt) hlt

section

variable [DecidableEq X]

local notation "values₀" => values (rankPartner N b s)

include hlt in
/-- Below the old cutoff, the partner's inventory is `s`'s. -/
theorem values_rankPartner_below :
    ∀ y, y < s b → (y ∈ values₀ ↔ y ∈ values s) := by
  intro y hy
  rw [mem_values, mem_values]
  constructor
  · rintro ⟨hz, d, hd⟩
    refine ⟨hz, ?_⟩
    by_cases hdb : d = b
    · rw [hdb, rankPartner_apply_self N b] at hd
      obtain ⟨_, e, he⟩ := mem_values.mp (donorMax_mem_values N (hd ▸ hz))
      exact ⟨e, he.trans hd⟩
    · grind [rankPartner_apply_of_ne]
  · aesop (add safe apply [rankPartner_apply_of_ne])

local notation "fieldRank₀" => fieldRank (rankPartner N b s)

include hlt in
/-- **The partner's cutoff rank is `k`.** -/
theorem rankPartner_cutoff : fieldRank₀ b = rankCut₀ := by
  unfold fieldRank rankCut
  rw [rankPartner_apply_self N b]
  exact rank_congr_below (values_rankPartner_below N b hlt) hlt

include hlt in
/-- **Rank-prefix agreement through `k`**, on every complete field. -/
theorem rankPartner_agree :
    Agree (fieldRank₀₀) (fieldRank₀) (rankCut₀) := by
  intro d
  by_cases hdb : d = b
  · rw [hdb, rankPartner_cutoff N b hlt, min_self,
      min_eq_right (rankCut_lt_cutoff N b hlt).le]
  · unfold fieldRank
    rw [rankPartner_apply_of_ne N b s hdb]
    by_cases hsd : s d < s b
    · rw [rank_congr_below (values_rankPartner_below N b hlt) hsd]
    · have h1 : rankCut₀ ≤ LadderScalarRendering.rank (values s) (s d) :=
        (rankCut_lt_cutoff N b hlt).le.trans (rank_mono _ (not_lt.mp hsd))
      have h2 : rankCut₀ ≤ LadderScalarRendering.rank (values₀) (s d) := by
        have h := rank_mono values₀ (hlt.le.trans (not_lt.mp hsd))
        have hk : LadderScalarRendering.rank values₀ (donorMax N s) =
            rankCut₀ := by
          grind [rankPartner_cutoff, fieldRank, rankPartner_apply_self]
        rw [← hk]
        exact h
      rw [min_eq_right h1, min_eq_right h2]

include hlt in
/-- **The common rank cut is `k`.** -/
theorem cut_rankPartner {H} (hH : Fintype.card X ≤ H) :
    cut H (fieldRank₀₀) (fieldRank₀) = rankCut₀ := by
  apply le_antisymm
  · apply le_of_not_gt
    intro hgt
    have hag := agree_cut H (fieldRank₀₀) (fieldRank₀) b
    rw [rankPartner_cutoff N b hlt, ] at hag
    have h1 := rankCut_lt_cutoff N b hlt
    have : rankCut₀ <
        min (fieldRank₀₀ b) (cut H (fieldRank₀₀) (fieldRank₀)) :=
      lt_min h1 hgt
    omega
  · exact le_cut ((rankCut_le N s).trans hH) (rankPartner_agree N b hlt)

include hlt in
/-- The ultrametric identity on rank cuts: a strict comparison pins the partner cut at `k`. -/
theorem cut_rankPartner_eq_of_lt {H} (hH : Fintype.card X ≤ H) {a}
    (h : cut H a (fieldRank₀) < cut H a (fieldRank₀₀)) :
    cut H a (fieldRank₀) = rankCut₀ ∧
      rankCut₀ < cut H a (fieldRank₀₀) := by
  have hst := cut_rankPartner N b hlt hH
  have h1 := cut_triangle H a (fieldRank₀₀) (fieldRank₀)
  have h2 := cut_triangle H (fieldRank₀₀) a fieldRank₀
  
  rw [cut_symm H (fieldRank₀₀) a] at h2
  omega

include hlt in
/-- **Strict comparison activates LOW at the rank level**: every non-top donor rank of the
serving profile is at most `k`, and its cutoff rank exceeds `k`. -/
theorem activation_of_cut_lt {H} (hH : Fintype.card X ≤ H) {a}
    (h : cut H a (fieldRank₀) < cut H a (fieldRank₀₀)) :
    (∀ d, N d → a d ≤ rankCut₀) ∧ rankCut₀ < a b := by
  obtain ⟨-, hu⟩ := cut_rankPartner_eq_of_lt N b hlt hH h
  have hag := agree_cut H a (fieldRank₀₀)
  refine ⟨fun d hd => ?_, ?_⟩
  · have hsd : fieldRank₀₀ d ≤ rankCut₀ := rank_mono _ (le_donorMax N s hd)
    have := hag d
    omega
  · have := hag b
    have hb := rankCut_lt_cutoff N b hlt
    omega

end

/-- **Activation at the actual source**: a source whose rank profile has every non-top donor
rank at most `k` and cutoff rank above `k` has its non-top maximum strictly below its cutoff. -/
theorem activation_of_source {k} a
    (hlow : ∀ d, N d → fieldRank a d ≤ k) (hb : k < fieldRank a b) :
    donorMax N a < a b := by
  have hab : ⊥ < a b := by
    apply bot_lt_iff_ne_bot.mpr
    intro hz
    have : fieldRank a b = 0 := by
      unfold fieldRank
      rw [hz]
      exact rank_bot (bot_not_values)
    omega
  apply (Finset.sup_lt_iff hab).mpr
  intro d hd
  have hd'  := (Finset.mem_filter.mp hd).2
  by_contra hn
  have := rank_mono (values a) (not_lt.mp hn)
  have := hlow d hd'
  unfold fieldRank at *
  omega

end

/-! ## The two-spare-tip separator on the actual ladder -/


/-! ## The selected rendered readings -/

section

variable {X : Type*} [Fintype X] (N : X → Prop) [DecidablePred N] (b : X)
  {Q : Type*} [Finite Q] {H : ℕ} (profile : Q → X → ℕ) (hH : 0 < H)

omit [Finite Q] in
include hH in
/-- The rendering of `s` reads the partner's tip at the non-top maximum. -/
theorem render_tip_partner [DecidableEq X] {s} (hlt : donorMax N s < s b)
    (hHX : Fintype.card X ≤ H) {qs qt} (hqs : profile qs = fieldRank s)
    (hqt : profile qt = fieldRank (rankPartner N b s)) C :
    render profile qs s C (leaf hH qt) = donorMax N s := by
  unfold render
  rw [image, index_leaf, hqs, hqt, cut_rankPartner N b hlt hHX]
  by_cases hM : donorMax N s = ⊥
  · unfold rankCut
    rw [hM, rank_bot (bot_not_values), level_zero]
  · exact level_rank (donorMax_mem_values N hM) C

omit [DecidablePred N] [Finite Q] in
include hH in
/-- The rendering of `s` reads its own tip at the ceiling. -/
theorem render_tip_self s (hHX : Fintype.card X < H) qs C :
    render profile qs s C (leaf hH qs) = C := by
  
  unfold render
  rw [image, index_leaf, cut_refl, LadderScalarRendering.level,
    ite_eq_left ((values_card_le s).trans_lt hHX)]

end

/-! ## The family instance at `K = 1` -/

section

open LowOnly

variable {n : ℕ} {P C : SemScheme n} (F : LowOnly.Family P C 1)

/-- At grade one, the LOW bound of an active admitted state is the plain minimum of the private
owner and low source. -/
theorem low_min_le {A} (hA : F.Admissible 1 A) (hm : F.maximum A < A.b)
    d (hd : F.p d = ⊤) : min (A.v F.gap.c) (A.v F.gap.r.1) ≤ A.u d := by
  have hlow := hA.low le_rfl hm d hd
  change max A.b (min (A.v F.gap.c) (extVisibilityReplace (A.v F.gap.r.1) 1 1)) ≤ A.u d at hlow
  have hvis : SelfVis 1 (A.v F.gap.r.1) := by
    have h := (hA.lawfulC.orderly (CellScheme.below.mono (F.gap.domLe le_rfl) F.gap.r)).symm
    change SelfVis (C.scheme.grade F.gap.r.1) (A.v F.gap.r.1) at h
    exact h.mono (C.scheme.grade_pos _)
  rw [evr_eq_self_of_selfVis hvis] at hlow
  exact (le_max_right _ _).trans hlow



