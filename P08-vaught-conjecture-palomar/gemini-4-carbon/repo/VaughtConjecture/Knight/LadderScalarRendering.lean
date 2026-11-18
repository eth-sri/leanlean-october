/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LongGuardRows
public import VaughtConjecture.Knight.FiniteProfileControllers
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

namespace VaughtConjecture.Knight.SupportLadderRows

open Transform Value ExtOrd FiniteProfileControllers

/-- The exact source code used by a rung, including its long diagonal. -/
noncomputable def source (t i : ℕ) : ExtOrd :=
  if t ≤ 1 then SlotControllerFamily.value (2 * min i t - 1)
  else LongGuardRows.source (2 * t - 3) (2 * min i t - 1)

theorem source_visible (t i : ℕ) : SelfVis 1 (source t i) := by
  unfold source
  split_ifs
  · exact SlotControllerFamily.value_visible _
  · exact LongGuardRows.source_visible _ _

theorem source_coded (t i : ℕ) : IsCodedLabel 1 (source t i) := by
  unfold source
  split_ifs
  · exact SlotControllerFamily.value_coded _
  · exact LongGuardRows.source_coded _ _

theorem source_le_iff (t i j : ℕ) :
    source t i ≤ source t j ↔ min i t ≤ min j t := by
  unfold source
  split_ifs with ht
  · rw [SlotControllerFamily.value_le_iff]
    omega
  · rw [LongGuardRows.source_le_iff]
    omega

theorem source_mono (t : ℕ) : Monotone (source t) :=
  fun _ _ h => (source_le_iff _ _ _).mpr (min_le_min_right _ h)

@[simp] theorem source_zero (t : ℕ) : source t 0 = ⊥ := by
  simp [source, SlotControllerFamily.value]

theorem source_bot_iff (t i : ℕ) : source t i = ⊥ ↔ min i t = 0 := by
  have h := source_le_iff t i 0
  simpa only [source_zero, le_bot_iff, Nat.zero_min, Nat.le_zero] using h

theorem source_floor_bot_iff (t i : ℕ) :
    blockFloor (source t i) = ⊥ ↔ source t i = ⊥ := by
  unfold source LongGuardRows.source SlotControllerFamily.value
  split_ifs <;>
    simp [LongGuardRows.endpoint,
      blockFloor_ofOrd, SeparatedGradeOne.band]

/-- Adjacent actual rungs share the decisive short/long source block. -/
theorem predecessor_block {t : ℕ} (ht : 2 ≤ t) :
    blockFloor (source t (t - 1)) = blockFloor (source t t) := by
  have h1 : ¬t ≤ 1 := by omega
  have h2 : 2 * min (t - 1) t - 1 = 2 * t - 3 := by omega
  have h3 : ¬2 * min t t - 1 ≤ 2 * t - 3 := by omega
  have h4 : 2 * t - 3 ≠ 0 := by omega
  simp only [source, ite_eq_right h1, h2, LongGuardRows.source,
    le_refl, ite_true, ite_eq_right h3, SlotControllerFamily.value,
    ite_eq_right h4, SeparatedGradeOne.band_floor,
    LongGuardRows.endpoint, blockFloor_ofOrd, limitPart_code]

/-- Positive visible tables have faithful locality at every rung. The
source-block test includes the long diagonal, not just bounded commutation. -/
theorem transforms_positive {Y : Type*} [Finite Y] (a : Y → ℕ) (t : ℕ)
    (f : ℕ → ExtOrd) (hf : Monotone f) (h0 : f 0 = ⊥)
    (hv : ∀ i, SelfVis 1 (f i)) (hp : ∀ i, 0 < i → i ≤ t → f i ≠ ⊥) :
    TransformsTo (fun _ : Y => 1) (fun d => source t (a d))
      (fun d => f (min (a d) t)) := by
  apply LongGuardRows.transforms_of_visible_table
    (fun _ => source_visible _ _) (fun _ => hv _)
  · intro d e hde
    exact hf ((source_le_iff _ _ _).mp hde)
  · intro d hd
    rw [(source_bot_iff _ _).mp hd, h0]
  · intro d e hde hd
    have hz : min (a d) t = 0 := by
      by_contra hn
      exact hp _ (Nat.pos_of_ne_zero hn) (min_le_right _ _) hd
    have hs : source t (a d) = ⊥ := (source_bot_iff _ _).mpr hz
    rw [hs, blockFloor_bot] at hde
    have he := (source_floor_bot_iff _ _).mp hde.symm
    rw [(source_bot_iff _ _).mp he, h0]

theorem source_min (t i : ℕ) : source t (min i t) = source t i := by
  simp only [source, min_assoc, min_self]

variable {X Q : Type*} {H : ℕ} {profile : Q → X → ℕ}

/-- Every rank has a separate rung, even when no original field uses it.
Shadows are separate occurrences, including rank-zero shadows. -/
abbrev Point (H : ℕ) (X Q : Type*) := Q × (Fin H ⊕ X)

def parent (v : Point H X Q) : Q := v.1

def ceiling (profile : Q → X → ℕ) (v : Point H X Q) : ℕ :=
  match v.2 with
  | .inl i => i.val + 1
  | .inr d => profile v.1 d

def rung (a : Q) (i : Fin H) : Point H X Q := (a, .inl i)
def shadow (a : Q) (d : X) : Point H X Q := (a, .inr d)
def leaf (hH : 0 < H) (a : Q) : Point H X Q := rung a ⟨H - 1, by omega⟩

noncomputable def index (profile : Q → X → ℕ) (a : Q) (v : Point H X Q) : ℕ :=
  min (cut H (profile a) (profile (parent v))) (ceiling profile v)

noncomputable def row (profile : Q → X → ℕ) (c v : Point H X Q) : ExtOrd :=
  source (ceiling profile c) (index profile (parent c) v)

noncomputable def image (profile : Q → X → ℕ) (a : Q) (f : ℕ → ExtOrd)
    (v : Point H X Q) : ExtOrd := f (index profile a v)

def Lawful (profile : Q → X → ℕ) (q : Point H X Q → ExtOrd) : Prop :=
  (∀ v, SelfVis 1 (q v)) ∧ ∀ c,
    TransformsTo (fun _ : Point H X Q => 1) (row profile c) (fun v => min (q v) (q c))

theorem ceiling_le (hbound : ∀ a d, profile a d ≤ H) (v : Point H X Q) :
    ceiling profile v ≤ H := by
  rcases v with ⟨a, i | d⟩
  · exact i.isLt
  · exact hbound a d

theorem index_le (a : Q) (v : Point H X Q) : index profile a v ≤ H :=
  (min_le_left _ _).trans (cut_le _ _ _)

@[simp] theorem index_rung (a : Q) (i : Fin H) :
    index profile a (rung a i) = i.val + 1 := by
  simp only [index, rung, parent, ceiling, cut_refl,
    min_eq_right (show i.val + 1 ≤ H from i.isLt)]

@[simp] theorem ceiling_leaf (hH : 0 < H) (a : Q) :
    ceiling profile (leaf (X := X) hH a) = H := by
  change H - 1 + 1 = H
  omega

@[simp] theorem index_leaf (hH : 0 < H) (a b : Q) :
    index profile a (leaf (X := X) hH b) = cut H (profile a) (profile b) := by
  rw [index, ceiling_leaf]
  exact min_eq_left (cut_le _ _ _)

theorem index_diagonal (hbound : ∀ a d, profile a d ≤ H) (c : Point H X Q) :
    index profile (parent c) c = ceiling profile c := by
  rw [index, cut_refl, min_eq_right (ceiling_le hbound c)]

/-- Whole-coordinate agreement includes every unused rung and every shadow. -/
theorem index_agreement (a b : Q) (v : Point H X Q) :
    min (index profile a v) (cut H (profile a) (profile b)) =
      min (index profile b v) (cut H (profile a) (profile b)) := by
  unfold index
  calc
    _ = min (min (cut H (profile a) (profile (parent v)))
        (cut H (profile a) (profile b))) (ceiling profile v) := by ac_rfl
    _ = min (min (cut H (profile b) (profile (parent v)))
        (cut H (profile a) (profile b))) (ceiling profile v) := by rw [cross_agreement]
    _ = _ := by ac_rfl

theorem image_cap_eq (a : Q) {f : ℕ → ExtOrd} (hf : Monotone f)
    (c v : Point H X Q) :
    min (image profile a f v) (image profile a f c) =
      f (min (index profile (parent c) v) (index profile a c)) := by
  rw [image, image, ← hf.map_min]
  change f (min (index profile a v) (min _ _)) = _
  rw [← min_assoc, index_agreement, min_assoc]
  rfl

variable [Finite X] [Finite Q]

/-- A positive ordered scalar table receives every physical rung at its own
cap, including all long diagonals and all unused ranks. -/
theorem image_lawful (a : Q) (f : ℕ → ExtOrd) (hf : Monotone f) (h0 : f 0 = ⊥)
    (hv : ∀ i, SelfVis 1 (f i)) (hp : ∀ i, 0 < i → i ≤ H → f i ≠ ⊥) :
    Lawful (H := H) profile (image profile a f) := by
  refine ⟨fun _ => hv _, ?_⟩
  intro c
  have he := funext (image_cap_eq (profile := profile) a hf c)
  rw [he]
  let e := index profile a c
  have het : e ≤ ceiling profile c := min_le_right _ _
  by_cases hz : e = 0
  · have hzero : (fun v : Point H X Q => f (min (index profile (parent c) v) e)) =
        fun _ => ⊥ := by simp [hz, h0]
    change TransformsTo _ _ (fun v => f (min (index profile (parent c) v) e))
    rw [hzero]
    exact TransformsTo.to_bot _
  · have ht := transforms_positive (index (H := H) profile (parent c)) (ceiling profile c)
        (fun i => f (min i e))
        (fun _ _ h => hf (min_le_min_right _ h)) (by simpa using h0)
        (fun _ => hv _) (fun i hi _ => hp _ (by omega) ((min_le_right _ _).trans (index_le a c)))
    change TransformsTo _ (fun v => source (ceiling profile c) (index profile (parent c) v))
      (fun v => f (min (index profile (parent c) v) e))
    simpa only [min_assoc, min_eq_right het] using ht

omit [Finite X] [Finite Q] in
theorem row_parent (hbound : ∀ a d, profile a d ≤ H) (hH : 0 < H)
    (c : Point H X Q) :
    row profile c (leaf hH (parent c)) = row profile c c := by
  rw [row, row, index_leaf, cut_refl, index_diagonal hbound]
  have h := source_min (ceiling profile c) H
  rw [min_eq_right (ceiling_le hbound c)] at h
  exact h.symm

omit [Finite X] [Finite Q] in
/-- Locality at the auxiliary itself bounds it by its actual parent leaf. -/
theorem Lawful.le_parent {q : Point H X Q → ExtOrd} (hq : Lawful profile q)
    (hbound : ∀ a d, profile a d ≤ H) (hH : 0 < H) (c : Point H X Q) :
    q c ≤ q (leaf hH (parent c)) := by
  obtain ⟨g, σ, _, _, _, _, _, hr⟩ := hq.2 c
  apply min_eq_right_iff.mp
  calc
    min (q (leaf hH (parent c))) (q c) =
        min (σ (row profile c (leaf hH (parent c)))) (g 1) := hr _
    _ = min (σ (row profile c c)) (g 1) := by rw [row_parent hbound hH]
    _ = q c := by simpa only [min_self] using (hr c).symm

omit [Finite X] [Finite Q] in
/-- An actual long rung forbids a zero predecessor and a positive diagonal.
No field need occupy either rank. -/
theorem Lawful.predecessor_bot {q : Point H X Q → ExtOrd} (hq : Lawful profile q)
    (a : Q) {i : ℕ} (hi : 0 < i) (hiH : i < H)
    (hz : q (rung a ⟨i - 1, by omega⟩) = ⊥) : q (rung a ⟨i, hiH⟩) = ⊥ := by
  let c : Point H X Q := rung a ⟨i, hiH⟩
  let d : Point H X Q := rung a ⟨i - 1, by omega⟩
  have hb : blockFloor (row profile c d) = blockFloor (row profile c c) := by
    change blockFloor (source (i + 1) (index profile a d)) =
      blockFloor (source (i + 1) (index profile a c))
    dsimp only [d, c]
    rw [index_rung, index_rung]
    have hi' : i - 1 + 1 = i := by omega
    rw [hi']
    simpa only [Nat.add_sub_cancel] using predecessor_block (t := i + 1) (by omega)
  have hd : min (q d) (q c) = ⊥ := by rw [show q d = ⊥ from hz, min_bot_left]
  have hh := LongGuardRows.bottom_of_same_block (hq.2 c) hb hd
  simpa only [min_self] using hh

omit [Finite X] in
/-- Extract a scalar chart from an actual maximal leaf of an arbitrary lawful
section. The leaf's faithful witness is used directly, including its long row. -/
theorem Lawful.exists_shape [Nonempty Q] {q : Point H X Q → ExtOrd}
    (hq : Lawful profile q) (hbound : ∀ a d, profile a d ≤ H) (hH : 0 < H) :
    ∃ a f, Monotone f ∧ f 0 = ⊥ ∧ (∀ i, SelfVis 1 (f i)) ∧
      ∀ v, q v = image profile a f v := by
  obtain ⟨a, ha⟩ := Finite.exists_max (fun a : Q => q (leaf hH a))
  have hdom (v : Point H X Q) : q v ≤ q (leaf hH a) :=
    (hq.le_parent hbound hH v).trans (ha (parent v))
  obtain ⟨g, σ, _, hg, h0, hm, h5, hr⟩ := hq.2 (leaf hH a)
  let f : ℕ → ExtOrd := fun i => min (σ (source H i)) (g 1)
  refine ⟨a, f, fun _ _ h => min_le_min_right _ (hm (source_mono H h)), ?_, ?_, ?_⟩
  · simp only [f, source_zero, h0, min_bot_left]
  · intro i
    change SelfVis 1 (min (σ (source H i)) (g 1))
    by_cases hi : σ (source H i) ≤ g 1
    · rw [min_eq_left hi]
      have he := h5 (source H i) 1 hi 1 le_rfl
      rw [source_visible H i] at he
      exact he.symm
    · rw [min_eq_right (not_le.mp hi).le]
      exact (hg 1).symm
  · intro v
    have h := hr v
    dsimp only at h
    rw [min_eq_left (hdom v)] at h
    rw [row, ceiling_leaf] at h
    exact h

/-- The full ladder excludes partial support erasure: every lawful section
is zero, or its serving chart is positive at every actual rung. -/
theorem lawful_iff_shape [Nonempty Q]
    (hbound : ∀ a d, profile a d ≤ H) (hH : 0 < H) (q : Point H X Q → ExtOrd) :
    Lawful profile q ↔ (∀ v, q v = ⊥) ∨
      ∃ a f, Monotone f ∧ f 0 = ⊥ ∧ (∀ i, SelfVis 1 (f i)) ∧
        (∀ i, 0 < i → i ≤ H → f i ≠ ⊥) ∧ ∀ v, q v = image profile a f v := by
  constructor
  · intro hq
    by_cases hzero : ∀ v, q v = ⊥
    · exact Or.inl hzero
    obtain ⟨a, f, hf, h0, hv, he⟩ := hq.exists_shape hbound hH
    have htop : f H ≠ ⊥ := by
      intro hz
      apply hzero
      intro v
      rw [he v]
      exact le_bot_iff.mp ((hf (index_le a v)).trans_eq hz)
    have hstep (i : ℕ) (hi : 0 < i) (hiH : i < H) (hz : f i = ⊥) : f (i + 1) = ⊥ := by
      have hz' : q (rung a ⟨i - 1, by omega⟩) = ⊥ := by
        rw [he, image, index_rung]
        simpa only [Nat.sub_add_cancel hi] using hz
      have hh := hq.predecessor_bot a hi hiH hz'
      simpa only [he, image, index_rung] using hh
    have hp (i : ℕ) (hi : 0 < i) (hiH : i ≤ H) : f i ≠ ⊥ := by
      intro hz
      have hall : ∀ j, i ≤ j → j ≤ H → f j = ⊥ := by
        intro j hij hjH
        induction j, hij using Nat.le_induction with
        | base => exact hz
        | succ j hij ih => exact hstep j (by omega) (by omega) (ih (by omega))
      exact htop (hall H hiH le_rfl)
    exact Or.inr ⟨a, f, hf, h0, hv, hp, he⟩
  · rintro (hz | ⟨a, f, hf, h0, hv, hp, he⟩)
    · have he : q = fun _ => ⊥ := funext hz
      rw [he]
      exact ⟨fun _ => selfVis_bot _, fun _ => by
        simp only [min_self]
        exact TransformsTo.to_bot _⟩
    · rw [funext he]
      exact image_lawful a f hf h0 hv hp

/-- Shadows remain distinct actual cells; the readout is their finite maximum. -/
noncomputable def readout (q : Point H X Q → ExtOrd) (d : X) : ExtOrd :=
  let _ := Fintype.ofFinite Q
  Finset.univ.sup (fun a : Q => q (shadow a d))

omit [Finite X] in
theorem readout_image (hbound : ∀ a d, profile a d ≤ H) (a : Q)
    {f : ℕ → ExtOrd} (hf : Monotone f) (d : X) :
    readout (image (H := H) profile a f) d = f (profile a d) := by
  classical
  let _ := Fintype.ofFinite Q
  apply le_antisymm
  · apply Finset.sup_le
    intro b _
    apply hf
    change min (cut H (profile a) (profile b)) (profile b d) ≤ profile a d
    have h := agree_cut H (profile a) (profile b) d
    omega
  · have h := Finset.le_sup (f := fun b : Q => image (H := H) profile a f (shadow b d))
        (Finset.mem_univ a)
    change f (profile a d) ≤
      Finset.univ.sup (fun b : Q => image (H := H) profile a f (shadow b d))
    simpa only [image, index, shadow, parent, ceiling, cut_refl,
      min_eq_right (hbound a d)] using h

omit [Finite X] [Finite Q] in
/-- Prefix repair preserves each real rung and shadow cap. Below the rank cut
only capped equality is required: a boundary half-orbit already above `γ`
need not keep its old uncapped reading. This theorem does not construct the
replacement profile or the scalar tables. -/
theorem cap_agreement (a b : Q) {k : ℕ}
    (hk : k ≤ cut H (profile a) (profile b)) (f g : ℕ → ExtOrd)
    (hf : Monotone f) (hg : Monotone g) {γ : ExtOrd}
    (hγf : γ ≤ f k) (hγg : γ ≤ g k)
    (hfg : ∀ i, i < k → min (f i) γ = min (g i) γ) (v : Point H X Q) :
    min (image profile a f v) γ = min (image profile b g v) γ := by
  have he := congrArg (fun z => min z k) (index_agreement (profile := profile) a b v)
  simp only [min_assoc, min_eq_right hk] at he
  change min (f (index profile a v)) γ = min (g (index profile b v)) γ
  by_cases ha : index profile a v < k
  · have hb : index profile b v = index profile a v := by omega
    rw [hb]
    exact hfg _ ha
  · have ha' : k ≤ index profile a v := by omega
    have hb' : k ≤ index profile b v := by omega
    rw [min_eq_right (hγf.trans (hf ha')), min_eq_right (hγg.trans (hg hb'))]

end VaughtConjecture.Knight.SupportLadderRows

namespace VaughtConjecture.Knight.LadderScalarRendering

open Transform Value ExtOrd
noncomputable section

open Classical in
/-- One-based rank on a finite set of positive values. -/
def rank (S : Finset ExtOrd) (x : ExtOrd) : ℕ := (S.filter (· ≤ x)).card

open Classical in
/-- The occupied initial segment followed by the constant ceiling tail. -/
def level (S : Finset ExtOrd) (C : ExtOrd) (i : ℕ) : ExtOrd :=
  if S.card < i then C else (S.filter (fun x => rank S x ≤ i)).sup id

theorem rank_le_card (S : Finset ExtOrd) (x : ExtOrd) : rank S x ≤ S.card := by
  classical
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem rank_mono (S : Finset ExtOrd) : Monotone (rank S) := by
  classical
  intro x y hxy
  apply Finset.card_le_card
  intro z hz
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
    (Finset.mem_filter.mp hz).2.trans hxy⟩

theorem rank_strict {S : Finset ExtOrd} {x y : ExtOrd} (hy : y ∈ S) (hxy : x < y) :
    rank S x < rank S y := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro z hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
      (Finset.mem_filter.mp hz).2.trans hxy.le⟩
  · intro he
    have hm : y ∈ S.filter (· ≤ y) := Finset.mem_filter.mpr ⟨hy, le_rfl⟩
    rw [← he] at hm
    exact (not_le_of_gt hxy) (Finset.mem_filter.mp hm).2

theorem rank_pos {S : Finset ExtOrd} {x : ExtOrd} (hx : x ∈ S) : 0 < rank S x := by
  classical
  exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, le_rfl⟩⟩

theorem rank_bot {S : Finset ExtOrd} (hS : ⊥ ∉ S) : rank S ⊥ = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hxS, hx⟩ := Finset.mem_filter.mp hx
  exact hS ((le_bot_iff.mp hx) ▸ hxS)

theorem level_zero (S : Finset ExtOrd) (C : ExtOrd) : level S C 0 = ⊥ := by
  classical
  rw [level, ite_eq_right (by omega)]
  have he : S.filter (fun x => rank S x ≤ 0) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hp := rank_pos (Finset.mem_filter.mp hx).1
    have := (Finset.mem_filter.mp hx).2
    omega
  rw [he, Finset.sup_empty]

theorem level_rank {S : Finset ExtOrd} {x : ExtOrd} (hx : x ∈ S) (C : ExtOrd) :
    level S C (rank S x) = x := by
  classical
  rw [level, ite_eq_right (not_lt.mpr (rank_le_card S x))]
  apply le_antisymm
  · apply Finset.sup_le
    intro y hy
    by_contra hn
    have hs := rank_strict (Finset.mem_filter.mp hy).1 (not_le.mp hn)
    exact not_le_of_gt hs (Finset.mem_filter.mp hy).2
  · exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨hx, le_rfl⟩)

theorem level_le {S : Finset ExtOrd} {C : ExtOrd} (hC : ∀ x ∈ S, x ≤ C) (i : ℕ) :
    level S C i ≤ C := by
  classical
  unfold level
  split_ifs
  · exact le_rfl
  · exact Finset.sup_le (fun x hx => hC x (Finset.mem_filter.mp hx).1)

theorem level_mono {S : Finset ExtOrd} {C : ExtOrd} (hC : ∀ x ∈ S, x ≤ C) :
    Monotone (level S C) := by
  classical
  intro i k hik
  by_cases hk : S.card < k
  · rw [show level S C k = C from ite_eq_left hk]
    exact level_le hC i
  · have hi : ¬S.card < i := by omega
    rw [level, ite_eq_right hi, level, ite_eq_right hk]
    apply Finset.sup_le
    intro x hx
    exact Finset.le_sup (f := id) (Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2.trans hik⟩)

theorem level_supported (S : Finset ExtOrd) (C : ExtOrd) (i : ℕ) :
    level S C i = ⊥ ∨ level S C i ∈ S ∨ level S C i = C := by
  classical
  unfold level
  split_ifs
  · exact Or.inr (Or.inr rfl)
  · by_cases hn : (S.filter (fun x => rank S x ≤ i)).Nonempty
    · obtain ⟨x, hx, he⟩ := Finset.sup_mem_of_nonempty (f := id) hn
      exact Or.inr (Or.inl (he ▸ (Finset.mem_filter.mp hx).1))
    · rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sup_empty]
      exact Or.inl rfl

theorem rank_min' {S : Finset ExtOrd} (hS : S.Nonempty) : rank S (S.min' hS) = 1 := by
  classical
  have he : S.filter (· ≤ S.min' hS) = {S.min' hS} := by
    ext x
    constructor
    · intro hx
      exact Finset.mem_singleton.mpr (le_antisymm (Finset.mem_filter.mp hx).2
        (Finset.min'_le S x (Finset.mem_filter.mp hx).1))
    · intro hx
      rw [Finset.mem_singleton.mp hx]
      exact Finset.mem_filter.mpr ⟨Finset.min'_mem S hS, le_rfl⟩
  rw [rank, he, Finset.card_singleton]

theorem level_pos {S : Finset ExtOrd} {C : ExtOrd} (hS : ⊥ ∉ S)
    (hC : ∀ x ∈ S, x ≤ C) (hpos : C ≠ ⊥) {i : ℕ} (hi : 0 < i) :
    level S C i ≠ ⊥ := by
  classical
  by_cases hn : S.Nonempty
  · have hm := Finset.min'_mem S hn
    have hle : S.min' hn ≤ level S C i := by
      rw [← level_rank hm C, rank_min' hn]
      exact level_mono hC hi
    intro hz
    exact hS ((le_bot_iff.mp (hle.trans_eq hz)) ▸ hm)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn, level, Finset.card_empty, ite_eq_left hi]
    exact hpos

open Classical in
/-- One more than the number of occupied values strictly below a cap. -/
def next (S : Finset ExtOrd) (h : ExtOrd) : ℕ := (S.filter (· < h)).card + 1

theorem next_le (S : Finset ExtOrd) (h : ExtOrd) : next S h ≤ S.card + 1 := by
  classical
  exact Nat.add_le_add_right (Finset.card_le_card (Finset.filter_subset _ _)) 1

theorem rank_lt_next {S : Finset ExtOrd} {x h : ExtOrd} (hx : x ∈ S) :
    rank S x < next S h ↔ x < h := by
  classical
  constructor
  · intro hr
    by_contra hn
    have hsub : S.filter (· < h) ⊂ S.filter (· ≤ x) := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨?_, ?_⟩
      · intro y hy
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1,
          (Finset.mem_filter.mp hy).2.le.trans (not_lt.mp hn)⟩
      · intro he
        have hm : x ∈ S.filter (· ≤ x) := Finset.mem_filter.mpr ⟨hx, le_rfl⟩
        rw [← he] at hm
        exact hn (Finset.mem_filter.mp hm).2
    have hc := Finset.card_lt_card hsub
    dsimp only [rank, next] at hr
    omega
  · intro hxh
    have hc : (S.filter (· ≤ x)).card ≤ (S.filter (· < h)).card := by
      apply Finset.card_le_card
      intro y hy
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1,
        (Finset.mem_filter.mp hy).2.trans_lt hxh⟩
    exact Nat.lt_succ_of_le hc

theorem rank_congr_below {S T : Finset ExtOrd} {h x : ExtOrd}
    (hst : ∀ y, y < h → (y ∈ S ↔ y ∈ T)) (hx : x < h) : rank S x = rank T x := by
  classical
  unfold rank
  congr 1
  ext y
  simp only [Finset.mem_filter]
  exact and_congr_left (fun hy => hst y (hy.trans_lt hx))

open Classical in
theorem below_eq {S T : Finset ExtOrd} {h : ExtOrd}
    (hst : ∀ y, y < h → (y ∈ S ↔ y ∈ T)) : S.filter (· < h) = T.filter (· < h) := by
  ext y
  simp only [Finset.mem_filter]
  exact and_congr_left (hst y)

theorem level_agree_below {S T : Finset ExtOrd} {C h : ExtOrd}
    (hst : ∀ y, y < h → (y ∈ S ↔ y ∈ T)) {i : ℕ} (hi : i < next S h) :
    level S C i = level T C i := by
  classical
  have he := below_eq hst
  have hn : next S h = next T h := congrArg (fun s : Finset ExtOrd => s.card + 1) he
  have hiS : ¬S.card < i := by have := next_le S h; omega
  have hiT : ¬T.card < i := by have := next_le T h; omega
  rw [level, ite_eq_right hiS, level, ite_eq_right hiT]
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨hxS, hr⟩ := Finset.mem_filter.mp hx
    have hxh := (rank_lt_next hxS).mp (hr.trans_lt hi)
    exact Finset.mem_filter.mpr ⟨(hst x hxh).mp hxS,
      (rank_congr_below hst hxh) ▸ hr⟩
  · intro hx
    obtain ⟨hxT, hr⟩ := Finset.mem_filter.mp hx
    have hxh := (rank_lt_next hxT).mp (hr.trans_lt (hn ▸ hi))
    exact Finset.mem_filter.mpr ⟨(hst x hxh).mpr hxT,
      (rank_congr_below hst hxh).symm ▸ hr⟩

theorem level_reaches (S : Finset ExtOrd) {C h : ExtOrd} (hh : h ≤ C) :
    h ≤ level S C (next S h) := by
  classical
  by_cases hc : S.card < next S h
  · rw [level, ite_eq_left hc]
    exact hh
  · have hn : (S.filter (h ≤ ·)).Nonempty := by
      by_contra hn
      have he : S.filter (· < h) = S := by
        apply Finset.filter_eq_self.mpr
        intro x hx
        by_contra hnx
        exact hn ⟨x, Finset.mem_filter.mpr ⟨hx, not_lt.mp hnx⟩⟩
      apply hc
      simp only [next, he]
      omega
    let x := (S.filter (h ≤ ·)).min' hn
    have hxm := Finset.min'_mem (S.filter (h ≤ ·)) hn
    have hxS : x ∈ S := (Finset.mem_filter.mp hxm).1
    have hxh : h ≤ x := (Finset.mem_filter.mp hxm).2
    have he : S.filter (· ≤ x) = insert x (S.filter (· < h)) := by
      ext y
      constructor
      · intro hy
        obtain ⟨hyS, hyx⟩ := Finset.mem_filter.mp hy
        by_cases hyh : y < h
        · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hyS, hyh⟩)
        · exact Finset.mem_insert.mpr (Or.inl (le_antisymm hyx
            (Finset.min'_le _ y (Finset.mem_filter.mpr ⟨hyS, not_lt.mp hyh⟩))))
      · intro hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact Finset.mem_filter.mpr ⟨hxS, le_rfl⟩
        · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1,
            (Finset.mem_filter.mp hy).2.le.trans hxh⟩
    have hr : rank S x = next S h := by
      rw [rank, he, Finset.card_insert_of_notMem]
      · rfl
      · intro hx
        exact (not_lt_of_ge hxh) (Finset.mem_filter.mp hx).2
    rw [← hr, level_rank hxS]
    exact hxh

variable {X : Type*} [Fintype X]

open Classical in
def values (p : X → ExtOrd) : Finset ExtOrd := (Finset.univ.image p).erase ⊥

theorem mem_values {p : X → ExtOrd} {x : ExtOrd} :
    x ∈ values p ↔ x ≠ ⊥ ∧ ∃ d, p d = x := by
  classical
  simp only [values, Finset.mem_erase, Finset.mem_image, Finset.mem_univ, true_and]

theorem bot_not_values (p : X → ExtOrd) : ⊥ ∉ values p := by
  rw [mem_values]
  simp only [ne_eq, not_true_eq_false, false_and, not_false_eq_true]

theorem values_card_le (p : X → ExtOrd) : (values p).card ≤ Fintype.card X := by
  classical
  exact (Finset.card_le_card (Finset.erase_subset _ _)).trans
    ((Finset.card_image_le).trans_eq (Finset.card_univ))

def fieldRank (p : X → ExtOrd) (d : X) : ℕ := rank (values p) (p d)

theorem fieldRank_le (p : X → ExtOrd) (d : X) : fieldRank p d ≤ Fintype.card X :=
  (rank_le_card _ _).trans (values_card_le p)

theorem field_readback (p : X → ExtOrd) (C : ExtOrd) (d : X) :
    level (values p) C (fieldRank p d) = p d := by
  by_cases hz : p d = ⊥
  · simp only [fieldRank, hz, rank_bot (bot_not_values p), level_zero]
  · exact level_rank (mem_values.mpr ⟨hz, d, rfl⟩) C

theorem values_bound {p : X → ExtOrd} {C : ExtOrd} (hC : ∀ d, p d ≤ C) :
    ∀ x ∈ values p, x ≤ C := by
  intro x hx
  obtain ⟨_, d, rfl⟩ := mem_values.mp hx
  exact hC d

theorem level_visible {p : X → ExtOrd} {C : ExtOrd} (hp : ∀ d, SelfVis 1 (p d))
    (hC : SelfVis 1 C) (i : ℕ) : SelfVis 1 (level (values p) C i) := by
  rcases level_supported (values p) C i with hz | hv | hc
  · rw [hz]; exact selfVis_bot 1
  · obtain ⟨_, d, hd⟩ := mem_values.mp hv
    rw [← hd]; exact hp d
  · rw [hc]; exact hC

private theorem eq_of_capped_lt {x y h : ExtOrd} (he : min x h = min y h) (hx : x < h) :
    x = y := by
  rw [min_eq_left hx.le] at he
  by_cases hy : y ≤ h
  · simpa only [min_eq_left hy] using he
  · rw [min_eq_right (not_le.mp hy).le] at he
    exact (ne_of_lt hx he).elim

theorem values_agree_below {p q : X → ExtOrd} {h : ExtOrd}
    (hag : ∀ d, min (p d) h = min (q d) h) :
    ∀ x, x < h → (x ∈ values p ↔ x ∈ values q) := by
  intro x hx
  rw [mem_values, mem_values]
  constructor
  · rintro ⟨hz, d, hd⟩
    refine ⟨hz, d, ?_⟩
    exact (eq_of_capped_lt (hag d) (hd ▸ hx)).symm.trans hd
  · rintro ⟨hz, d, hd⟩
    refine ⟨hz, d, ?_⟩
    exact (eq_of_capped_lt (hag d).symm (hd ▸ hx)).symm.trans hd

/-- Capped scalar agreement constructs the common rank prefix. -/
theorem fieldRank_agreement {p q : X → ExtOrd} {h : ExtOrd} (hh : ⊥ < h)
    (hag : ∀ d, min (p d) h = min (q d) h) :
    FiniteProfileControllers.Agree (fieldRank p) (fieldRank q) (next (values p) h) := by
  have hs := values_agree_below hag
  have hn : next (values p) h = next (values q) h :=
    congrArg (fun s : Finset ExtOrd => s.card + 1) (below_eq hs)
  intro d
  by_cases hd : p d < h
  · have he := eq_of_capped_lt (hag d) hd
    exact congrArg (fun n => min n (next (values p) h))
      ((rank_congr_below hs hd).trans (congrArg (rank (values q)) he))
  · have hph : h ≤ p d := not_lt.mp hd
    have hqh : h ≤ q d := by
      have he := hag d
      rw [min_eq_right hph] at he
      exact he.le.trans (min_le_left _ _)
    have hpv : p d ∈ values p := mem_values.mpr ⟨ne_of_gt (hh.trans_le hph), d, rfl⟩
    have hqv : q d ∈ values q := mem_values.mpr ⟨ne_of_gt (hh.trans_le hqh), d, rfl⟩
    have hpr : next (values p) h ≤ fieldRank p d :=
      not_lt.mp (fun hr => hd ((rank_lt_next hpv).mp hr))
    have hqr : next (values p) h ≤ fieldRank q d := by
      rw [hn]
      exact not_lt.mp (fun hr => (not_lt_of_ge hqh) ((rank_lt_next hqv).mp hr))
    rw [min_eq_right hpr, min_eq_right hqr]

/-- Both ladders reach the cap at a constructed common rank and agree
literally at all preceding rungs. No rank-cut hypothesis is supplied. -/
theorem common_rank_cut {p q : X → ExtOrd} {C h : ExtOrd}
    (hh : ⊥ < h) (hC : h ≤ C) (hag : ∀ d, min (p d) h = min (q d) h) :
    ∃ k, 0 < k ∧ k ≤ Fintype.card X + 1 ∧
      FiniteProfileControllers.Agree (fieldRank p) (fieldRank q) k ∧
      h ≤ level (values p) C k ∧ h ≤ level (values q) C k ∧
      ∀ i, i < k → level (values p) C i = level (values q) C i := by
  have hs := values_agree_below hag
  have hn : next (values p) h = next (values q) h :=
    congrArg (fun s : Finset ExtOrd => s.card + 1) (below_eq hs)
  refine ⟨next (values p) h, by unfold next; omega,
    (next_le _ _).trans (Nat.add_le_add_right (values_card_le p) 1),
    fieldRank_agreement hh hag, level_reaches _ hC, ?_, ?_⟩
  · rw [hn]
    exact level_reaches _ hC
  · exact fun _ hi => level_agree_below hs hi

variable {L : ℕ} {Q : Type*} [Finite Q] (profile : Q → X → ℕ)

/-- A selected table section. The anchor's ranks will be identified with
the ranks of the scalar input in the readback and prefix theorems. -/
def render (a : Q) (p : X → ExtOrd) (C : ExtOrd) :
    SupportLadderRows.Point L X Q → ExtOrd :=
  SupportLadderRows.image profile a (level (values p) C)

omit [Finite Q] in
/-- Scalar prefixes determine every physical rung and shadow cap, even
when the profiles reorder or split ties above the cap. -/
theorem render_cap_agreement {a b : Q} {p q : X → ExtOrd} {C h : ExtOrd}
    (hL : Fintype.card X + 1 ≤ L)
    (ha : ∀ d, profile a d = fieldRank p d) (hb : ∀ d, profile b d = fieldRank q d)
    (hp : ∀ d, p d ≤ C) (hq : ∀ d, q d ≤ C) (hC : h ≤ C)
    (hag : ∀ d, min (p d) h = min (q d) h) (v : SupportLadderRows.Point L X Q) :
    min (render profile a p C v) h = min (render profile b q C v) h := by
  by_cases hz : h = ⊥
  · simp only [hz, min_eq_right bot_le]
  · obtain ⟨k, _, hk, hr, hkp, hkq, he⟩ := common_rank_cut (bot_lt_iff_ne_bot.mpr hz) hC hag
    have hcut : k ≤ FiniteProfileControllers.cut L (profile a) (profile b) := by
      apply FiniteProfileControllers.le_cut (hk.trans hL)
      intro d
      rw [ha d, hb d]
      exact hr d
    exact SupportLadderRows.cap_agreement a b hcut (level (values p) C) (level (values q) C)
      (level_mono (values_bound hp)) (level_mono (values_bound hq)) hkp hkq
      (fun i hi => congrArg (fun x => min x h) (he i hi)) v

end
end VaughtConjecture.Knight.LadderScalarRendering
