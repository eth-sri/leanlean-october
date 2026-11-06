/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LongGuardRows
public import VaughtConjecture.Knight.FiniteProfileControllers

/-! # Physical support ladders

The rung of height `t ≥ 2` puts ranks `t - 1` and `t` in the same
source block, at offsets one and two. Every rung is an actual row owner;
unused field ranks are not omitted. These are the ladder rows of
`newapproach4` / `newapproach5`, with their original odd-block encoding.

This module concerns the complete row table. Installation on mixed supports
and grade-two numerical receiving remain separate obligations.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.SupportLadderRows

open Transform Value ExtOrd FiniteProfileControllers

/-- The exact source code used by a rung, including its long diagonal. -/
def source (t i : ℕ) : ExtOrd :=
  if t ≤ 1 then SlotControllerFamily.value (2 * min i t - 1)
  else LongGuardRows.source (2 * t - 3) (2 * min i t - 1)

theorem source_visible (t i : ℕ) : SelfVis 1 (source t i) := by
  unfold source; split_ifs <;> [exact SlotControllerFamily.value_visible _;
    exact LongGuardRows.source_visible _ _]

theorem source_coded (t i : ℕ) : IsCodedLabel 1 (source t i) := by
  unfold source; split_ifs <;> [exact SlotControllerFamily.value_coded _;
    exact LongGuardRows.source_coded _ _]

theorem source_le_iff (t i j : ℕ) :
    source t i ≤ source t j ↔ min i t ≤ min j t := by
  unfold source; split_ifs with ht
  · rw [SlotControllerFamily.value_le_iff]; omega
  · rw [LongGuardRows.source_le_iff]; omega

theorem source_mono (t : ℕ) : Monotone (source t) :=
  fun _ _ h => (source_le_iff _ _ _).mpr (min_le_min_right _ h)

@[simp] theorem source_zero (t : ℕ) : source t 0 = ⊥ := by
  simp [source, SlotControllerFamily.value]

theorem source_bot_iff (t i : ℕ) : source t i = ⊥ ↔ min i t = 0 := by
  simpa only [source_zero, le_bot_iff, Nat.zero_min, Nat.le_zero] using source_le_iff t i 0

/-- Positive visible tables have faithful locality at every rung. The
source-block test includes the long diagonal, not just bounded commutation. -/
theorem transforms_positive {Y : Type*} [Finite Y] (a : Y → ℕ) (t : ℕ)
    (f : ℕ → ExtOrd) (hf : Monotone f) (h0 : f 0 = ⊥)
    (hv : ∀ i, SelfVis 1 (f i)) (hp : ∀ i, 0 < i → i ≤ t → f i ≠ ⊥) :
    TransformsTo (fun _ : Y => 1) (fun d => source t (a d))
      (fun d => f (min (a d) t)) := by
  refine LongGuardRows.transforms_of_visible_table
    (fun _ => source_visible _ _) (fun _ => hv _)
    (fun d e hde => hf ((source_le_iff _ _ _).mp hde))
    (fun d hd => by rw [(source_bot_iff _ _).mp hd, h0])
    fun d e hde hd => ?_
  have hz : min (a d) t = 0 :=
    by_contra fun hn => hp _ (Nat.pos_of_ne_zero hn) (min_le_right _ _) hd
  rw [(source_bot_iff _ _).mpr hz, blockFloor_bot] at hde
  have he : blockFloor (source t (a e)) = ⊥ ↔ source t (a e) = ⊥ := by
    unfold source LongGuardRows.source SlotControllerFamily.value
    split_ifs <;> simp [LongGuardRows.endpoint, blockFloor_ofOrd, SeparatedGradeOne.band]
  rw [(source_bot_iff _ _).mp (he.mp hde.symm), h0]

variable {X Q : Type*} {H : ℕ} {profile : Q → X → ℕ}

/-- Every rank has a separate rung, even when no original field uses it.
Shadows are separate occurrences, including rank-zero shadows. -/
abbrev Point (H : ℕ) (X Q : Type*) := Q × (Fin H ⊕ X)

local notation "Pt" => Point H X Q

def parent (v : Pt) : Q := v.1

def ceiling (profile : Q → X → ℕ) (v : Pt) : ℕ :=
  match v.2 with
  | .inl i => i.val + 1
  | .inr d => profile v.1 d

def rung (a : Q) (i : Fin H) : Pt := (a, .inl i)
def shadow (a : Q) (d : X) : Pt := (a, .inr d)
def leaf (hH : 0 < H) (a : Q) : Pt := rung a ⟨H - 1, by omega⟩

def index (profile : Q → X → ℕ) (a : Q) (v : Pt) : ℕ :=
  min (cut H (profile a) (profile (parent v))) (ceiling profile v)

def row (profile : Q → X → ℕ) (c v : Pt) : ExtOrd :=
  source (ceiling profile c) (index profile (parent c) v)

def image (profile : Q → X → ℕ) (a : Q) (f : ℕ → ExtOrd) (v : Pt) : ExtOrd :=
  f (index profile a v)

def Lawful (profile : Q → X → ℕ) (q : Pt → ExtOrd) : Prop :=
  (∀ v, SelfVis 1 (q v)) ∧ ∀ c,
    TransformsTo (fun _ : Pt => 1) (row profile c) (fun v => min (q v) (q c))

theorem ceiling_le (hbound : ∀ a d, profile a d ≤ H) (v : Pt) : ceiling profile v ≤ H := by
  rcases v with ⟨a, i | d⟩
  · exact i.isLt
  · exact hbound a d

theorem index_le (a : Q) (v : Pt) : index profile a v ≤ H :=
  (min_le_left _ _).trans (cut_le _ _ _)

@[simp] theorem ceiling_leaf (hH : 0 < H) (a : Q) :
    ceiling profile (leaf (X := X) hH a) = H := by
  change H - 1 + 1 = H; omega

@[simp] theorem index_leaf (hH : 0 < H) (a b : Q) :
    index profile a (leaf (X := X) hH b) = cut H (profile a) (profile b) := by
  rw [index, ceiling_leaf]
  exact min_eq_left (cut_le _ _ _)

/-- Whole-coordinate agreement includes every unused rung and every shadow. -/
theorem index_agreement (a b : Q) (v : Pt) :
    min (index profile a v) (cut H (profile a) (profile b)) =
      min (index profile b v) (cut H (profile a) (profile b)) := by
  unfold index
  have := cross_agreement H (profile a) (profile b) (profile (parent v))
  omega

variable [Finite X] [Finite Q]

omit [Finite X] [Finite Q] in
theorem row_parent (hbound : ∀ a d, profile a d ≤ H) (hH : 0 < H) (c : Pt) :
    row profile c (leaf hH (parent c)) = row profile c c := by
  rw [row, row, index_leaf, cut_refl, index, cut_refl, min_eq_right (ceiling_le hbound c)]
  simp only [source, min_self, min_eq_right (ceiling_le hbound c)]

omit [Finite X] [Finite Q] in
/-- Locality at the auxiliary itself bounds it by its actual parent leaf. -/
theorem Lawful.le_parent {q : Pt → ExtOrd} (hq : Lawful profile q)
    (hbound : ∀ a d, profile a d ≤ H) (hH : 0 < H) (c : Pt) :
    q c ≤ q (leaf hH (parent c)) := by
  obtain ⟨g, σ, _, _, _, _, _, hr⟩ := hq.2 c
  refine min_eq_right_iff.mp ((hr _).trans ?_)
  rw [row_parent hbound hH]
  simpa only [min_self] using (hr c).symm

/-- The full ladder excludes partial support erasure: every lawful section
is zero, or its serving chart is positive at every actual rung. -/
theorem lawful_iff_shape [Nonempty Q]
    (hbound : ∀ a d, profile a d ≤ H) (hH : 0 < H) (q : Pt → ExtOrd) :
    Lawful profile q ↔ (∀ v, q v = ⊥) ∨
      ∃ a f, Monotone f ∧ f 0 = ⊥ ∧ (∀ i, SelfVis 1 (f i)) ∧
        (∀ i, 0 < i → i ≤ H → f i ≠ ⊥) ∧ ∀ v, q v = image profile a f v := by
  constructor
  · intro hq
    by_cases hzero : ∀ v, q v = ⊥
    · exact Or.inl hzero
    obtain ⟨a, ha⟩ := Finite.exists_max (fun a : Q => q (leaf hH a))
    have hdom (v : Pt) : q v ≤ q (leaf hH a) := (hq.le_parent hbound hH v).trans (ha (parent v))
    obtain ⟨g, σ, _, hg, h0, hm, h5, hr⟩ := hq.2 (leaf hH a)
    let f : ℕ → ExtOrd := fun i => min (σ (source H i)) (g 1)
    have hf : Monotone f := fun _ _ h => min_le_min_right _ (hm (source_mono H h))
    have hf0 : f 0 = ⊥ := by simp only [f, source_zero, h0, min_bot_left]
    have hv (i : ℕ) : SelfVis 1 (f i) := by
      change SelfVis 1 (min (σ (source H i)) (g 1))
      by_cases hi : σ (source H i) ≤ g 1
      · rw [min_eq_left hi]
        have he := h5 (source H i) 1 hi 1 le_rfl
        rw [source_visible H i] at he; exact he.symm
      · rw [min_eq_right (not_le.mp hi).le]
        exact (hg 1).symm
    have he (v : Pt) : q v = image profile a f v := by
      have h := hr v; dsimp only at h
      rwa [min_eq_left (hdom v), row, ceiling_leaf] at h
    have htop : f H ≠ ⊥ := fun hz => hzero fun v => by
      rw [he v]; exact le_bot_iff.mp ((hf (index_le a v)).trans_eq hz)
    have hrung (x : Fin H) : index profile a (rung a x) = x.val + 1 := by
      simp only [index, rung, parent, ceiling, cut_refl, min_eq_right (show x.val + 1 ≤ H from x.isLt)]
    have hstep (i : ℕ) (hi : 0 < i) (hiH : i < H) (hz : f i = ⊥) : f (i + 1) = ⊥ := by
      let c : Pt := rung a ⟨i, hiH⟩
      let d : Pt := rung a ⟨i - 1, by omega⟩
      have hb : blockFloor (row profile c d) = blockFloor (row profile c c) := by
        change blockFloor (source (i + 1) (index profile a d)) =
          blockFloor (source (i + 1) (index profile a c))
        dsimp only [d, c]; rw [hrung, hrung]
        have hi' : i - 1 + 1 = i := by omega
        rw [hi']
        have h1 : ¬i + 1 ≤ 1 := by omega
        have h2 : 2 * min i (i + 1) - 1 = 2 * (i + 1) - 3 := by omega
        have h3 : ¬2 * min (i + 1) (i + 1) - 1 ≤ 2 * (i + 1) - 3 := by omega
        have h4 : 2 * (i + 1) - 3 ≠ 0 := by omega
        simp only [source, ite_eq_right h1, h2, LongGuardRows.source, le_refl, ite_true,
          ite_eq_right h3, SlotControllerFamily.value, ite_eq_right h4,
          SeparatedGradeOne.band_floor, LongGuardRows.endpoint, blockFloor_ofOrd, limitPart_code]
      have hd : min (q d) (q c) = ⊥ := by
        have hzd : q d = ⊥ := by rw [he, image, hrung]; simpa only [Nat.sub_add_cancel hi] using hz
        rw [hzd, min_bot_left]
      have hh := LongGuardRows.bottom_of_same_block (hq.2 c) hb hd
      simpa only [min_self, he, image, c, hrung] using hh
    have hp (i : ℕ) (hi : 0 < i) (hiH : i ≤ H) : f i ≠ ⊥ := fun hz => by
      have hall (j) (hij : i ≤ j) (hjH : j ≤ H) : f j = ⊥ := by
        induction j, hij using Nat.le_induction with
        | base => exact hz
        | succ j hij ih => exact hstep j (by omega) (by omega) (ih (by omega))
      exact htop (hall H hiH le_rfl)
    exact Or.inr ⟨a, f, hf, hf0, hv, hp, he⟩
  · rintro (hz | ⟨a, f, hf, h0, hv, hp, he⟩)
    · rw [funext hz]
      exact ⟨fun _ => selfVis_bot _, fun _ => by simp only [min_self]; exact TransformsTo.to_bot _⟩
    · rw [funext he]
      refine ⟨fun _ => hv _, fun c => ?_⟩
      let e := index profile a c
      have hcap (v : Pt) : min (image profile a f v) (image profile a f c) =
          f (min (index profile (parent c) v) e) := by
        rw [image, image, ← hf.map_min]
        change f (min (index profile a v) (min _ _)) = _
        rw [← min_assoc, index_agreement, min_assoc]; rfl
      rw [funext hcap]
      by_cases hz : e = 0
      · have hzero : (fun v : Pt => f (min (index profile (parent c) v) e)) = fun _ => ⊥ := by
          simp [hz, h0]
        change TransformsTo _ _ (fun v => f (min (index profile (parent c) v) e))
        rw [hzero]; exact TransformsTo.to_bot _
      · have het : e ≤ ceiling profile c := min_le_right _ _
        change TransformsTo _ (fun v => source (ceiling profile c) (index profile (parent c) v))
          (fun v => f (min (index profile (parent c) v) e))
        simpa only [min_assoc, min_eq_right het] using
          transforms_positive (index (H := H) profile (parent c)) (ceiling profile c)
            (fun i => f (min i e)) (fun _ _ h => hf (min_le_min_right _ h)) (by simpa using h0)
            (fun _ => hv _) (fun i hi _ => hp _ (by omega) ((min_le_right _ _).trans (index_le a c)))

/-- Shadows remain distinct actual cells; the readout is their finite maximum. -/
def readout (q : Pt → ExtOrd) (d : X) : ExtOrd :=
  let _ := Fintype.ofFinite Q
  Finset.univ.sup fun a : Q => q (shadow a d)

omit [Finite X] in
theorem readout_image (hbound : ∀ a d, profile a d ≤ H) (a : Q)
    {f : ℕ → ExtOrd} (hf : Monotone f) (d : X) :
    readout (image (H := H) profile a f) d = f (profile a d) := by
  classical
  let _ := Fintype.ofFinite Q
  refine le_antisymm (Finset.sup_le fun b _ => hf ?_) ?_
  · change min (cut H (profile a) (profile b)) (profile b d) ≤ profile a d
    have := agree_cut H (profile a) (profile b) d
    omega
  · change f (profile a d) ≤ Finset.univ.sup fun b : Q => image (H := H) profile a f (shadow b d)
    simpa only [image, index, shadow, parent, ceiling, cut_refl, min_eq_right (hbound a d)] using
      Finset.le_sup (f := fun b : Q => image (H := H) profile a f (shadow b d)) (Finset.mem_univ a)

omit [Finite X] [Finite Q] in
theorem cap_agreement (a b : Q) {k : ℕ}
    (hk : k ≤ cut H (profile a) (profile b)) (f g : ℕ → ExtOrd)
    (hf : Monotone f) (hg : Monotone g) {γ : ExtOrd}
    (hγf : γ ≤ f k) (hγg : γ ≤ g k)
    (hfg : ∀ i, i < k → min (f i) γ = min (g i) γ) (v : Pt) :
    min (image profile a f v) γ = min (image profile b g v) γ := by
  have he := congrArg (fun z => min z k) (index_agreement (profile := profile) a b v)
  simp only [min_assoc, min_eq_right hk] at he
  change min (f (index profile a v)) γ = min (g (index profile b v)) γ
  by_cases ha : index profile a v < k
  · rw [show index profile b v = index profile a v by omega]
    exact hfg _ ha
  · rw [min_eq_right (hγf.trans (hf (by omega))), min_eq_right (hγg.trans (hg (by omega)))]

