
import VaughtConjecture.Knight.PointwiseLabels
import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CountedEncoding
import Mathlib.Algebra.Order.BigOperators.Group.Finset
/-! # Paired point/orbit slots and literal lower-prefix stability

An orbit is hosted only when the inventory contains an occurrence invisible at
the encoding grade. Its endpoint shares the orbit; an unhosted visible value is
a point. Rank r receives the odd point block 2r+1 or even orbit block 2r+2.

The encoding is constructed, injective and strictly monotone on the inventory.
It uses at most twice as many blocks as there are boundary occurrences. Capped
agreement at a visible ordinal cut preserves every group, rank and code below
the cut, including a group's invisible companions. No agreement of normalized
profiles at their largest common source cut is assumed or proved here.

This module proves scalar coding facts, not semantic respect of normalization.
Literal top is left top by normalize, and excluded explicitly from its finite
alphabet theorem. The coupled construction's bounded profiles have no top.
-/

namespace VaughtConjecture.Knight.PairedSlotEncoding
open  Value ExtOrd
noncomputable section
def Orbit (j : ℕ) (S : Finset Ordinal₀) (a : Ordinal₀) :=
  finitePart a ≤ j ∧ ∃ b ∈ S, finitePart b < j ∧ limitPart b = limitPart a
def key j S a := by
  classical
  exact if Orbit j S a then limitPart a else a
def keys j (S : Finset Ordinal₀) := S.image (key j S)
def rank j S a :=
  ((keys j S).filter fun b => b < key j S a).card

theorem key_le {j : ℕ} {S : Finset Ordinal₀} {a : Ordinal₀} : key j S a ≤ a := by
  unfold key
  split_ifs
  · exact limitPart_le
  · exact le_rfl

theorem orbit_of_invisible {j} {S} {a}
    (ha : a ∈ S) (h : finitePart a < j) : Orbit j S a :=
  ⟨h.le, a, ha, h, rfl⟩

theorem invisible_lt_cut {j} {a h}
    (ha : finitePart a < j) (hh : j ≤ finitePart h) (hl : limitPart a < h) : a < h := by
  by_contra hn
  have hha := not_lt.mp hn
  have hlp : limitPart h = limitPart a := by
    apply le_antisymm (limitPart_mono hha)
    by_contra hm
    have hm' := limitPart_add_nat_le_of_lt (not_le.mp hm) (finitePart h)
    rw [limitPart_add_finitePart] at hm'
    exact not_lt_of_ge hm' hl
  have := finitePart_le_of_le_of_limitPart_eq hha hlp
  omega

theorem orbit_congr_below {j} {S T} {a h}
    (hh : j ≤ finitePart h)
    (heq : ∀ b, b < h → (b ∈ S ↔ b ∈ T))
    (ha : limitPart a < h) : Orbit j S a ↔ Orbit j T a := by
  constructor
  · rintro ⟨hfp, b, hb, hbj, hba⟩
    exact ⟨hfp, b, (heq b (invisible_lt_cut hbj hh (hba ▸ ha))).mp hb, hbj, hba⟩
  · rintro ⟨hfp, b, hb, hbj, hba⟩
    exact ⟨hfp, b, (heq b (invisible_lt_cut hbj hh (hba ▸ ha))).mpr hb, hbj, hba⟩

theorem key_congr_below {j} {S T} {a h}
    (hh : j ≤ finitePart h)
    (heq : ∀ b, b < h → (b ∈ S ↔ b ∈ T)) (ha : a < h) :
    key j S a = key j T a := by
  have ho := orbit_congr_below hh heq ((limitPart_le).trans_lt ha)
  by_cases hs : Orbit j S a
  · simp_all [key]
  · simp_all [key]

theorem orbit_witness_key {j} {S} {a}
    (ha : Orbit j S a) :
    ∃ b ∈ S, finitePart b < j ∧ key j S b = key j S a := by
  obtain ⟨b, hb, hbj, hba⟩ := ha.2
  exact ⟨b, hb, hbj, by simp_all [key, orbit_of_invisible]⟩
theorem exists_low_key {j} {S} {a h}
    (hh : j ≤ finitePart h) (ha : a ∈ S) (hk : key j S a < h) :
    ∃ b ∈ S, b < h ∧ key j S b = key j S a := by
  by_cases ho : Orbit j S a
  · obtain ⟨b, hb, hbj, hba⟩ := ho.2
    have hl : limitPart b < h := by
      simp_all [key]
    exact ⟨b, hb, invisible_lt_cut hbj hh hl, by
      simp_all [key, orbit_of_invisible]⟩
  · exact ⟨a, ha, by simp_all [key], rfl⟩

theorem keys_prefix {j} {S T} {h}
    (hh : j ≤ finitePart h) (heq : ∀ b, b < h → (b ∈ S ↔ b ∈ T)) :
    (keys j S).filter (· < h) = (keys j T).filter (· < h) := by
  have transfer (S T : Finset Ordinal₀)
      (heq : ∀ b, b < h → (b ∈ S ↔ b ∈ T)) :
      ∀ x ∈ keys j S, x < h → x ∈ keys j T := by
    intro x hx hxh
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, hbh, hba⟩ := exists_low_key hh ha hxh
    exact Finset.mem_image.mpr ⟨b, (heq b hbh).mp hb,
      (key_congr_below hh heq hbh).symm.trans hba⟩
  ext x
  simp only [Finset.mem_filter]
  exact ⟨fun hx => ⟨transfer S T heq x hx.1 hx.2, hx.2⟩,
    fun hx => ⟨transfer T S (fun b hb => (heq b hb).symm) x hx.1 hx.2, hx.2⟩⟩

theorem rank_congr_below {j} {S T} {a h}
    (hh : j ≤ finitePart h) (heq : ∀ b, b < h → (b ∈ S ↔ b ∈ T)) (ha : a < h) :
    rank j S a = rank j T a := by
  have hk := key_congr_below hh heq ha
  have hp := keys_prefix hh heq
  have hfilter : (keys j S).filter (fun b => b < key j S a) =
      (keys j T).filter (fun b => b < key j S a) := by
    ext b
    by_cases hb : b < key j S a
    · have hbh := hb.trans ((key_le).trans_lt ha)
      have hm := Finset.ext_iff.mp hp b
      simpa only [Finset.mem_filter, hbh, hb, ] using hm
    · simp_all
  unfold rank
  rw [← hk, hfilter]

def block j S a := by
  classical
  exact 2 * rank j S a + if Orbit j S a then 2 else 1
def offset j S a := by
  classical
  exact if Orbit j S a then finitePart a else j
def encode j S a :=
  ofOrd (Ordinal.omega0 * block j S a + offset j S a)

theorem offset_le j S a :
    offset j S a ≤ j := by
  unfold offset
  split_ifs with ho
  · exact ho.1
  · exact le_rfl

theorem block_pos j S a :
    0 < block j S a := by
  unfold block
  split_ifs <;> omega

theorem encode_congr_below {j} {S T} {a h}
    (hh : j ≤ finitePart h) (heq : ∀ b, b < h → (b ∈ S ↔ b ∈ T)) (ha : a < h) :
    encode j S a = encode j T a := by
  have hr := rank_congr_below hh heq ha
  have ho := orbit_congr_below hh heq ((limitPart_le).trans_lt ha)
  by_cases hs : Orbit j S a
  · simp_all [encode, block, offset]
  · simp_all [encode, block, offset]

theorem rank_lt_of_key_lt {j} {S} {a b}
    (ha : a ∈ S) (hab : key j S a < key j S b) : rank j S a < rank j S b := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_of_subset
    (fun x hx => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,
      (Finset.mem_filter.mp hx).2.trans hab⟩) |>.mpr
  refine ⟨key j S a, Finset.mem_filter.mpr
    ⟨Finset.mem_image_of_mem _ ha, hab⟩, ?_⟩
  simp  

theorem rank_lt_card {j} {S} {a}
    (ha : a ∈ S) : rank j S a < S.card := by
  apply lt_of_lt_of_le (b := (keys j S).card) _ Finset.card_image_le
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr
  exact ⟨key j S a, Finset.mem_image_of_mem _ ha, by simp⟩

theorem encode_mem_sharp {j} {S} {a}
    (ha : a ∈ S) : encode j S a ∈ codedAlphabet (2 * S.card) j := by
  have hr := rank_lt_card (j := j) ha
  have hb : block j S a ≤ 2 * S.card := by
    grind [block]
  exact mem_codedAlphabet_iff.mpr (Or.inr
    ⟨block j S a, offset j S a, hb, (offset_le j S a).trans (Nat.le_succ j), rfl⟩)

theorem encode_visible {j k} {S} {a}
    (hk : k ≤ j) (ha : k ≤ finitePart a) : SelfVis k (encode j S a) := by
  rw [encode, selfVis_ofOrd_iff, finitePart_mul_add]
  unfold offset
  split_ifs
  · exact ha
  · exact hk

theorem key_mono j S :
    Monotone (key j S) := by
  intro a b hab
  by_cases hb : Orbit j S b
  · by_cases ha : Orbit j S a
    · simp_all [key, limitPart_mono]
    · have hl : limitPart a < limitPart b := by
        apply lt_of_le_of_ne (limitPart_mono hab)
        intro he
        have hf := finitePart_le_of_le_of_limitPart_eq hab he
        exact ha ⟨hf.trans hb.1, by
          obtain ⟨c, hc, hcj, hcb⟩ := hb.2
          exact ⟨c, hc, hcj, hcb.trans he.symm⟩⟩
      have hh := limitPart_add_nat_le_of_lt hl (finitePart a)
      rw [limitPart_add_finitePart] at hh
      simpa only [key, ite_eq_right ha, ite_eq_left hb] using hh
  · simpa only [key, ite_eq_right hb] using (key_le).trans hab

theorem encode_strictMonoOn j S :
    StrictMonoOn (encode j S) S := by
  intro a ha b hb hab
  rcases lt_or_eq_of_le (key_mono j S hab.le) with hkey | hkey
  · have hr := rank_lt_of_key_lt ha hkey
    have hblock : block j S a < block j S b := by
      grind [block]
    apply ofOrd_lt_ofOrd.mpr
    exact (code_add_lt_mul (Nat.cast_lt.mpr hblock) _).trans_le le_self_add
  · by_cases hoa : Orbit j S a <;> by_cases hob : Orbit j S b
    · have hr : rank j S a = rank j S b := by simp  [rank, hkey]
      simp  [key, ite_eq_left hoa, ite_eq_left hob] at hkey
      have hfp : finitePart a < finitePart b := by
        grind [not_lt_of_ge, le_of_finitePart_le]
      apply ofOrd_lt_ofOrd.mpr
      simp only [block, offset, ite_eq_left hoa, ite_eq_left hob, hr]
      exact (add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr hfp)
    · have hj : 0 < j := by obtain ⟨c, _, hc, _⟩ := hoa.2; omega
      simp  [key, ite_eq_left hoa, ite_eq_right hob] at hkey
      have hfp : finitePart b = 0 := by rw [← hkey, finitePart_limitPart]
      exact (hob (orbit_of_invisible hb (hfp ▸ hj))).elim
    · have hj : 0 < j := by obtain ⟨c, _, hc, _⟩ := hob.2; omega
      simp  [key, ite_eq_right hoa, ite_eq_left hob] at hkey
      have hfp : finitePart a = 0 := by rw [hkey, finitePart_limitPart]
      exact (hoa (orbit_of_invisible ha (hfp ▸ hj))).elim
    · simp_all [key]

theorem orbit_iff_of_key_eq {j} {S} {a b}
    (ha : a ∈ S) (hb : b ∈ S) (hk : key j S a = key j S b) :
    Orbit j S a ↔ Orbit j S b := by
  have one (a b : Ordinal₀) (hb : b ∈ S)
      (hk : key j S a = key j S b) (ho : Orbit j S a) : Orbit j S b := by
    by_contra hn
    have hj : 0 < j := by obtain ⟨c, _, hc, _⟩ := ho.2; omega
    simp  [key, ite_eq_left ho, ite_eq_right hn] at hk
    have hf : finitePart b = 0 := by rw [← hk, finitePart_limitPart]
    exact hn (orbit_of_invisible hb (hf ▸ hj))
  exact ⟨one a b hb hk, one b a ha hk.symm⟩

theorem block_eq_of_key_eq {j} {S} {a b}
    (ha : a ∈ S) (hb : b ∈ S) (hk : key j S a = key j S b) :
    block j S a = block j S b := by
  have hr : rank j S a = rank j S b := by simp  [rank, hk]
  have ho := orbit_iff_of_key_eq ha hb hk
  by_cases hoa : Orbit j S a
  · simp_all [block]
  · simp_all [block]

theorem block_lt_of_key_lt {j} {S} {a b}
    (ha : a ∈ S) (hk : key j S a < key j S b) : block j S a < block j S b := by
  have hr := rank_lt_of_key_lt ha hk
  unfold block
  split_ifs <;> omega

def ceiling j S a := by
  classical
  exact if Orbit j S a then limitPart a + j else a

theorem ceiling_le_of_key_lt {j} {S} {a b}
    (hk : key j S a < key j S b) : ceiling j S a ≤ b := by
  have hab : a < b := by
    by_contra hn
    exact not_lt_of_ge (key_mono j S (not_lt.mp hn)) hk
  by_cases ha : Orbit j S a
  · have hl := limitPart_mono hab.le
    rcases lt_or_eq_of_le hl with hl | hl
    · simpa only [ceiling, ite_eq_left ha] using
        (limitPart_add_nat_le_of_lt hl j).trans (limitPart_le)
    · have hb : j < finitePart b := by
        by_contra hn
        have ho : Orbit j S b := ⟨not_lt.mp hn, by
          obtain ⟨c, hc, hcj, hca⟩ := ha.2
          exact ⟨c, hc, hcj, hca.trans hl⟩⟩
        simp  [key, ite_eq_left ha, ite_eq_left ho, hl, ] at hk
      simp  [ceiling, ite_eq_left ha, hl]
      calc limitPart b + j ≤ limitPart b + finitePart b :=
            add_le_add_right (Nat.cast_le.mpr hb.le) _
        _ = b := limitPart_add_finitePart b
  · grind [ceiling]

def ordValues : ExtOrd → Finset Ordinal₀
  | ⊥ => ∅
  | some ⊤ => ∅
  | some (some a) => {a}

theorem mem_ordValues {x} {a} :
    a ∈ ordValues x ↔ x = ofOrd a := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨b, rfl⟩
  · simp [ordValues, ofOrd]
  · simp [ordValues, ofOrd]
  · change a ∈ ({b}) ↔ ofOrd b = ofOrd a
    simp  [  eq_comm]

section
variable {X : Type*} [Fintype X]

def values (p : X → ExtOrd) :=
  Finset.univ.biUnion (fun d => ordValues (p d))

theorem mem_values {p : X → ExtOrd} {a : Ordinal₀} :
    a ∈ values p ↔ ∃ d, p d = ofOrd a := by
  simp  [values,    mem_ordValues]

theorem values_card_le (p : X → ExtOrd) : (values p).card ≤ Fintype.card X := by
  calc
    _ ≤ ∑ d : X, (ordValues (p d)).card := Finset.card_biUnion_le
    _ ≤ ∑ _d : X, 1 := by
      apply Finset.sum_le_sum
      intro d _
      rcases ExtOrd.cases (p d) with h | h | ⟨a, h⟩ <;> simp [h, ordValues, ofOrd]
    _ = _ := by simp

theorem eq_of_cap_eq_lt {x y h : ExtOrd} (he : min x h = min y h) (hx : x < h) :
    x = y := by grind

theorem values_prefix {p q : X → ExtOrd} {h : Ordinal₀}
    (hpq : CappedEq p q (ofOrd h)) :
    ∀ a, a < h → (a ∈ values p ↔ a ∈ values q) := by
  intro a ha
  rw [mem_values, mem_values]
  constructor
  · rintro ⟨d, hd⟩
    have he := eq_of_cap_eq_lt (hpq d) (hd ▸ ofOrd_lt_ofOrd.mpr ha)
    exact ⟨d, he.symm.trans hd⟩
  · rintro ⟨d, hd⟩
    have he := eq_of_cap_eq_lt (hpq d).symm (hd ▸ ofOrd_lt_ofOrd.mpr ha)
    exact ⟨d, he.symm.trans hd⟩

def normalize (j : ℕ) (p : X → ExtOrd) (d : X) :=
  match p d with
  | ⊥ => ⊥
  | some ⊤ => ⊤
  | some (some a) => encode j (values p) a

theorem normalize_ofOrd {j : ℕ} {p : X → ExtOrd} {d : X} {a : Ordinal₀}
    (hd : p d = ofOrd a) : normalize j p d = encode j (values p) a := by
  simp  [normalize, hd, ofOrd]

theorem normalize_bot_iff {j : ℕ} {p : X → ExtOrd} {d : X} :
    normalize j p d = ⊥ ↔ p d = ⊥ := by
  rcases ExtOrd.cases (p d) with hd | hd | ⟨a, hd⟩
  · simp  [normalize, hd]
  · simp_all [normalize]
  · rw [normalize_ofOrd hd]
    exact iff_of_false (ofOrd_ne_bot _) (hd ▸ ofOrd_ne_bot a)

theorem normalize_mem (j : ℕ) (p : X → ExtOrd) (d : X) (hd : p d ≠ ⊤) :
    normalize j p d ∈ codedAlphabet (2 * Fintype.card X) j := by
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · simp  [normalize, hb]
    exact mem_codedAlphabet_iff.mpr (Or.inl rfl)
  · exact (hd ht).elim
  · rw [normalize_ofOrd ha]
    obtain hb | ⟨b, i, hb, hi, he⟩ := mem_codedAlphabet_iff.mp
      (encode_mem_sharp (j := j) (mem_values.mpr ⟨d, ha⟩))
    · simp_all [VaughtConjecture.Knight.ExtOrd.codedAlphabet]
    · exact mem_codedAlphabet_iff.mpr (Or.inr
        ⟨b, i, hb.trans (Nat.mul_le_mul_left 2 (values_card_le p)), hi, he⟩)

theorem normalize_prefix {j : ℕ} {p q : X → ExtOrd} {h : Ordinal₀}
    (hh : j ≤ finitePart h)
    (hpq : CappedEq p q (ofOrd h))
    (d : X) (hd : p d < ofOrd h) : normalize j p d = normalize j q d := by
  have he := eq_of_cap_eq_lt (hpq d) hd
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · simp  [normalize, hb, ← he]
  · grind
  · rw [normalize_ofOrd ha, normalize_ofOrd (he.symm.trans ha)]
    exact encode_congr_below hh (values_prefix hpq) (ofOrd_lt_ofOrd.mp (ha ▸ hd))


