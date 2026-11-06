/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CountedEncoding
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
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

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.PairedSlotEncoding
open Transform Value ExtOrd

section Explicit
variable (j : ℕ) (S : Finset Ordinal.{0})

def Orbit (a : Ordinal.{0}) : Prop :=
  finitePart a ≤ j ∧ ∃ b ∈ S, finitePart b < j ∧ limitPart b = limitPart a
def key (a : Ordinal.{0}) : Ordinal.{0} := by
  classical exact if Orbit j S a then limitPart a else a
def keys : Finset Ordinal.{0} := S.image (key j S)
def rank (a : Ordinal.{0}) : ℕ := ((keys j S).filter fun b => b < key j S a).card

theorem key_le (a : Ordinal.{0}) : key j S a ≤ a := by
  unfold key; split_ifs <;> [exact limitPart_le a; exact le_rfl]

end Explicit

theorem orbit_of_invisible {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}}
    (ha : a ∈ S) (h : finitePart a < j) : Orbit j S a :=
  ⟨h.le, a, ha, h, rfl⟩

theorem invisible_lt_cut {j : ℕ} {a h : Ordinal.{0}}
    (ha : finitePart a < j) (hh : j ≤ finitePart h) (hl : limitPart a < h) : a < h := by
  by_contra hn
  have hha := not_lt.mp hn
  have hlp : limitPart h = limitPart a := le_antisymm (limitPart_mono hha)
    (not_lt.mp fun hm => hl.not_ge ((limitPart_add_finitePart h).symm ▸
      limitPart_add_nat_le_of_lt hm (finitePart h)))
  have := finitePart_le_of_le_of_limitPart_eq hha hlp
  omega

theorem orbit_congr_below {j : ℕ} {S T : Finset Ordinal.{0}} {a h : Ordinal.{0}}
    (hh : j ≤ finitePart h) (heq : ∀ b, b < h → (b ∈ S ↔ b ∈ T))
    (ha : limitPart a < h) : Orbit j S a ↔ Orbit j T a :=
  ⟨fun ⟨hfp, b, hb, hbj, hba⟩ => ⟨hfp, b, (heq b (invisible_lt_cut hbj hh (hba ▸ ha))).mp hb, hbj, hba⟩,
    fun ⟨hfp, b, hb, hbj, hba⟩ => ⟨hfp, b, (heq b (invisible_lt_cut hbj hh (hba ▸ ha))).mpr hb, hbj, hba⟩⟩

theorem key_congr_below {j : ℕ} {S T : Finset Ordinal.{0}} {a h : Ordinal.{0}}
    (hh : j ≤ finitePart h) (heq : ∀ b, b < h → (b ∈ S ↔ b ∈ T)) (ha : a < h) :
    key j S a = key j T a := by
  have ho := orbit_congr_below hh heq ((limitPart_le a).trans_lt ha)
  by_cases hs : Orbit j S a
  · simp only [key, ite_eq_left hs, ite_eq_left (ho.mp hs)]
  · simp only [key, ite_eq_right hs, ite_eq_right fun ht => hs (ho.mpr ht)]

theorem orbit_witness_key {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}}
    (ha : Orbit j S a) : ∃ b ∈ S, finitePart b < j ∧ key j S b = key j S a := by
  obtain ⟨b, hb, hbj, hba⟩ := ha.2
  exact ⟨b, hb, hbj, by simp only [key, ite_eq_left ha, ite_eq_left (orbit_of_invisible hb hbj), hba]⟩

theorem exists_low_key {j : ℕ} {S : Finset Ordinal.{0}} {a h : Ordinal.{0}}
    (hh : j ≤ finitePart h) (ha : a ∈ S) (hk : key j S a < h) :
    ∃ b ∈ S, b < h ∧ key j S b = key j S a := by
  by_cases ho : Orbit j S a
  · obtain ⟨b, hb, hbj, hba⟩ := ho.2
    exact ⟨b, hb, invisible_lt_cut hbj hh (by rw [hba]; simpa only [key, ite_eq_left ho] using hk),
      by simp only [key, ite_eq_left ho, ite_eq_left (orbit_of_invisible hb hbj), hba]⟩
  · exact ⟨a, ha, by simpa only [key, ite_eq_right ho] using hk, rfl⟩

theorem keys_prefix {j : ℕ} {S T : Finset Ordinal.{0}} {h : Ordinal.{0}}
    (hh : j ≤ finitePart h) (heq : ∀ b, b < h → (b ∈ S ↔ b ∈ T)) :
    (keys j S).filter (· < h) = (keys j T).filter (· < h) := by
  have transfer (S T : Finset Ordinal.{0}) (heq : ∀ b, b < h → (b ∈ S ↔ b ∈ T))
      (x) (hx : x ∈ keys j S) (hxh : x < h) : x ∈ keys j T := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, hbh, hba⟩ := exists_low_key hh ha hxh
    exact Finset.mem_image.mpr ⟨b, (heq b hbh).mp hb, (key_congr_below hh heq hbh).symm.trans hba⟩
  ext x
  simp only [Finset.mem_filter]
  exact ⟨fun hx => ⟨transfer S T heq x hx.1 hx.2, hx.2⟩,
    fun hx => ⟨transfer T S (fun b hb => (heq b hb).symm) x hx.1 hx.2, hx.2⟩⟩

theorem rank_congr_below {j : ℕ} {S T : Finset Ordinal.{0}} {a h : Ordinal.{0}}
    (hh : j ≤ finitePart h) (heq : ∀ b, b < h → (b ∈ S ↔ b ∈ T)) (ha : a < h) :
    rank j S a = rank j T a := by
  have hfilter : (keys j S).filter (· < key j S a) = (keys j T).filter (· < key j S a) := by
    ext b
    by_cases hb : b < key j S a
    · have hbh := hb.trans ((key_le j S a).trans_lt ha)
      simpa only [Finset.mem_filter, hbh, hb, and_true] using Finset.ext_iff.mp (keys_prefix hh heq) b
    · simp only [Finset.mem_filter, hb, and_false]
  unfold rank
  rw [← key_congr_below hh heq ha, hfilter]

section Explicit2
variable (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0})

def block : ℕ := by classical exact 2 * rank j S a + if Orbit j S a then 2 else 1
def offset : ℕ := by classical exact if Orbit j S a then finitePart a else j
def encode : ExtOrd := ofOrd (Ordinal.omega0 * block j S a + offset j S a)

theorem offset_le : offset j S a ≤ j := by
  unfold offset; split_ifs with ho <;> [exact ho.1; exact le_rfl]

theorem block_pos : 0 < block j S a := by
  unfold block; split_ifs <;> omega

end Explicit2

theorem rank_lt_of_key_lt {j : ℕ} {S : Finset Ordinal.{0}} {a b : Ordinal.{0}}
    (ha : a ∈ S) (hab : key j S a < key j S b) : rank j S a < rank j S b := by
  apply Finset.card_lt_card
  refine (Finset.ssubset_iff_of_subset fun x hx => Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2.trans hab⟩).mpr
    ⟨key j S a, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ ha, hab⟩, by simp⟩

theorem rank_lt_card {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}}
    (ha : a ∈ S) : rank j S a < S.card :=
  (Finset.card_lt_card ((Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr
    ⟨key j S a, Finset.mem_image_of_mem _ ha, by simp⟩)).trans_le Finset.card_image_le

theorem encode_visible {j k : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}}
    (hk : k ≤ j) (ha : k ≤ finitePart a) : SelfVis k (encode j S a) := by
  rw [encode, selfVis_ofOrd_iff, finitePart_mul_add]
  unfold offset; split_ifs <;> assumption

theorem key_mono (j : ℕ) (S : Finset Ordinal.{0}) : Monotone (key j S) := by
  intro a b hab
  by_cases hb : Orbit j S b
  · by_cases ha : Orbit j S a
    · simpa only [key, ite_eq_left ha, ite_eq_left hb] using limitPart_mono hab
    · have hl : limitPart a < limitPart b := lt_of_le_of_ne (limitPart_mono hab) fun he =>
        ha ⟨(finitePart_le_of_le_of_limitPart_eq hab he).trans hb.1,
          let ⟨c, hc, hcj, hcb⟩ := hb.2; ⟨c, hc, hcj, hcb.trans he.symm⟩⟩
      have hh := limitPart_add_nat_le_of_lt hl (finitePart a)
      rw [limitPart_add_finitePart] at hh
      simpa only [key, ite_eq_right ha, ite_eq_left hb] using hh
  · simpa only [key, ite_eq_right hb] using (key_le j S a).trans hab

section KeyCompare
variable {j : ℕ} {S : Finset Ordinal.{0}} {a b : Ordinal.{0}}

theorem orbit_iff_of_key_eq (ha : a ∈ S) (hb : b ∈ S) (hk : key j S a = key j S b) :
    Orbit j S a ↔ Orbit j S b := by
  have one (a b : Ordinal.{0}) (hb : b ∈ S) (hk : key j S a = key j S b) (ho : Orbit j S a) :
      Orbit j S b := by
    by_contra hn
    obtain ⟨c, _, hc, _⟩ := ho.2
    simp only [key, ite_eq_left ho, ite_eq_right hn] at hk
    have hf : finitePart b = 0 := by rw [← hk, finitePart_limitPart]
    exact hn (orbit_of_invisible hb (by omega))
  exact ⟨one a b hb hk, one b a ha hk.symm⟩

theorem block_eq_of_key_eq (ha : a ∈ S) (hb : b ∈ S) (hk : key j S a = key j S b) :
    block j S a = block j S b := by
  have hr : rank j S a = rank j S b := by simp only [rank, hk]
  have ho := orbit_iff_of_key_eq ha hb hk
  by_cases hoa : Orbit j S a
  · simp only [block, hr, ite_eq_left hoa, ite_eq_left (ho.mp hoa)]
  · simp only [block, hr, ite_eq_right hoa, ite_eq_right fun h => hoa (ho.mpr h)]

theorem block_lt_of_key_lt (ha : a ∈ S) (hk : key j S a < key j S b) :
    block j S a < block j S b := by
  have hr := rank_lt_of_key_lt ha hk
  unfold block; split_ifs <;> omega

end KeyCompare

theorem encode_strictMonoOn (j : ℕ) (S : Finset Ordinal.{0}) : StrictMonoOn (encode j S) S := by
  intro a ha b hb hab
  rcases lt_or_eq_of_le (key_mono j S hab.le) with hkey | hkey
  · exact ofOrd_lt_ofOrd.mpr
      ((code_add_lt_mul (Nat.cast_lt.mpr (block_lt_of_key_lt ha hkey)) _).trans_le le_self_add)
  · have ho := orbit_iff_of_key_eq ha hb hkey
    by_cases hoa : Orbit j S a
    · have hob := ho.mp hoa
      rw [encode, encode, ofOrd_lt_ofOrd, block_eq_of_key_eq ha hb hkey]
      simp only [offset, ite_eq_left hoa, ite_eq_left hob, add_lt_add_iff_left, Nat.cast_lt]
      simp only [key, ite_eq_left hoa, ite_eq_left hob] at hkey
      exact not_le.mp fun hn => hab.not_ge (le_of_finitePart_le hkey.symm hn)
    · have hob : ¬ Orbit j S b := fun h => hoa (ho.mpr h)
      simp only [key, ite_eq_right hoa, ite_eq_right hob] at hkey
      exact (hab.ne hkey).elim

def ceiling (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) : Ordinal.{0} := by
  classical exact if Orbit j S a then limitPart a + j else a

theorem ceiling_le_of_key_lt {j : ℕ} {S : Finset Ordinal.{0}} {a b : Ordinal.{0}}
    (hk : key j S a < key j S b) : ceiling j S a ≤ b := by
  have hab : a < b := not_le.mp fun hn => hk.not_ge (key_mono j S hn)
  by_cases ha : Orbit j S a
  · rcases lt_or_eq_of_le (limitPart_mono hab.le) with hl | hl
    · simpa only [ceiling, ite_eq_left ha] using
        (limitPart_add_nat_le_of_lt hl j).trans (limitPart_le b)
    · have hb : j < finitePart b := not_le.mp fun hn => by
        have ho : Orbit j S b := ⟨hn, let ⟨c, hc, hcj, hca⟩ := ha.2; ⟨c, hc, hcj, hca.trans hl⟩⟩
        simp only [key, ite_eq_left ha, ite_eq_left ho, hl, lt_self_iff_false] at hk
      simp only [ceiling, ite_eq_left ha, hl]
      exact (add_le_add_right (Nat.cast_le.mpr hb.le) _).trans_eq (limitPart_add_finitePart b)
  · simpa only [ceiling, ite_eq_right ha] using hab.le

def ordValues : ExtOrd → Finset Ordinal.{0}
  | ⊥ => ∅
  | some ⊤ => ∅
  | some (some a) => {a}

section Profile
variable {X : Type*} [Fintype X]

def values (p : X → ExtOrd) : Finset Ordinal.{0} :=
  Finset.univ.biUnion fun d => ordValues (p d)

theorem mem_values {p : X → ExtOrd} {a : Ordinal.{0}} :
    a ∈ values p ↔ ∃ d, p d = ofOrd a := by
  have hm {x : ExtOrd} : a ∈ ordValues x ↔ x = ofOrd a := by
    rcases ExtOrd.cases x with rfl | rfl | ⟨b, rfl⟩ <;> simp [ordValues, ofOrd, eq_comm]
  simp only [values, Finset.mem_biUnion, Finset.mem_univ, true_and, hm]

theorem values_card_le (p : X → ExtOrd) : (values p).card ≤ Fintype.card X := by
  refine Finset.card_biUnion_le.trans
    ((Finset.sum_le_sum (g := fun _ => 1) fun d _ => ?_).trans_eq (by simp))
  rcases ExtOrd.cases (p d) with h | h | ⟨a, h⟩ <;> simp [h, ordValues, ofOrd]

theorem eq_of_cap_eq_lt {x y h : ExtOrd} (he : min x h = min y h) (hx : x < h) : x = y := by
  have hy : y < h := not_le.mp fun hn => hx.ne (by rwa [min_eq_left hx.le, min_eq_right hn] at he)
  simpa only [min_eq_left hx.le, min_eq_left hy.le] using he

theorem values_prefix {p q : X → ExtOrd} {h : Ordinal.{0}}
    (hpq : ∀ d, min (p d) (ofOrd h) = min (q d) (ofOrd h)) :
    ∀ a, a < h → (a ∈ values p ↔ a ∈ values q) := fun a ha => by
  rw [mem_values, mem_values]
  exact ⟨fun ⟨d, hd⟩ => ⟨d, (eq_of_cap_eq_lt (hpq d) (hd ▸ ofOrd_lt_ofOrd.mpr ha)).symm.trans hd⟩,
    fun ⟨d, hd⟩ => ⟨d, (eq_of_cap_eq_lt (hpq d).symm (hd ▸ ofOrd_lt_ofOrd.mpr ha)).symm.trans hd⟩⟩

def normalize (j : ℕ) (p : X → ExtOrd) (d : X) : ExtOrd :=
  match p d with
  | ⊥ => ⊥
  | some ⊤ => ⊤
  | some (some a) => encode j (values p) a

theorem normalize_ofOrd {j : ℕ} {p : X → ExtOrd} {d : X} {a : Ordinal.{0}}
    (hd : p d = ofOrd a) : normalize j p d = encode j (values p) a := by
  simp only [normalize, hd, ofOrd]

theorem normalize_bot_iff (j : ℕ) (p : X → ExtOrd) (d : X) :
    normalize j p d = ⊥ ↔ p d = ⊥ := by
  rcases ExtOrd.cases (p d) with hd | hd | ⟨a, hd⟩
  · simp only [normalize, hd]
  · simp only [normalize, hd, top_ne_bot]
  · rw [normalize_ofOrd hd]
    exact iff_of_false (ofOrd_ne_bot _) (hd ▸ ofOrd_ne_bot a)

theorem normalize_mem (j : ℕ) (p : X → ExtOrd) (d : X) (hd : p d ≠ ⊤) :
    normalize j p d ∈ codedAlphabet (2 * Fintype.card X) j := by
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · simp only [normalize, hb]; exact mem_codedAlphabet_iff.mpr (Or.inl rfl)
  · exact (hd ht).elim
  · rw [normalize_ofOrd ha]
    have hr := rank_lt_card (j := j) (mem_values.mpr ⟨d, ha⟩)
    have hc := values_card_le p
    have hb : block j (values p) a ≤ 2 * Fintype.card X := by
      unfold block; split_ifs <;> omega
    exact mem_codedAlphabet_iff.mpr (Or.inr
      ⟨_, _, hb, (offset_le j (values p) a).trans (Nat.le_succ j), rfl⟩)

theorem normalize_prefix {j : ℕ} {p q : X → ExtOrd} {h : Ordinal.{0}}
    (hh : j ≤ finitePart h) (hpq : ∀ d, min (p d) (ofOrd h) = min (q d) (ofOrd h))
    (d : X) (hd : p d < ofOrd h) : normalize j p d = normalize j q d := by
  have he := eq_of_cap_eq_lt (hpq d) hd
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · simp only [normalize, hb, ← he]
  · exact (not_lt_of_ge le_top (ht ▸ hd)).elim
  · rw [normalize_ofOrd ha, normalize_ofOrd (he.symm.trans ha)]
    have hah : a < h := ofOrd_lt_ofOrd.mp (ha ▸ hd)
    have heq := values_prefix hpq
    have hr := rank_congr_below hh heq hah
    have ho := orbit_congr_below hh heq ((limitPart_le a).trans_lt hah)
    by_cases hs : Orbit j (values p) a
    · simp only [encode, block, offset, hr, ite_eq_left hs, ite_eq_left (ho.mp hs)]
    · simp only [encode, block, offset, hr, ite_eq_right hs, ite_eq_right fun ht => hs (ho.mpr ht)]

