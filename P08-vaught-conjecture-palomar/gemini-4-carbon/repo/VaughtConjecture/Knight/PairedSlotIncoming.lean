/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import VaughtConjecture.Knight.OrbitPrefixSupport
public import VaughtConjecture.Knight.FiniteOrbitEmbedding

@[expose] public section

namespace VaughtConjecture.Knight.PairedSlotEncoding
open Transform Value ExtOrd
noncomputable section
def Orbit (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) : Prop :=
  finitePart a ≤ j ∧ ∃ b ∈ S, finitePart b < j ∧ limitPart b = limitPart a
def key (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) : Ordinal.{0} := by
  classical
  exact if Orbit j S a then limitPart a else a
def keys (j : ℕ) (S : Finset Ordinal.{0}) : Finset Ordinal.{0} := S.image (key j S)
def rank (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) : ℕ :=
  ((keys j S).filter fun b => b < key j S a).card

theorem key_le (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) : key j S a ≤ a := by
  unfold key
  split_ifs
  · exact limitPart_le a
  · exact le_rfl

theorem orbit_of_invisible {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}}
    (ha : a ∈ S) (h : finitePart a < j) : Orbit j S a :=
  ⟨h.le, a, ha, h, rfl⟩

theorem invisible_lt_cut {j : ℕ} {a h : Ordinal.{0}}
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

theorem orbit_congr_below {j : ℕ} {S T : Finset Ordinal.{0}} {a h : Ordinal.{0}}
    (hh : j ≤ finitePart h)
    (heq : ∀ b, b < h → (b ∈ S ↔ b ∈ T))
    (ha : limitPart a < h) : Orbit j S a ↔ Orbit j T a := by
  constructor
  · rintro ⟨hfp, b, hb, hbj, hba⟩
    exact ⟨hfp, b, (heq b (invisible_lt_cut hbj hh (hba ▸ ha))).mp hb, hbj, hba⟩
  · rintro ⟨hfp, b, hb, hbj, hba⟩
    exact ⟨hfp, b, (heq b (invisible_lt_cut hbj hh (hba ▸ ha))).mpr hb, hbj, hba⟩

theorem key_congr_below {j : ℕ} {S T : Finset Ordinal.{0}} {a h : Ordinal.{0}}
    (hh : j ≤ finitePart h)
    (heq : ∀ b, b < h → (b ∈ S ↔ b ∈ T)) (ha : a < h) :
    key j S a = key j T a := by
  have ho := orbit_congr_below hh heq ((limitPart_le a).trans_lt ha)
  by_cases hs : Orbit j S a
  · simp only [key, ite_eq_left hs, ite_eq_left (ho.mp hs)]
  · simp only [key, ite_eq_right hs, ite_eq_right (fun ht => hs (ho.mpr ht))]

theorem orbit_witness_key {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}}
    (ha : Orbit j S a) :
    ∃ b ∈ S, finitePart b < j ∧ key j S b = key j S a := by
  obtain ⟨b, hb, hbj, hba⟩ := ha.2
  exact ⟨b, hb, hbj, by simp only [key, ite_eq_left ha,
    ite_eq_left (orbit_of_invisible hb hbj), hba]⟩
theorem exists_low_key {j : ℕ} {S : Finset Ordinal.{0}} {a h : Ordinal.{0}}
    (hh : j ≤ finitePart h) (ha : a ∈ S) (hk : key j S a < h) :
    ∃ b ∈ S, b < h ∧ key j S b = key j S a := by
  by_cases ho : Orbit j S a
  · obtain ⟨b, hb, hbj, hba⟩ := ho.2
    have hl : limitPart b < h := by
      rw [hba]
      simpa only [key, ite_eq_left ho] using hk
    exact ⟨b, hb, invisible_lt_cut hbj hh hl, by
      simp only [key, ite_eq_left ho, ite_eq_left (orbit_of_invisible hb hbj), hba]⟩
  · exact ⟨a, ha, by simpa only [key, ite_eq_right ho] using hk, rfl⟩

theorem keys_prefix {j : ℕ} {S T : Finset Ordinal.{0}} {h : Ordinal.{0}}
    (hh : j ≤ finitePart h) (heq : ∀ b, b < h → (b ∈ S ↔ b ∈ T)) :
    (keys j S).filter (· < h) = (keys j T).filter (· < h) := by
  have transfer (S T : Finset Ordinal.{0})
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

theorem rank_congr_below {j : ℕ} {S T : Finset Ordinal.{0}} {a h : Ordinal.{0}}
    (hh : j ≤ finitePart h) (heq : ∀ b, b < h → (b ∈ S ↔ b ∈ T)) (ha : a < h) :
    rank j S a = rank j T a := by
  have hk := key_congr_below hh heq ha
  have hp := keys_prefix hh heq
  have hfilter : (keys j S).filter (fun b => b < key j S a) =
      (keys j T).filter (fun b => b < key j S a) := by
    ext b
    by_cases hb : b < key j S a
    · have hbh := hb.trans ((key_le j S a).trans_lt ha)
      have hm := Finset.ext_iff.mp hp b
      simpa only [Finset.mem_filter, hbh, hb, and_true] using hm
    · simp only [Finset.mem_filter, hb, and_false]
  unfold rank
  rw [← hk, hfilter]

def block (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) : ℕ := by
  classical
  exact 2 * rank j S a + if Orbit j S a then 2 else 1
def offset (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) : ℕ := by
  classical
  exact if Orbit j S a then finitePart a else j
def encode (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) : ExtOrd :=
  ofOrd (Ordinal.omega0 * block j S a + offset j S a)

theorem offset_le (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) :
    offset j S a ≤ j := by
  unfold offset
  split_ifs with ho
  · exact ho.1
  · exact le_rfl

theorem block_pos (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) :
    0 < block j S a := by
  unfold block
  split_ifs <;> omega

theorem encode_congr_below {j : ℕ} {S T : Finset Ordinal.{0}} {a h : Ordinal.{0}}
    (hh : j ≤ finitePart h) (heq : ∀ b, b < h → (b ∈ S ↔ b ∈ T)) (ha : a < h) :
    encode j S a = encode j T a := by
  have hr := rank_congr_below hh heq ha
  have ho := orbit_congr_below hh heq ((limitPart_le a).trans_lt ha)
  by_cases hs : Orbit j S a
  · simp only [encode, block, offset, hr, ite_eq_left hs, ite_eq_left (ho.mp hs)]
  · simp only [encode, block, offset, hr, ite_eq_right hs,
      ite_eq_right (fun ht => hs (ho.mpr ht))]

theorem rank_lt_of_key_lt {j : ℕ} {S : Finset Ordinal.{0}} {a b : Ordinal.{0}}
    (ha : a ∈ S) (hab : key j S a < key j S b) : rank j S a < rank j S b := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_of_subset
    (fun x hx => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,
      (Finset.mem_filter.mp hx).2.trans hab⟩) |>.mpr
  refine ⟨key j S a, Finset.mem_filter.mpr
    ⟨Finset.mem_image_of_mem _ ha, hab⟩, ?_⟩
  simp only [Finset.mem_filter, lt_self_iff_false, and_false, not_false_eq_true]

theorem rank_lt_card {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}}
    (ha : a ∈ S) : rank j S a < S.card := by
  apply lt_of_lt_of_le (b := (keys j S).card) _ Finset.card_image_le
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr
  exact ⟨key j S a, Finset.mem_image_of_mem _ ha, by simp⟩

theorem encode_mem_sharp {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}}
    (ha : a ∈ S) : encode j S a ∈ codedAlphabet (2 * S.card) j := by
  have hr := rank_lt_card (j := j) ha
  have hb : block j S a ≤ 2 * S.card := by
    unfold block
    split_ifs <;> omega
  exact mem_codedAlphabet_iff.mpr (Or.inr
    ⟨block j S a, offset j S a, hb, (offset_le j S a).trans (Nat.le_succ j), rfl⟩)

theorem encode_visible {j k : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}}
    (hk : k ≤ j) (ha : k ≤ finitePart a) : SelfVis k (encode j S a) := by
  rw [encode, selfVis_ofOrd_iff, finitePart_mul_add]
  unfold offset
  split_ifs
  · exact ha
  · exact hk

theorem key_mono (j : ℕ) (S : Finset Ordinal.{0}) :
    Monotone (key j S) := by
  intro a b hab
  by_cases hb : Orbit j S b
  · by_cases ha : Orbit j S a
    · simpa only [key, ite_eq_left ha, ite_eq_left hb] using limitPart_mono hab
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
  · simpa only [key, ite_eq_right hb] using (key_le j S a).trans hab

theorem encode_strictMonoOn (j : ℕ) (S : Finset Ordinal.{0}) :
    StrictMonoOn (encode j S) S := by
  intro a ha b hb hab
  rcases lt_or_eq_of_le (key_mono j S hab.le) with hkey | hkey
  · have hr := rank_lt_of_key_lt ha hkey
    have hblock : block j S a < block j S b := by
      unfold block
      split_ifs <;> omega
    apply ofOrd_lt_ofOrd.mpr
    exact (code_add_lt_mul (Nat.cast_lt.mpr hblock) _).trans_le le_self_add
  · by_cases hoa : Orbit j S a <;> by_cases hob : Orbit j S b
    · have hr : rank j S a = rank j S b := by simp only [rank, hkey]
      simp only [key, ite_eq_left hoa, ite_eq_left hob] at hkey
      have hfp : finitePart a < finitePart b := by
        by_contra hn
        exact not_lt_of_ge (le_of_finitePart_le hkey.symm (not_lt.mp hn)) hab
      apply ofOrd_lt_ofOrd.mpr
      simp only [block, offset, ite_eq_left hoa, ite_eq_left hob, hr]
      exact (add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr hfp)
    · have hj : 0 < j := by obtain ⟨c, _, hc, _⟩ := hoa.2; omega
      simp only [key, ite_eq_left hoa, ite_eq_right hob] at hkey
      have hfp : finitePart b = 0 := by rw [← hkey, finitePart_limitPart]
      exact (hob (orbit_of_invisible hb (hfp ▸ hj))).elim
    · have hj : 0 < j := by obtain ⟨c, _, hc, _⟩ := hob.2; omega
      simp only [key, ite_eq_right hoa, ite_eq_left hob] at hkey
      have hfp : finitePart a = 0 := by rw [hkey, finitePart_limitPart]
      exact (hoa (orbit_of_invisible ha (hfp ▸ hj))).elim
    · simp only [key, ite_eq_right hoa, ite_eq_right hob] at hkey
      exact (hab.ne hkey).elim

theorem orbit_iff_of_key_eq {j : ℕ} {S : Finset Ordinal.{0}} {a b : Ordinal.{0}}
    (ha : a ∈ S) (hb : b ∈ S) (hk : key j S a = key j S b) :
    Orbit j S a ↔ Orbit j S b := by
  have one (a b : Ordinal.{0}) (hb : b ∈ S)
      (hk : key j S a = key j S b) (ho : Orbit j S a) : Orbit j S b := by
    by_contra hn
    have hj : 0 < j := by obtain ⟨c, _, hc, _⟩ := ho.2; omega
    simp only [key, ite_eq_left ho, ite_eq_right hn] at hk
    have hf : finitePart b = 0 := by rw [← hk, finitePart_limitPart]
    exact hn (orbit_of_invisible hb (hf ▸ hj))
  exact ⟨one a b hb hk, one b a ha hk.symm⟩

theorem block_eq_of_key_eq {j : ℕ} {S : Finset Ordinal.{0}} {a b : Ordinal.{0}}
    (ha : a ∈ S) (hb : b ∈ S) (hk : key j S a = key j S b) :
    block j S a = block j S b := by
  have hr : rank j S a = rank j S b := by simp only [rank, hk]
  have ho := orbit_iff_of_key_eq ha hb hk
  by_cases hoa : Orbit j S a
  · simp only [block, hr, ite_eq_left hoa, ite_eq_left (ho.mp hoa)]
  · simp only [block, hr, ite_eq_right hoa, ite_eq_right (fun h => hoa (ho.mpr h))]

theorem block_lt_of_key_lt {j : ℕ} {S : Finset Ordinal.{0}} {a b : Ordinal.{0}}
    (ha : a ∈ S) (hk : key j S a < key j S b) : block j S a < block j S b := by
  have hr := rank_lt_of_key_lt ha hk
  unfold block
  split_ifs <;> omega

def ceiling (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) : Ordinal.{0} := by
  classical
  exact if Orbit j S a then limitPart a + j else a

theorem ceiling_le_of_key_lt {j : ℕ} {S : Finset Ordinal.{0}} {a b : Ordinal.{0}}
    (hk : key j S a < key j S b) : ceiling j S a ≤ b := by
  have hab : a < b := by
    by_contra hn
    exact not_lt_of_ge (key_mono j S (not_lt.mp hn)) hk
  by_cases ha : Orbit j S a
  · have hl := limitPart_mono hab.le
    rcases lt_or_eq_of_le hl with hl | hl
    · simpa only [ceiling, ite_eq_left ha] using
        (limitPart_add_nat_le_of_lt hl j).trans (limitPart_le b)
    · have hb : j < finitePart b := by
        by_contra hn
        have ho : Orbit j S b := ⟨not_lt.mp hn, by
          obtain ⟨c, hc, hcj, hca⟩ := ha.2
          exact ⟨c, hc, hcj, hca.trans hl⟩⟩
        simp only [key, ite_eq_left ha, ite_eq_left ho, hl, lt_self_iff_false] at hk
      simp only [ceiling, ite_eq_left ha, hl]
      calc limitPart b + j ≤ limitPart b + finitePart b :=
            add_le_add_right (Nat.cast_le.mpr hb.le) _
        _ = b := limitPart_add_finitePart b
  · simpa only [ceiling, ite_eq_right ha] using hab.le

def ordValues : ExtOrd → Finset Ordinal.{0}
  | ⊥ => ∅
  | some ⊤ => ∅
  | some (some a) => {a}

theorem mem_ordValues {x : ExtOrd} {a : Ordinal.{0}} :
    a ∈ ordValues x ↔ x = ofOrd a := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨b, rfl⟩
  · simp [ordValues, ofOrd]
  · simp [ordValues, ofOrd]
  · change a ∈ ({b} : Finset Ordinal.{0}) ↔ ofOrd b = ofOrd a
    simp only [Finset.mem_singleton, ofOrd_inj, eq_comm]

section Profile
variable {X : Type*} [Fintype X]

def values (p : X → ExtOrd) : Finset Ordinal.{0} :=
  Finset.univ.biUnion (fun d => ordValues (p d))

theorem mem_values {p : X → ExtOrd} {a : Ordinal.{0}} :
    a ∈ values p ↔ ∃ d, p d = ofOrd a := by
  simp only [values, Finset.mem_biUnion, Finset.mem_univ, true_and, mem_ordValues]

theorem values_card_le (p : X → ExtOrd) : (values p).card ≤ Fintype.card X := by
  calc
    _ ≤ ∑ d : X, (ordValues (p d)).card := Finset.card_biUnion_le
    _ ≤ ∑ _d : X, 1 := by
      apply Finset.sum_le_sum
      intro d _
      rcases ExtOrd.cases (p d) with h | h | ⟨a, h⟩ <;> simp [h, ordValues, ofOrd]
    _ = _ := by simp

theorem eq_of_cap_eq_lt {x y h : ExtOrd} (he : min x h = min y h) (hx : x < h) :
    x = y := by
  have hy : y < h := by
    by_contra hn
    rw [min_eq_left hx.le, min_eq_right (not_lt.mp hn)] at he
    exact hx.ne he
  simpa only [min_eq_left hx.le, min_eq_left hy.le] using he

theorem values_prefix {p q : X → ExtOrd} {h : Ordinal.{0}}
    (hpq : ∀ d, min (p d) (ofOrd h) = min (q d) (ofOrd h)) :
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
  · simp only [normalize, hb]
    exact mem_codedAlphabet_iff.mpr (Or.inl rfl)
  · exact (hd ht).elim
  · rw [normalize_ofOrd ha]
    obtain hb | ⟨b, i, hb, hi, he⟩ := mem_codedAlphabet_iff.mp
      (encode_mem_sharp (j := j) (mem_values.mpr ⟨d, ha⟩))
    · exact mem_codedAlphabet_iff.mpr (Or.inl hb)
    · exact mem_codedAlphabet_iff.mpr (Or.inr
        ⟨b, i, hb.trans (Nat.mul_le_mul_left 2 (values_card_le p)), hi, he⟩)

theorem normalize_prefix {j : ℕ} {p q : X → ExtOrd} {h : Ordinal.{0}}
    (hh : j ≤ finitePart h)
    (hpq : ∀ d, min (p d) (ofOrd h) = min (q d) (ofOrd h))
    (d : X) (hd : p d < ofOrd h) : normalize j p d = normalize j q d := by
  have he := eq_of_cap_eq_lt (hpq d) hd
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · simp only [normalize, hb, ← he]
  · exact (not_lt_of_ge le_top (ht ▸ hd)).elim
  · rw [normalize_ofOrd ha, normalize_ofOrd (he.symm.trans ha)]
    exact encode_congr_below hh (values_prefix hpq) (ofOrd_lt_ofOrd.mp (ha ▸ hd))

end Profile

end
end VaughtConjecture.Knight.PairedSlotEncoding

namespace VaughtConjecture.Knight.RightFilledGap

open Transform Value ExtOrd

/-- The greatest grid value below the next floor, or bottom if none qualifies. -/
noncomputable def floor (G : Finset ExtOrd) (B : ExtOrd) : ExtOrd :=
  G.sup (fun z => if z ≤ B then z else ⊥)

theorem floor_le (G : Finset ExtOrd) (B : ExtOrd) : floor G B ≤ B := by
  apply Finset.sup_le
  intro z _
  split_ifs with hz
  · exact hz
  · exact bot_le

theorem le_floor {G : Finset ExtOrd} {h B : ExtOrd} (hh : h ∈ G) (hle : h ≤ B) :
    h ≤ floor G B := by
  unfold floor
  apply Finset.le_sup_of_le hh
  simp only [ite_eq_left hle, le_refl]

/-- A finite maximum creates no extra value between the grid points. -/
theorem floor_eq_bot_or_mem (G : Finset ExtOrd) (B : ExtOrd) :
    floor G B = ⊥ ∨ floor G B ∈ G := by
  apply Finset.sup_induction (p := fun z => z = ⊥ ∨ z ∈ G)
  · exact Or.inl rfl
  · intro a ha b hb
    rcases le_total a b with hab | hba
    · simpa only [sup_eq_right.mpr hab] using hb
    · simpa only [sup_eq_left.mpr hba] using ha
  · intro z hz
    split_ifs
    · exact Or.inr hz
    · exact Or.inl rfl

end VaughtConjecture.Knight.RightFilledGap

namespace VaughtConjecture.Knight.PairedSlotDecoder
open Transform Value ExtOrd PairedSlotEncoding
noncomputable section

def piece (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) : ExtOrd → ExtOrd := by
  classical
  exact if Orbit j S a then
    FiniteOrbitEmbedding.ray j (Ordinal.omega0 * block j S a) (limitPart a)
  else stepShifter (block j S a) ⊥ (ofOrd a)

theorem piece_witness {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}}
    (ha : a ∈ S) : Witness (gTop j) (piece j S a) := by
  unfold piece
  split_ifs with ho
  · exact (FiniteOrbitEmbedding.ray_step j (limitPart_idem a)).normalizedWitness
  · exact Witness.stepLimit j _ bot_le (selfVis_bot j)
      (selfVis_ofOrd_iff.mpr (by
        by_contra hn
        exact ho (orbit_of_invisible ha (not_le.mp hn))))

theorem piece_le (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) (x : ExtOrd) :
    piece j S a x ≤ ofOrd (ceiling j S a) := by
  unfold piece ceiling
  split_ifs with ho
  · exact FiniteOrbitEmbedding.ray_le _ _ _ _
  · rcases ExtOrd.cases x with rfl | rfl | ⟨b, rfl⟩
    · exact bot_le
    · exact le_rfl
    · change (if _ then _ else _) ≤ _
      split_ifs <;> simp

theorem piece_at {j : ℕ} {S : Finset Ordinal.{0}} {a b : Ordinal.{0}}
    (ha : a ∈ S) (hb : b ∈ S) (hk : key j S a = key j S b) :
    piece j S a (encode j S b) = ofOrd b := by
  have hblock := block_eq_of_key_eq ha hb hk
  have ho := orbit_iff_of_key_eq ha hb hk
  by_cases hoa : Orbit j S a
  · have hob := ho.mp hoa
    have hl : limitPart a = limitPart b := by
      simpa only [key, ite_eq_left hoa, ite_eq_left hob] using hk
    simp only [piece, ite_eq_left hoa, encode, offset, ite_eq_left hob, hblock]
    rw [FiniteOrbitEmbedding.ray_at j (limitPart_mul_nat _) hob.1, hl,
      limitPart_add_finitePart]
  · have hob : ¬ Orbit j S b := fun h => hoa (ho.mpr h)
    have hab : a = b := by
      simpa only [key, ite_eq_right hoa, ite_eq_right hob] using hk
    simp only [piece, ite_eq_right hoa, hab]
    apply stepShifter_of_ge
    exact ofOrd_le_ofOrd.mpr le_self_add

theorem piece_before {j : ℕ} {S : Finset Ordinal.{0}} {a b : Ordinal.{0}}
    (ha : a ∈ S) (hk : key j S a < key j S b) :
    piece j S b (encode j S a) = ⊥ := by
  have hb := block_lt_of_key_lt ha hk
  have hbo : (block j S a : Ordinal.{0}) < block j S b := Nat.cast_lt.mpr hb
  unfold piece
  split_ifs
  · rw [encode, FiniteOrbitEmbedding.ray_ofOrd, limitPart_mul_add,
      ite_eq_left (by simpa only [Nat.cast_zero, add_zero] using code_add_lt_mul hbo 0)]
  · exact stepShifter_of_lt (ofOrd_ne_bot _)
      (ofOrd_lt_ofOrd.mpr (code_add_lt_mul hbo _))

def occupied (j : ℕ) (S : Finset Ordinal.{0}) (x : ExtOrd) : ExtOrd :=
  S.sup (fun a => piece j S a x)

theorem occupied_witness (j : ℕ) (S : Finset Ordinal.{0}) :
    Witness (gTop j) (occupied j S) :=
  Witness.finset_sup (MixedGradeInterpolation.zero_witness j) S (fun _ ha => piece_witness ha)

theorem occupied_encode {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}}
    (ha : a ∈ S) : occupied j S (encode j S a) = ofOrd a := by
  apply le_antisymm
  · apply Finset.sup_le
    intro b hb
    rcases lt_trichotomy (key j S b) (key j S a) with hk | hk | hk
    · exact (piece_le j S b _).trans (ofOrd_le_ofOrd.mpr (ceiling_le_of_key_lt hk))
    · exact (piece_at hb ha hk).le
    · rw [piece_before ha hk]
      exact bot_le
  · rw [← piece_at ha ha rfl]
    exact Finset.le_sup (f := fun b => piece j S b (encode j S a)) ha
/-- The first source block not occupied by an earlier group. -/
def gapStart (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) : ℕ :=
  S.sup (fun b => if key j S b < key j S a then block j S b + 1 else 0)

theorem gapStart_le (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) :
    gapStart j S a ≤ block j S a := by
  apply Finset.sup_le
  intro b hb
  split_ifs with hk
  · exact block_lt_of_key_lt hb hk
  · exact Nat.zero_le _

theorem block_lt_gapStart {j : ℕ} {S : Finset Ordinal.{0}} {a b : Ordinal.{0}}
    (ha : a ∈ S) (hk : key j S a < key j S b) :
    block j S a < gapStart j S b := by
  change block j S a + 1 ≤ gapStart j S b
  unfold gapStart
  apply Finset.le_sup_of_le ha
  simp only [ite_eq_left hk, le_refl]

def gap (j : ℕ) (S : Finset Ordinal.{0}) (G : Finset ExtOrd)
    (a : Ordinal.{0}) : ExtOrd → ExtOrd :=
  stepShifter (gapStart j S a) ⊥ (RightFilledGap.floor G (ofOrd (key j S a)))

theorem step_zero_le (n : ℕ) (c x : ExtOrd) : stepShifter n ⊥ c x ≤ c := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨b, rfl⟩
  · exact bot_le
  · exact le_rfl
  · change (if _ then _ else _) ≤ _
    split_ifs <;> simp

theorem gap_witness {j : ℕ} {S : Finset Ordinal.{0}} {G : Finset ExtOrd}
    (hG : ∀ z ∈ G, SelfVis j z) (a : Ordinal.{0}) :
    Witness (gTop j) (gap j S G a) := by
  apply Witness.stepLimit j _ bot_le (selfVis_bot j)
  rcases RightFilledGap.floor_eq_bot_or_mem G (ofOrd (key j S a)) with hb | hm
  · rw [hb]; exact selfVis_bot j
  · exact hG _ hm

theorem gap_encode_le {j : ℕ} {S : Finset Ordinal.{0}} {G : Finset ExtOrd}
    {a b : Ordinal.{0}} (ha : a ∈ S) :
    gap j S G b (encode j S a) ≤ ofOrd a := by
  by_cases hk : key j S b ≤ key j S a
  · exact (step_zero_le _ _ _).trans ((RightFilledGap.floor_le _ _).trans
      (ofOrd_le_ofOrd.mpr (hk.trans (key_le j S a))))
  · have hblock := block_lt_gapStart ha (not_le.mp hk)
    have he : gap j S G b (encode j S a) = ⊥ :=
      stepShifter_of_lt (ofOrd_ne_bot _)
        (ofOrd_lt_ofOrd.mpr (code_add_lt_mul (Nat.cast_lt.mpr hblock) _))
    rw [he]
    exact bot_le

def tailStart (j : ℕ) (S : Finset Ordinal.{0}) : ℕ := S.sup (block j S) + 1

/-- Occupied pieces, right-filled gaps, and the terminal ceiling. -/
def decode (j : ℕ) (S : Finset Ordinal.{0}) (G : Finset ExtOrd)
    (C x : ExtOrd) : ExtOrd :=
  max (occupied j S x)
    (max (S.sup (fun a => gap j S G a x)) (stepShifter (tailStart j S) ⊥ C x))

theorem decode_witness {j : ℕ} {S : Finset Ordinal.{0}} {G : Finset ExtOrd} {C : ExtOrd}
    (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C) :
    Witness (gTop j) (decode j S G C) :=
  (occupied_witness j S).max
    ((Witness.finset_sup (MixedGradeInterpolation.zero_witness j) S
      (fun a _ => gap_witness hG a)).max
      (Witness.stepLimit j _ bot_le (selfVis_bot j) hC))

theorem decode_encode {j : ℕ} {S : Finset Ordinal.{0}} {G : Finset ExtOrd} {C : ExtOrd}
    {a : Ordinal.{0}} (ha : a ∈ S) : decode j S G C (encode j S a) = ofOrd a := by
  have htail : stepShifter (tailStart j S) ⊥ C (encode j S a) = ⊥ := by
    apply stepShifter_of_lt (ofOrd_ne_bot _)
    apply ofOrd_lt_ofOrd.mpr
    apply code_add_lt_mul
    exact Nat.cast_lt.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := block j S) ha))
  rw [decode, occupied_encode ha, htail, max_eq_left bot_le]
  apply max_eq_left
  apply Finset.sup_le
  intro b _
  exact gap_encode_le ha

theorem decode_gap_reaches {j : ℕ} {S : Finset Ordinal.{0}} {G : Finset ExtOrd}
    {C x h : ExtOrd} {a : Ordinal.{0}}
    (ha : a ∈ S) (hh : h ∈ G) (hfloor : h ≤ ofOrd (key j S a))
    (hx : ofOrd (Ordinal.omega0 * gapStart j S a) ≤ x) :
    h ≤ decode j S G C x := by
  have hg : gap j S G a x = RightFilledGap.floor G (ofOrd (key j S a)) :=
    stepShifter_of_ge hx
  calc h ≤ gap j S G a x := hg ▸ RightFilledGap.le_floor hh hfloor
    _ ≤ S.sup (fun b => gap j S G b x) := Finset.le_sup (f := fun b => gap j S G b x) ha
    _ ≤ decode j S G C x := (le_max_left _ _).trans (le_max_right _ _)

theorem decode_tail {j : ℕ} {S : Finset Ordinal.{0}} {G : Finset ExtOrd}
    {C x : ExtOrd} (hx : ofOrd (Ordinal.omega0 * tailStart j S) ≤ x) :
    C ≤ decode j S G C x := by
  have he := stepShifter_of_ge (c₀ := (⊥ : ExtOrd)) (c₁ := C) hx
  rw [decode, he]
  exact (le_max_right _ _).trans (le_max_right _ _)

theorem ceiling_eq_replace {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}}
    (ha : a ∈ S) : ofOrd (ceiling j S a) = extVisibilityReplace (ofOrd a) j j := by
  by_cases hf : finitePart a < j
  · simp only [ceiling, ite_eq_left (orbit_of_invisible ha hf),
      extVisibilityReplace_of_finitePart_lt hf]
  · rw [extVisibilityReplace_of_le_finitePart (not_lt.mp hf)]
    unfold ceiling
    split_ifs with ho
    · have he : finitePart a = j := le_antisymm ho.1 (not_lt.mp hf)
      rw [← he, limitPart_add_finitePart]
    · rfl

theorem decode_le {j : ℕ} {S : Finset Ordinal.{0}} {G : Finset ExtOrd} {C : ExtOrd}
    (hC : SelfVis j C) (hS : ∀ a ∈ S, ofOrd a ≤ C) (x : ExtOrd) :
    decode j S G C x ≤ C := by
  apply max_le
  · apply Finset.sup_le
    intro a ha
    apply (piece_le j S a x).trans
    rw [ceiling_eq_replace ha]
    exact extVisibilityReplace_le_of_le_selfVis le_rfl hC (hS a ha)
  · apply max_le
    · apply Finset.sup_le
      intro a ha
      exact (step_zero_le _ _ _).trans ((RightFilledGap.floor_le _ _).trans
        ((ofOrd_le_ofOrd.mpr (key_le j S a)).trans (hS a ha)))
    · exact step_zero_le _ _ _

section Profile
variable {X : Type*} [Fintype X]

theorem decode_normalize {j : ℕ} {p : X → ExtOrd} {G : Finset ExtOrd} {C : ExtOrd}
    (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C)
    (hp : ∀ d, p d ≠ ⊤) (d : X) :
    decode j (values p) G C (PairedSlotEncoding.normalize j p d) = p d := by
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · simp only [PairedSlotEncoding.normalize, hb]
    exact (decode_witness hG hC).bot
  · exact (hp d ht).elim
  · rw [normalize_ofOrd ha, ha]
    exact decode_encode (mem_values.mpr ⟨d, ha⟩)

omit [Fintype X] in
private theorem supported_max {K : ℕ} {G : Set ExtOrd} {p : X → ExtOrd} {a b : ExtOrd}
    (ha : OrbitPrefixSupport.Supported K G p a)
    (hb : OrbitPrefixSupport.Supported K G p b) :
    OrbitPrefixSupport.Supported K G p (max a b) := by
  rcases le_total a b with h | h
  · rwa [max_eq_right h]
  · rwa [max_eq_left h]

omit [Fintype X] in
private theorem supported_sup {I : Type*} (s : Finset I) {K : ℕ} {G : Set ExtOrd}
    {p : X → ExtOrd} {f : I → ExtOrd}
    (hf : ∀ a ∈ s, OrbitPrefixSupport.Supported K G p (f a)) :
    OrbitPrefixSupport.Supported K G p (s.sup f) := by
  classical
  apply Finset.sup_induction (p := OrbitPrefixSupport.Supported K G p)
  · exact Or.inl rfl
  · intro a ha b hb
    exact supported_max ha hb
  · exact hf

omit [Fintype X] in
private theorem supported_boundary {K : ℕ} {G : Set ExtOrd} {p : X → ExtOrd} (d : X) :
    OrbitPrefixSupport.Supported K G p (p d) := by
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · exact Or.inl hb
  · exact Or.inr (Or.inr ⟨d, K, le_rfl, by rw [ht, extVisibilityReplace_top]⟩)
  · by_cases hk : finitePart a < K
    · exact Or.inr (Or.inr ⟨d, finitePart a, hk.le, by
        rw [ha, extVisibilityReplace_of_finitePart_lt hk, limitPart_add_finitePart]⟩)
    · exact Or.inr (Or.inr ⟨d, K, le_rfl, by
        rw [ha, extVisibilityReplace_of_le_finitePart (not_lt.mp hk)]⟩)

theorem piece_supported {j K : ℕ} {p : X → ExtOrd} {G : Set ExtOrd}
    (hj : j ≤ K) {a : Ordinal.{0}} (ha : a ∈ values p) (x : ExtOrd) :
    OrbitPrefixSupport.Supported K G p (piece j (values p) a x) := by
  unfold piece
  split_ifs with ho
  · obtain ⟨b, hb, hbj, hba⟩ := ho.2
    obtain ⟨d, hd⟩ := mem_values.mp hb
    have hs (i : ℕ) (hi : i ≤ j) :
        OrbitPrefixSupport.Supported K G p (ofOrd (limitPart a + i)) :=
      Or.inr (Or.inr ⟨d, i, hi.trans hj, by
        rw [hd, extVisibilityReplace_of_finitePart_lt (hbj.trans_le hj), hba]⟩)
    rcases ExtOrd.cases x with rfl | rfl | ⟨b, rfl⟩
    · exact Or.inl rfl
    · exact hs j le_rfl
    · rw [FiniteOrbitEmbedding.ray_ofOrd]
      split_ifs
      · exact Or.inl rfl
      · exact hs _ (min_le_right _ _)
      · exact hs j le_rfl
  · obtain ⟨d, hd⟩ := mem_values.mp ha
    have hs : OrbitPrefixSupport.Supported K G p (ofOrd a) := hd ▸ supported_boundary d
    rcases ExtOrd.cases x with rfl | rfl | ⟨b, rfl⟩
    · exact Or.inl rfl
    · exact hs
    · change OrbitPrefixSupport.Supported K G p (if _ then _ else _)
      split_ifs <;> first | exact Or.inl rfl | exact hs

/-- Every output, not only the represented boundary values, has orbit support. -/
theorem decode_supported {j K : ℕ} {p : X → ExtOrd} {G : Finset ExtOrd} {C : ExtOrd}
    (hj : j ≤ K) (hC : C ∈ G) (x : ExtOrd) :
    OrbitPrefixSupport.Supported K (G : Set ExtOrd) p (decode j (values p) G C x) := by
  apply supported_max
  · exact supported_sup _ (fun a ha => piece_supported hj ha x)
  · apply supported_max
    · apply supported_sup
      intro a _
      have hs : OrbitPrefixSupport.Supported K (G : Set ExtOrd) p
          (RightFilledGap.floor G (ofOrd (key j (values p) a))) := by
        rcases RightFilledGap.floor_eq_bot_or_mem G _ with hb | hm
        · exact Or.inl hb
        · exact Or.inr (Or.inl hm)
      rcases ExtOrd.cases x with rfl | rfl | ⟨b, rfl⟩
      · exact Or.inl rfl
      · exact hs
      · change OrbitPrefixSupport.Supported K (G : Set ExtOrd) p (if _ then _ else _)
        split_ifs <;> first | exact Or.inl rfl | exact hs
    · rcases ExtOrd.cases x with rfl | rfl | ⟨b, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl hC)
      · change OrbitPrefixSupport.Supported K (G : Set ExtOrd) p (if _ then _ else _)
        split_ifs <;> first | exact Or.inl rfl | exact Or.inr (Or.inl hC)

end Profile

end
end VaughtConjecture.Knight.PairedSlotDecoder

namespace VaughtConjecture.Knight.PairedSlotIncoming
open Transform Value ExtOrd PairedSlotEncoding SharpWitnessComposition
noncomputable section

def after (a c x : ExtOrd) : ExtOrd := if a < x then c else ⊥

theorem after_bounded {j : ℕ} {a c : ExtOrd}
    (ha : SelfVis j a) (hc : SelfVis j c) : BoundedMap j (after a c) where
  bot := by simp [after]
  mono := by
    intro x y hxy
    by_cases hx : a < x
    · simp only [after, ite_eq_left hx, ite_eq_left (hx.trans_le hxy), le_refl]
    · simp only [after, ite_eq_right hx, bot_le]
  comm := by
    intro x k i hk hi
    have he : a < extVisibilityReplace x k i ↔ a < x := by
      simpa only [not_le] using not_congr (replace_le_visible_cut_iff ha hk hi)
    by_cases hx : a < x
    · simp only [after, ite_eq_left hx, ite_eq_left (he.mpr hx)]
      exact (evr_eq_self_of_selfVis (selfVis_mono hc hk) i).symm
    · simp only [after, ite_eq_right hx, ite_eq_right (fun h => hx (he.mp h)),
        extVisibilityReplace_bot]

theorem bounded_max {j : ℕ} {f g : ExtOrd → ExtOrd}
    (hf : BoundedMap j f) (hg : BoundedMap j g) :
    BoundedMap j (fun x => max (f x) (g x)) where
  bot := by rw [hf.bot, hg.bot, max_self]
  mono := fun _ _ h => max_le_max (hf.mono h) (hg.mono h)
  comm := by
    intro x k i hk hi
    rw [hf.comm x k i hk hi, hg.comm x k i hk hi, extVisibilityReplace_max _ _ hi]

theorem bounded_sup {I : Type*} {j : ℕ} (s : Finset I) (f : I → ExtOrd → ExtOrd)
    (hf : ∀ a ∈ s, BoundedMap j (f a)) : BoundedMap j (fun x => s.sup (fun a => f a x)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sup_empty] using
        (boundedMap_of_witness (MixedGradeInterpolation.zero_witness j))
  | @insert a s ha ih =>
      simpa only [Finset.sup_insert] using
        bounded_max (hf a (Finset.mem_insert_self a s))
          (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

def predecessor (a : Ordinal.{0}) : Ordinal.{0} := limitPart a + (finitePart a - 1 : ℕ)

theorem predecessor_lt {a : Ordinal.{0}} (ha : 0 < finitePart a) : predecessor a < a := by
  conv_rhs => rw [← limitPart_add_finitePart a]
  exact (add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr (by omega))

theorem le_predecessor_of_lt {a b : Ordinal.{0}} (ha : 0 < finitePart a)
    (hb : b < a) : b ≤ predecessor a := by
  rcases lt_or_eq_of_le (limitPart_mono hb.le) with hl | hl
  · exact (lt_limitPart_of_limitPart_lt hl).le.trans le_self_add
  · have hf : finitePart b < finitePart a := by
      by_contra hn
      exact hb.not_ge (le_of_finitePart_le hl.symm (not_lt.mp hn))
    rw [← limitPart_add_finitePart b, predecessor, hl]
    exact add_le_add_right (Nat.cast_le.mpr (by omega)) _

def piece (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) : ExtOrd → ExtOrd :=
  if finitePart a ≤ j then
    FiniteOrbitEmbedding.ray j (limitPart a) (Ordinal.omega0 * block j S a)
  else after (ofOrd (predecessor a)) (encode j S a)

theorem piece_bounded (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) :
    BoundedMap j (piece j S a) := by
  unfold piece
  split_ifs with ha
  · exact boundedMap_of_witness
      (FiniteOrbitEmbedding.ray_step j (limitPart_mul_nat _)).normalizedWitness
  · apply after_bounded
    · apply selfVis_ofOrd_iff.mpr
      rw [predecessor, finitePart_limitPart_add_nat]
      omega
    · exact encode_visible le_rfl (not_le.mp ha).le

theorem offset_eq_min {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}}
    (ha : a ∈ S) : offset j S a = min (finitePart a) j := by
  by_cases h : finitePart a < j
  · simp only [offset, ite_eq_left (orbit_of_invisible ha h), min_eq_left h.le]
  · unfold offset
    split_ifs with ho
    · have he : finitePart a = j := le_antisymm ho.1 (not_lt.mp h)
      simp only [he, min_self]
    · exact (min_eq_right (not_lt.mp h)).symm

theorem piece_at {j : ℕ} {S : Finset Ordinal.{0}} {a b : Ordinal.{0}}
    (ha : a ∈ S) (hb : b ∈ S) (hk : key j S a = key j S b) :
    piece j S a (ofOrd b) = encode j S b := by
  have hblock := block_eq_of_key_eq ha hb hk
  by_cases ho : Orbit j S a
  · have hob := (orbit_iff_of_key_eq ha hb hk).mp ho
    have hl : limitPart a = limitPart b := by
      simpa only [key, ite_eq_left ho, ite_eq_left hob] using hk
    rw [piece, ite_eq_left ho.1, encode, offset, ite_eq_left hob, hblock, hl]
    simpa only [limitPart_add_finitePart] using
      (FiniteOrbitEmbedding.ray_at j (ν := Ordinal.omega0 * block j S b)
        (limitPart_idem b) hob.1)
  · have hob : ¬ Orbit j S b := fun h => ho ((orbit_iff_of_key_eq ha hb hk).mpr h)
    have hab : a = b := by simpa only [key, ite_eq_right ho, ite_eq_right hob] using hk
    subst b
    by_cases hf : finitePart a ≤ j
    · rw [piece, ite_eq_left hf, encode, offset_eq_min ha, min_eq_left hf]
      simpa only [limitPart_add_finitePart] using
        (FiniteOrbitEmbedding.ray_at j (ν := Ordinal.omega0 * block j S a)
          (limitPart_idem a) hf)
    · rw [piece, ite_eq_right hf, after, ite_eq_left
        (ofOrd_lt_ofOrd.mpr (predecessor_lt (by omega : 0 < finitePart a)))]

theorem piece_le (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) (x : ExtOrd) :
    piece j S a x ≤ ofOrd (Ordinal.omega0 * block j S a + j) := by
  unfold piece
  split_ifs
  · exact FiniteOrbitEmbedding.ray_le _ _ _ _
  · unfold after
    split_ifs
    · exact ofOrd_le_ofOrd.mpr
        (add_le_add_right (Nat.cast_le.mpr (offset_le j S a)) _)
    · exact bot_le

theorem piece_before {j : ℕ} {S : Finset Ordinal.{0}} {a b : Ordinal.{0}}
    (hb : b ∈ S) (hk : key j S b < key j S a) : piece j S a (ofOrd b) = ⊥ := by
  have hba : b < a := by
    by_contra hn
    exact hk.not_ge (key_mono j S (not_lt.mp hn))
  unfold piece
  split_ifs with ha
  · have hl : limitPart b < limitPart a := by
      apply lt_of_le_of_ne (limitPart_mono hba.le)
      intro he
      have hf : finitePart b < finitePart a := by
        by_contra hn
        exact hba.not_ge (le_of_finitePart_le he.symm (not_lt.mp hn))
      have hob := orbit_of_invisible hb (hf.trans_le ha)
      have hoa : Orbit j S a := ⟨ha, b, hb, hf.trans_le ha, he⟩
      simp only [key, ite_eq_left hoa, ite_eq_left hob, he, lt_self_iff_false] at hk
    rw [FiniteOrbitEmbedding.ray_ofOrd, ite_eq_left hl]
  · exact ite_eq_right (not_lt.mpr
      (ofOrd_le_ofOrd.mpr (le_predecessor_of_lt (by omega) hba)))

/-- A scalar encoder on every input, not only on the represented finite values. -/
def incoming (j : ℕ) (S : Finset Ordinal.{0}) (x : ExtOrd) : ExtOrd :=
  max (FiniteOrbitEmbedding.ray j 0 0 x) (S.sup (fun a => piece j S a x))

theorem incoming_bounded (j : ℕ) (S : Finset Ordinal.{0}) :
    BoundedMap j (incoming j S) :=
  bounded_max (boundedMap_of_witness (FiniteOrbitEmbedding.ray_step j
    (by simpa only [Nat.cast_zero] using limitPart_natCast 0)).normalizedWitness)
    (bounded_sup S _ (fun a _ => piece_bounded j S a))

theorem incoming_reflects_bottom (j : ℕ) (S : Finset Ordinal.{0}) (x : ExtOrd)
    (hx : incoming j S x = ⊥) : x = ⊥ :=
  FiniteOrbitEmbedding.baseline_reflects_bottom j x
    (le_bot_iff.mp ((le_max_left _ _).trans_eq hx))

theorem incoming_at {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}} (ha : a ∈ S) :
    incoming j S (ofOrd a) = encode j S a := by
  apply le_antisymm
  · apply max_le
    · apply (FiniteOrbitEmbedding.ray_le j 0 0 _).trans
      apply ofOrd_le_ofOrd.mpr
      rw [zero_add]
      have hblock : ((0 : ℕ) : Ordinal.{0}) < block j S a :=
        Nat.cast_lt.mpr (block_pos j S a)
      have hlow : (j : Ordinal.{0}) ≤ Ordinal.omega0 * block j S a := by
        simpa only [Nat.cast_zero, mul_zero, zero_add] using (code_add_lt_mul hblock j).le
      exact hlow.trans le_self_add
    · apply Finset.sup_le
      intro b hb
      rcases lt_trichotomy (key j S b) (key j S a) with hk | hk | hk
      · apply (piece_le j S b _).trans
        exact ofOrd_le_ofOrd.mpr ((code_add_lt_mul
          (Nat.cast_lt.mpr (block_lt_of_key_lt hb hk)) j).le.trans le_self_add)
      · exact (piece_at hb ha hk).le
      · rw [piece_before ha hk]
        exact bot_le
  · calc encode j S a = piece j S a (ofOrd a) := (piece_at ha ha rfl).symm
         _ ≤ S.sup (fun b => piece j S b (ofOrd a)) :=
           Finset.le_sup (f := fun b => piece j S b (ofOrd a)) ha
         _ ≤ incoming j S (ofOrd a) := le_max_right _ _

/-! ## Literal top and semantic transport -/

/-- Preserve literal top as well as all the finite represented values. -/
def encoder (j : ℕ) (S : Finset Ordinal.{0}) (x : ExtOrd) : ExtOrd :=
  if x = ⊤ then ⊤ else incoming j S x

theorem encoder_bounded (j : ℕ) (S : Finset Ordinal.{0}) :
    BoundedMap j (encoder j S) where
  bot := by simpa only [encoder, bot_ne_top, ite_false] using (incoming_bounded j S).bot
  mono := by
    intro x y hxy
    by_cases hy : y = ⊤
    · simp only [encoder, hy, ite_true, le_top]
    · have hx : x ≠ ⊤ := fun hx => hy (top_le_iff.mp (hx ▸ hxy))
      simpa only [encoder, ite_eq_right hx, ite_eq_right hy] using
        (incoming_bounded j S).mono hxy
  comm := by
    intro x k i hk hi
    rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
    · simp only [encoder, extVisibilityReplace_bot, bot_ne_top, ite_false,
        (incoming_bounded j S).bot]
    · simp only [encoder, extVisibilityReplace_top, ite_true]
    · simpa only [encoder, extVisibilityReplace_ofOrd, ofOrd_ne_top, ite_false] using
        (incoming_bounded j S).comm (ofOrd a) k i hk hi

theorem encoder_reflects_bottom (j : ℕ) (S : Finset Ordinal.{0}) (x : ExtOrd)
    (hx : encoder j S x = ⊥) : x = ⊥ := by
  unfold encoder at hx
  split_ifs at hx with ht
  · exact (top_ne_bot hx).elim
  · exact incoming_reflects_bottom j S x hx

/-- Bottom reflection supplies the clause-5 tail above the bounded commutation range. -/
theorem witness_of_bounded_reflecting {j : ℕ} {f : ExtOrd → ExtOrd}
    (hf : BoundedMap j f) (hbot : ∀ x, f x = ⊥ → x = ⊥) : Witness (gTop j) f where
  anti := (witness_id j).anti
  vis := (witness_id j).vis
  bot := hf.bot
  mono := hf.mono
  clause5 := by
    intro x k hact i hi
    by_cases hk : k ≤ j
    · exact hf.comm x k i hk hi
    · have hz : f x = ⊥ := by rwa [gTop_of_gt (not_le.mp hk), le_bot_iff] at hact
      rw [hbot x hz, extVisibilityReplace_bot, hf.bot, extVisibilityReplace_bot]

theorem encoder_witness (j : ℕ) (S : Finset Ordinal.{0}) :
    Witness (gTop j) (encoder j S) :=
  witness_of_bounded_reflecting (encoder_bounded j S) (encoder_reflects_bottom j S)

theorem encoder_at {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}} (ha : a ∈ S) :
    encoder j S (ofOrd a) = encode j S a := by
  simpa only [encoder, ofOrd_ne_top, ite_false] using incoming_at ha

section Profile
variable {X : Type*} [Fintype X]

theorem encoder_profile (j : ℕ) (p : X → ExtOrd) (d : X) :
    encoder j (values p) (p d) = PairedSlotEncoding.normalize j p d := by
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · simpa only [PairedSlotEncoding.normalize, hb] using (encoder_bounded j (values p)).bot
  · simp only [encoder, ht, ite_true, PairedSlotEncoding.normalize]
  · rw [normalize_ofOrd ha, ha]
    exact encoder_at (mem_values.mpr ⟨d, ha⟩)

end Profile

end
end VaughtConjecture.Knight.PairedSlotIncoming
