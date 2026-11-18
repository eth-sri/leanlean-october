/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PairedSlotComparison

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalPairedEncoding
open Transform Value ExtOrd PairedSlotEncoding
noncomputable section

def codeOrd (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) : Ordinal.{0} :=
  Ordinal.omega0 * block j S a + offset j S a

def codedValues (j : ℕ) (S : Finset Ordinal.{0}) : Finset Ordinal.{0} :=
  S.image (codeOrd j S)

theorem codeOrd_finitePart (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) :
    finitePart (codeOrd j S a) = offset j S a := by
  exact finitePart_mul_add _ _

theorem codeOrd_limitPart (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) :
    limitPart (codeOrd j S a) = Ordinal.omega0 * block j S a := by
  exact limitPart_mul_add _ _

theorem orbit_codeOrd_iff {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}}
    (ha : a ∈ S) : Orbit j (codedValues j S) (codeOrd j S a) ↔ Orbit j S a := by
  classical
  constructor
  · rintro ⟨_, b, hb, hbj, hba⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hb
    rw [codeOrd_finitePart] at hbj
    have hob : Orbit j S b := by
      by_contra hn
      simp only [offset, ite_eq_right hn, lt_self_iff_false] at hbj
    have he : block j S b = block j S a := by
      simp only [codeOrd_limitPart] at hba
      have h := congrArg blockIdx hba
      have hz (n : ℕ) : blockIdx (Ordinal.omega0 * n) = (n : Ordinal.{0}) := by
        simpa only [Nat.cast_zero, add_zero] using blockIdx_mul_add n 0
      simpa only [hz, Nat.cast_inj] using h
    by_contra hoa
    simp only [block, ite_eq_left hob, ite_eq_right hoa] at he
    omega
  · intro hoa
    obtain ⟨b, hb, hbj, hk⟩ := orbit_witness_key hoa
    have hob := orbit_of_invisible hb hbj
    refine ⟨by rw [codeOrd_finitePart]; exact offset_le _ _ _,
      codeOrd j S b, Finset.mem_image_of_mem _ hb, ?_, ?_⟩
    · simpa only [codeOrd_finitePart, offset, ite_eq_left hob] using hbj
    · simp only [codeOrd_limitPart, block_eq_of_key_eq hb ha hk]

theorem key_codeOrd_eq_of_key_eq {j : ℕ} {S : Finset Ordinal.{0}} {a b : Ordinal.{0}}
    (ha : a ∈ S) (hb : b ∈ S) (hk : key j S a = key j S b) :
    key j (codedValues j S) (codeOrd j S a) =
      key j (codedValues j S) (codeOrd j S b) := by
  classical
  have he := block_eq_of_key_eq ha hb hk
  by_cases hoa : Orbit j S a
  · have hob := (orbit_iff_of_key_eq ha hb hk).mp hoa
    simp only [key, ite_eq_left ((orbit_codeOrd_iff ha).mpr hoa),
      ite_eq_left ((orbit_codeOrd_iff hb).mpr hob), codeOrd_limitPart, he]
  · have hob : ¬ Orbit j S b := fun h => hoa ((orbit_iff_of_key_eq ha hb hk).mpr h)
    have hab : a = b := by simpa only [key, ite_eq_right hoa, ite_eq_right hob] using hk
    rw [hab]

theorem key_codeOrd_lt_of_key_lt {j : ℕ} {S : Finset Ordinal.{0}} {a b : Ordinal.{0}}
    (ha : a ∈ S) (hk : key j S a < key j S b) :
    key j (codedValues j S) (codeOrd j S a) <
      key j (codedValues j S) (codeOrd j S b) := by
  have he := block_lt_of_key_lt ha hk
  have hlt : codeOrd j S a < limitPart (codeOrd j S b) := by
    rw [codeOrd_limitPart]
    exact code_add_lt_mul (Nat.cast_lt.mpr he) _
  apply (key_le _ _ _).trans_lt
  apply hlt.trans_le
  unfold key
  split_ifs
  · exact le_rfl
  · exact limitPart_le _

theorem key_codeOrd_lt_iff {j : ℕ} {S : Finset Ordinal.{0}} {a b : Ordinal.{0}}
    (ha : a ∈ S) (hb : b ∈ S) :
    key j (codedValues j S) (codeOrd j S a) <
      key j (codedValues j S) (codeOrd j S b) ↔ key j S a < key j S b := by
  constructor
  · intro h
    rcases lt_trichotomy (key j S a) (key j S b) with hlt | he | hgt
    · exact hlt
    · exact (h.ne (key_codeOrd_eq_of_key_eq ha hb he)).elim
    · exact (lt_asymm h (key_codeOrd_lt_of_key_lt hb hgt)).elim
  · exact key_codeOrd_lt_of_key_lt ha

theorem key_codeOrd_eq_iff {j : ℕ} {S : Finset Ordinal.{0}} {a b : Ordinal.{0}}
    (ha : a ∈ S) (hb : b ∈ S) :
    key j (codedValues j S) (codeOrd j S a) =
      key j (codedValues j S) (codeOrd j S b) ↔ key j S a = key j S b := by
  constructor
  · intro h
    rcases lt_trichotomy (key j S a) (key j S b) with hlt | he | hgt
    · exact ((key_codeOrd_lt_of_key_lt ha hlt).ne h).elim
    · exact he
    · exact ((key_codeOrd_lt_of_key_lt hb hgt).ne h.symm).elim
  · exact key_codeOrd_eq_of_key_eq ha hb

theorem rank_codeOrd {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}}
    (ha : a ∈ S) : rank j (codedValues j S) (codeOrd j S a) = rank j S a := by
  classical
  let rep (x : Ordinal.{0}) (hx : x ∈ PairedSlotEncoding.keys j S) : Ordinal.{0} :=
    Classical.choose (Finset.mem_image.mp hx)
  have rep_spec (x : Ordinal.{0}) (hx : x ∈ PairedSlotEncoding.keys j S) :
      rep x hx ∈ S ∧ key j S (rep x hx) = x :=
    Classical.choose_spec (Finset.mem_image.mp hx)
  unfold PairedSlotEncoding.rank
  symm
  apply Finset.card_bij (fun x hx =>
    key j (codedValues j S) (codeOrd j S (rep x (Finset.mem_filter.mp hx).1)))
  · intro x hx
    obtain ⟨hm, hl⟩ := Finset.mem_filter.mp hx
    obtain ⟨hr, he⟩ := rep_spec x hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _
      (Finset.mem_image_of_mem _ hr),
      key_codeOrd_lt_of_key_lt hr (lt_of_eq_of_lt he hl)⟩
  · intro x hx y hy he
    obtain ⟨hr, hx'⟩ := rep_spec x (Finset.mem_filter.mp hx).1
    obtain ⟨hs, hy'⟩ := rep_spec y (Finset.mem_filter.mp hy).1
    exact hx'.symm.trans (((key_codeOrd_eq_iff hr hs).mp he).trans hy')
  · intro y hy
    obtain ⟨hy, hlt⟩ := Finset.mem_filter.mp hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hw
    subst w
    have hk : key j S b ∈ PairedSlotEncoding.keys j S := Finset.mem_image_of_mem _ hb
    have hm : key j S b ∈ (PairedSlotEncoding.keys j S).filter (fun x => x < key j S a) :=
      Finset.mem_filter.mpr ⟨hk, (key_codeOrd_lt_iff hb ha).mp hlt⟩
    refine ⟨key j S b, hm, ?_⟩
    exact key_codeOrd_eq_of_key_eq (rep_spec _ hk).1 hb (rep_spec _ hk).2

theorem encode_codeOrd {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}}
    (ha : a ∈ S) : encode j (codedValues j S) (codeOrd j S a) = encode j S a := by
  classical
  have hr := rank_codeOrd (j := j) ha
  by_cases ho : Orbit j S a
  · have hc := (orbit_codeOrd_iff ha).mpr ho
    simp only [encode, block, offset, ite_eq_left ho, ite_eq_left hc, hr,
      codeOrd_finitePart]
  · have hc : ¬ Orbit j (codedValues j S) (codeOrd j S a) :=
      fun h => ho ((orbit_codeOrd_iff ha).mp h)
    simp only [encode, block, offset, ite_eq_right ho, ite_eq_right hc, hr]

section Profile
variable {X : Type*} [Fintype X]

theorem values_normalize (j : ℕ) (p : X → ExtOrd) :
    values (normalize j p) = codedValues j (values p) := by
  classical
  ext a
  rw [mem_values, codedValues, Finset.mem_image]
  constructor
  · rintro ⟨d, hd⟩
    rcases ExtOrd.cases (p d) with hb | ht | ⟨b, hb⟩
    · simp only [PairedSlotEncoding.normalize, hb] at hd
      exact (ofOrd_ne_bot _ hd.symm).elim
    · simp only [PairedSlotEncoding.normalize, ht] at hd
      exact (ofOrd_ne_top _ hd.symm).elim
    · exact ⟨b, mem_values.mpr ⟨d, hb⟩, ofOrd_inj.mp ((normalize_ofOrd hb).symm.trans hd)⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨d, hd⟩ := mem_values.mp hb
    exact ⟨d, normalize_ofOrd hd⟩

/-- Paired normalization is a retraction, with no bound on the original ordinals.
Literal top stays top; membership of the finite proper catalogue is separate. -/
theorem normalize_idempotent (j : ℕ) (p : X → ExtOrd) :
    normalize j (normalize j p) = normalize j p := by
  funext d
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · simp only [PairedSlotEncoding.normalize, hb]
  · simp only [PairedSlotEncoding.normalize, ht]
  · rw [normalize_ofOrd (normalize_ofOrd ha), values_normalize, normalize_ofOrd ha]
    exact encode_codeOrd (mem_values.mpr ⟨d, ha⟩)

end Profile
end
end VaughtConjecture.Knight.CanonicalPairedEncoding

namespace VaughtConjecture.Knight.CanonicalPairedPrefix
open Transform Value ExtOrd PairedSlotEncoding CanonicalPairedEncoding
noncomputable section

def lowerGroups (j : ℕ) (S : Finset Ordinal.{0}) (h : Ordinal.{0}) : ℕ :=
  ((PairedSlotEncoding.keys j S).filter (· < h)).card

/-- If a canonical field reaches a grid cut, the unchanged lower groups leave
enough room for a new point group at or above that cut. -/
theorem cut_le_next_slot {j B : ℕ} {S : Finset Ordinal.{0}}
    (hc : ∀ a ∈ S, encode j S a = ofOrd a)
    (hu : ∃ a ∈ S, Ordinal.omega0 * B + j ≤ a) :
    (Ordinal.omega0 : Ordinal.{0}) * B + j ≤
      Ordinal.omega0 * (2 * lowerGroups j S (Ordinal.omega0 * B + j) + 1 : ℕ) + j := by
  classical
  let h := Ordinal.omega0 * B + j
  let U := S.filter (fun a => h ≤ a)
  have hU : U.Nonempty := by
    obtain ⟨a, ha, hh⟩ := hu
    exact ⟨a, Finset.mem_filter.mpr ⟨ha, hh⟩⟩
  obtain ⟨a, haU, hmin⟩ := U.exists_min_image id hU
  have ha := (Finset.mem_filter.mp haU).1
  have hha : h ≤ a := (Finset.mem_filter.mp haU).2
  have he : a = codeOrd j S a := (ofOrd_inj.mp (hc a ha)).symm
  by_cases hk : key j S a < h
  · have hr : PairedSlotEncoding.rank j S a < lowerGroups j S h := by
      apply Finset.card_lt_card
      apply (Finset.ssubset_iff_of_subset (fun x hx =>
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,
          (Finset.mem_filter.mp hx).2.trans hk⟩)).mpr
      exact ⟨key j S a, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ ha, hk⟩,
        by simp⟩
    have hb : block j S a ≤ 2 * lowerGroups j S h + 1 := by
      unfold block
      split_ifs <;> omega
    apply hha.trans
    rw [he]
    exact add_le_add (by gcongr) (Nat.cast_le.mpr (offset_le j S a))
  · have hf : (PairedSlotEncoding.keys j S).filter (· < key j S a) =
        (PairedSlotEncoding.keys j S).filter (· < h) := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hx, hxa⟩
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
        have hba : b < a := by
          by_contra hn
          exact hxa.not_ge (key_mono j S (not_lt.mp hn))
        have hbh : b < h := by
          by_contra hn
          exact hba.not_ge (hmin b (Finset.mem_filter.mpr ⟨hb, not_lt.mp hn⟩))
        exact ⟨Finset.mem_image_of_mem _ hb, (key_le j S b).trans_lt hbh⟩
      · rintro ⟨hx, hxh⟩
        exact ⟨hx, hxh.trans_le (not_lt.mp hk)⟩
    have hr : PairedSlotEncoding.rank j S a = lowerGroups j S h := congrArg Finset.card hf
    by_cases ho : Orbit j S a
    · obtain ⟨b, hb, hbj, hba⟩ := ho.2
      have hhb : h ≤ b := by
        apply (not_lt.mp hk).trans
        simpa only [key, ite_eq_left ho, ← hba] using limitPart_le b
      have hab := hmin b (Finset.mem_filter.mpr ⟨hb, hhb⟩)
      have haj : finitePart a < j :=
        (finitePart_le_of_le_of_limitPart_eq hab hba.symm).trans_lt hbj
      have hB : B ≤ 2 * lowerGroups j S h + 1 := by
        by_contra hn
        have hblock : block j S a ≤ B := by
          simp only [block, ite_eq_left ho, hr]
          omega
        have hsmall : a < h := by
          rw [he]
          apply lt_of_lt_of_le
            ((add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr
              (show offset j S a < j by simpa only [offset, ite_eq_left ho] using haj)))
          exact add_le_add (by gcongr) le_rfl
        exact hsmall.not_ge hha
      exact add_le_add (by gcongr) le_rfl
    · have hh : codeOrd j S a =
          Ordinal.omega0 * (2 * lowerGroups j S h + 1 : ℕ) + j := by
        simp only [codeOrd, block, offset, ite_eq_right ho, hr]
      exact hha.trans_eq (he.trans hh)

section Profile
variable {X : Type*} [Fintype X]

theorem fixed_values {j : ℕ} {p : X → ExtOrd}
    (hc : normalize j p = p) : ∀ a ∈ values p, encode j (values p) a = ofOrd a := by
  intro a ha
  obtain ⟨d, hd⟩ := mem_values.mp ha
  exact (normalize_ofOrd hd).symm.trans ((congrFun hc d).trans hd)

theorem normalize_upper {j B : ℕ} {p q : X → ExtOrd}
    (hc : normalize j p = p) (hp : ∀ d, p d ≠ ⊤)
    (hag : ∀ d, min (p d) (ofOrd (Ordinal.omega0 * B + j)) =
      min (q d) (ofOrd (Ordinal.omega0 * B + j)))
    (d : X) (hd : ofOrd (Ordinal.omega0 * B + j) ≤ q d) :
    ofOrd (Ordinal.omega0 * B + j) ≤ normalize j q d := by
  classical
  let h := Ordinal.omega0 * B + j
  have hv : j ≤ finitePart h := by simp only [h, finitePart_mul_add, le_refl]
  have hpref := keys_prefix hv (values_prefix hag)
  have hl : lowerGroups j (values p) h = lowerGroups j (values q) h :=
    congrArg Finset.card hpref
  have hpd : ofOrd h ≤ p d := by
    have he := hag d
    rw [min_eq_right hd] at he
    exact (min_eq_right_iff.mp he)
  have hu : ∃ a ∈ values p, h ≤ a := by
    rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
    · exact (ofOrd_ne_bot h (le_bot_iff.mp (hb ▸ hpd))).elim
    · exact (hp d ht).elim
    · exact ⟨a, mem_values.mpr ⟨d, ha⟩, ofOrd_le_ofOrd.mp (ha ▸ hpd)⟩
  have hbound := cut_le_next_slot (B := B) (fixed_values hc) hu
  rw [hl] at hbound
  rcases ExtOrd.cases (q d) with hb | ht | ⟨a, ha⟩
  · exact (ofOrd_ne_bot h (le_bot_iff.mp (hb ▸ hd))).elim
  · simp only [PairedSlotEncoding.normalize, ht, le_top]
  · have haS : a ∈ values q := mem_values.mpr ⟨d, ha⟩
    have hha : h ≤ a := ofOrd_le_ofOrd.mp (ha ▸ hd)
    by_cases hk : key j (values q) a < h
    · have ho : Orbit j (values q) a := by
        by_contra hn
        simp only [key, ite_eq_right hn] at hk
        exact hk.not_ge hha
      obtain ⟨b, hbS, hbj, hba⟩ := ho.2
      have hbh : b < h := invisible_lt_cut hbj hv (by
        simpa only [key, ite_eq_left ho, ← hba] using hk)
      obtain ⟨e, he⟩ := mem_values.mp hbS
      have hlow : normalize j q e = q e := by
        have heqOld : p e = q e :=
          (eq_of_cap_eq_lt (hag e).symm (he ▸ ofOrd_lt_ofOrd.mpr hbh)).symm
        have hpe : p e < ofOrd h := heqOld ▸ he ▸ ofOrd_lt_ofOrd.mpr hbh
        calc
          normalize j q e = normalize j p e := (normalize_prefix hv hag e hpe).symm
          _ = p e := congrFun hc e
          _ = q e := heqOld
      have haround : ofOrd a ≤ extVisibilityReplace (ofOrd b) j j := by
        rw [extVisibilityReplace_ofOrd, visibilityReplace, ite_eq_left hbj,
          ordinalReplace, hba]
        apply ofOrd_le_ofOrd.mpr
        calc
          a = limitPart a + finitePart a := (limitPart_add_finitePart a).symm
          _ ≤ limitPart a + j := add_le_add_right (Nat.cast_le.mpr ho.1) _
      have hround : extVisibilityReplace (ofOrd b) j j = ofOrd h := by
        apply le_antisymm
        · exact (evr_mono (ofOrd_lt_ofOrd.mpr hbh).le (le_refl j)).trans_eq
            (selfVis_ofOrd_iff.mpr hv)
        · exact (ofOrd_le_ofOrd.mpr hha).trans haround
      have heq : ofOrd a = ofOrd h := le_antisymm
        (haround.trans_eq hround) (ofOrd_le_ofOrd.mpr hha)
      have hw := (PairedSlotIncoming.encoder_bounded j (values q)).comm
        (ofOrd b) j j le_rfl le_rfl
      rw [hround, ← heq, PairedSlotIncoming.encoder_at haS,
        ← he, PairedSlotIncoming.encoder_profile, hlow, he, hround] at hw
      rw [normalize_ofOrd ha, hw]
    · have hr : lowerGroups j (values q) h ≤ PairedSlotEncoding.rank j (values q) a :=
        Finset.card_le_card (fun x hx => Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2.trans_le (not_lt.mp hk)⟩)
      rw [normalize_ofOrd ha]
      apply ofOrd_le_ofOrd.mpr
      apply hbound.trans
      by_cases ho : Orbit j (values q) a
      · have hb : 2 * lowerGroups j (values q) h + 1 < block j (values q) a := by
          simp only [block, ite_eq_left ho]
          omega
        exact (code_add_lt_mul (Nat.cast_lt.mpr hb) j).le.trans le_self_add
      · have hb : 2 * lowerGroups j (values q) h + 1 ≤ block j (values q) a := by
          simp only [block, ite_eq_right ho]
          omega
        exact add_le_add (by gcongr) (by simp only [offset, ite_eq_right ho, le_refl])

/-- Relative normalization retains the entire original cut, not only the
coordinates strictly below it. The ambient must be a proper canonical fixed point. -/
theorem normalize_cap {j B : ℕ} {p q : X → ExtOrd}
    (hc : normalize j p = p) (hp : ∀ d, p d ≠ ⊤)
    (hag : ∀ d, min (p d) (ofOrd (Ordinal.omega0 * B + j)) =
      min (q d) (ofOrd (Ordinal.omega0 * B + j))) (d : X) :
    min (normalize j q d) (ofOrd (Ordinal.omega0 * B + j)) =
      min (p d) (ofOrd (Ordinal.omega0 * B + j)) := by
  by_cases hd : p d < ofOrd (Ordinal.omega0 * B + j)
  · rw [← normalize_prefix (by simp only [finitePart_mul_add, le_refl]) hag d hd, hc]
  · have hqd : ofOrd (Ordinal.omega0 * B + j) ≤ q d := by
      have he := hag d
      rw [min_eq_right (not_lt.mp hd)] at he
      exact min_eq_right_iff.mp he.symm
    rw [min_eq_right (normalize_upper hc hp hag d hqd), min_eq_right (not_lt.mp hd)]

end Profile
end
end VaughtConjecture.Knight.CanonicalPairedPrefix

namespace VaughtConjecture.Knight.CanonicalPairedProfiles
open Transform Value ExtOrd PairedSlotEncoding PairedSlotProfiles SharpWitnessComposition
noncomputable section

section Inventory
variable (X : Type*) [Fintype X] (j : ℕ)

/-- Proper canonical fixed points on the complete inventory. -/
def inventory : Set (X → ExtOrd) :=
  {p | PairedSlotEncoding.normalize j p = p ∧ ∀ d, p d ≠ ⊤}

theorem inventory_coded {p : X → ExtOrd} (hp : p ∈ inventory X j) (d : X) :
    p d ∈ ExtOrd.codedAlphabet (2 * Fintype.card X) j := by
  rw [← congrFun hp.1 d]
  exact normalize_mem j p d (hp.2 d)

theorem inventory_finite : (inventory X j).Finite :=
  (ExtOrd.codedLabellings_finite X (2 * Fintype.card X) j).subset
    (fun _ hp => inventory_coded X j hp)

theorem inventory_short {p : X → ExtOrd} (hp : p ∈ inventory X j) (d : X) :
    Short j (p d) := by
  rw [← congrFun hp.1 d]
  exact normalize_short j p d

theorem inventory_bound {p : X → ExtOrd} (hp : p ∈ inventory X j) (d : X) :
    p d ≤ sourceCeiling j X := by
  rw [← congrFun hp.1 d]
  exact normalize_le_ceiling hp.2 d

theorem normalize_mem_inventory {p : X → ExtOrd} (hp : ∀ d, p d ≠ ⊤) :
    PairedSlotEncoding.normalize j p ∈ inventory X j := by
  refine ⟨CanonicalPairedEncoding.normalize_idempotent j p, ?_⟩
  intro d
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · simpa only [PairedSlotEncoding.normalize, hb] using
      (show (⊥ : ExtOrd) ≠ ⊤ from hb ▸ hp d)
  · exact (hp d ht).elim
  · rw [normalize_ofOrd ha]
    exact ofOrd_ne_top _

/-- The relative prefix theorem applies coordinatewise to the full field vector,
including auxiliary fields, and uses the original grid cut. -/
theorem normalize_cap {a p : X → ExtOrd} {B : ℕ}
    (ha : a ∈ inventory X j)
    (hag : ∀ d, min (a d) (ofOrd (Ordinal.omega0 * B + j)) =
      min (p d) (ofOrd (Ordinal.omega0 * B + j))) (d : X) :
    min (PairedSlotEncoding.normalize j p d) (ofOrd (Ordinal.omega0 * B + j)) =
      min (a d) (ofOrd (Ordinal.omega0 * B + j)) :=
  CanonicalPairedPrefix.normalize_cap ha.1 ha.2 hag d

end Inventory

section Scheme
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (BJ : Finset ι × ℕ) [Fintype (D.below BJ)] (j : ℕ)

end Scheme
end
end VaughtConjecture.Knight.CanonicalPairedProfiles
