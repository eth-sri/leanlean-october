
import VaughtConjecture.Knight.PointwiseLabels
import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.PairedSlotEncoding
import VaughtConjecture.Knight.FiniteOrbitEmbedding
import VaughtConjecture.Knight.RightFilledGap

/-! # Constructed right-filled decoder for the paired slots

One affine ray serves each hosted orbit and one constant step serves each point.
Their finite maximum reads the occupied slots literally. Before each next group,
a step beginning just past every preceding occupied block raises unused strips
to the greatest grid value below the next group's floor. A final step supplies
the chosen ceiling after the last group. These are genuine faithful witnesses:
clause 5 holds at every threshold, including the bottom-suppressor tail.

The resulting decoder is exact, bounded by any visible ceiling of the inventory,
and orbit-supported over the original boundary when that ceiling belongs to the
grid. It constructs the outgoing transformation of a normalized finite profile.
Bottom reflection is neither needed nor claimed. The initial-gap control shows
where right-filling improves on the occupied rays alone.

Still open: a bottom-reflecting incoming normalization witness, the decoder
comparison at the largest common source-grid cut, normalization idempotence,
and the coupled lawful-section producer. Thus this is not source-prefix
extension, semantic amalgamation, or a bountifulness theorem.
-/

namespace VaughtConjecture.Knight.PairedSlotDecoder
open Transform Value ExtOrd PairedSlotEncoding
noncomputable section

def piece j S a := by
  classical
  exact if Orbit j S a then
    FiniteOrbitEmbedding.ray j (Ordinal.omega0 * block j S a) (limitPart a)
  else stepShifter (block j S a) ⊥ (ofOrd a)

theorem piece_witness {j} {S} {a}
    (ha : a ∈ S) : Witness (gTop j) (piece j S a) := by
  unfold piece
  split_ifs with ho
  · exact (FiniteOrbitEmbedding.ray_step j (limitPart_idem a)).normalizedWitness
  · exact Witness.stepLimit j _ bot_le (selfVis_bot)
      (selfVis_ofOrd_iff.mpr (by
        grind [VaughtConjecture.Knight.PairedSlotEncoding.Orbit]))

theorem piece_le {j : ℕ} {S : Finset Ordinal₀} {a : Ordinal₀} {x : ExtOrd} :
    piece j S a x ≤ ofOrd (ceiling j S a) := by
  unfold piece ceiling
  split_ifs with ho
  · exact?
  · simp_all [VaughtConjecture.Knight.stepShifter] <;> aesop

theorem piece_at {j} {S} {a b}
    (ha : a ∈ S) (hb : b ∈ S) (hk : key j S a = key j S b) :
    piece j S a (encode j S b) = ofOrd b := by
  have hblock := block_eq_of_key_eq ha hb hk
  have ho := orbit_iff_of_key_eq ha hb hk
  by_cases hoa : Orbit j S a
  · have hob := ho.mp hoa
    have hl : limitPart a = limitPart b := by
      simp_all [VaughtConjecture.Knight.PairedSlotEncoding.key]
    simp  [piece, ite_eq_left hoa, encode, offset, ite_eq_left hob, hblock]
    rw [FiniteOrbitEmbedding.ray_at j (limitPart_mul_nat _) hob.1, hl,
      limitPart_add_finitePart]
  · 
    have hab : a = b := by
      grind [VaughtConjecture.Knight.PairedSlotEncoding.key]
    simp  [piece, ite_eq_right hoa, hab]
    apply stepShifter_of_ge
    exact ofOrd_le_ofOrd.mpr le_self_add

theorem piece_before {j} {S} {a b}
    (ha : a ∈ S) (hk : key j S a < key j S b) :
    piece j S b (encode j S a) = ⊥ := by
  have hb := block_lt_of_key_lt ha hk
  have hbo : (block j S a : Ordinal₀) < block j S b := Nat.cast_lt.mpr hb
  unfold piece
  split_ifs
  · rw [encode, FiniteOrbitEmbedding.ray_ofOrd, limitPart_mul_add,
      ite_eq_left (by simp_all)]
  · exact stepShifter_of_lt (ofOrd_ne_bot _)
      (ofOrd_lt_ofOrd.mpr (code_add_lt_mul hbo _))

def occupied j (S : Finset Ordinal₀) x :=
  S.sup (fun a => piece j S a x)

theorem occupied_witness j S :
    Witness (gTop j) (occupied j S) :=
  Witness.finset_sup (MixedGradeInterpolation.zero_witness j) S (fun _ ha => piece_witness ha)

theorem occupied_encode {j} {S} {a}
    (ha : a ∈ S) : occupied j S (encode j S a) = ofOrd a := by
  apply le_antisymm
  · apply Finset.sup_le
    intro b hb
    rcases lt_trichotomy (key j S b) (key j S a) with hk | hk | hk
    · exact (piece_le).trans (ofOrd_le_ofOrd.mpr (ceiling_le_of_key_lt hk))
    · exact (piece_at hb ha hk).le
    · simp_all [piece_before]
  · rw [← piece_at ha ha rfl]
    exact Finset.le_sup (f := fun b => piece j S b (encode j S a)) ha
/-- The first source block not occupied by an earlier group. -/
def gapStart j (S : Finset Ordinal₀) a :=
  S.sup (fun b => if key j S b < key j S a then block j S b + 1 else 0)

theorem gapStart_le j S a :
    gapStart j S a ≤ block j S a := by
  apply Finset.sup_le
  intro b hb
  split_ifs with hk
  · exact block_lt_of_key_lt hb hk
  · exact Nat.zero_le _

theorem block_lt_gapStart {j} {S} {a b}
    (ha : a ∈ S) (hk : key j S a < key j S b) :
    block j S a < gapStart j S b := by
  change block j S a + 1 ≤ gapStart j S b
  
  apply Finset.le_sup_of_le ha
  simp  [ite_eq_left hk, ]

def gap j S G
    a :=
  stepShifter (gapStart j S a) ⊥ (RightFilledGap.floor G (ofOrd (key j S a)))

theorem step_zero_le {n : ℕ} {c x : ExtOrd} : stepShifter n ⊥ c x ≤ c := by simp_all [VaughtConjecture.Knight.stepShifter] <;> aesop

theorem gap_witness {j} {S} {G}
    (hG : VisibleOn j G) a :
    Witness (gTop j) (gap j S G a) := by
  apply Witness.stepLimit j _ bot_le (selfVis_bot)
  rcases RightFilledGap.floor_eq_bot_or_mem G (ofOrd (key j S a)) with hb | hm
  · rw [hb]; exact selfVis_bot
  · exact hG _ hm

theorem gap_encode_le {j} {S} {G}
    {a b} (ha : a ∈ S) :
    gap j S G b (encode j S a) ≤ ofOrd a := by
  by_cases hk : key j S b ≤ key j S a
  · exact (step_zero_le).trans ((RightFilledGap.floor_le _ _).trans
      (ofOrd_le_ofOrd.mpr (hk.trans (key_le))))
  · have hblock := block_lt_gapStart ha (not_le.mp hk)
    have he : gap j S G b (encode j S a) = ⊥ :=
      stepShifter_of_lt (ofOrd_ne_bot _)
        (ofOrd_lt_ofOrd.mpr (code_add_lt_mul (Nat.cast_lt.mpr hblock) _))
    rw [he]
    exact bot_le

def tailStart j (S : Finset Ordinal₀) := S.sup (block j S) + 1

/-- Occupied pieces, right-filled gaps, and the terminal ceiling. -/
def decode j S G
    C x :=
  max (occupied j S x)
    (max (S.sup (fun a => gap j S G a x)) (stepShifter (tailStart j S) ⊥ C x))

theorem decode_witness {j} {S} {G} {C}
    (hG : VisibleOn j G) (hC : SelfVis j C) :
    Witness (gTop j) (decode j S G C) :=
  (occupied_witness j S).max
    ((Witness.finset_sup (MixedGradeInterpolation.zero_witness j) S
      (fun a _ => gap_witness hG a)).max
      (Witness.stepLimit j _ bot_le (selfVis_bot) hC))

theorem decode_encode {j} {S} {G} {C}
    {a} (ha : a ∈ S) : decode j S G C (encode j S a) = ofOrd a := by
  have htail : stepShifter (tailStart j S) ⊥ C (encode j S a) = ⊥ := by
    apply stepShifter_of_lt (ofOrd_ne_bot _)
    apply ofOrd_lt_ofOrd.mpr
    apply code_add_lt_mul
    exact Nat.cast_lt.mpr (Nat.lt_succ_of_le (Finset.le_sup  ha))
  rw [decode, occupied_encode ha, htail, max_eq_left bot_le]
  apply max_eq_left
  apply Finset.sup_le
  intro b _
  exact gap_encode_le ha

theorem decode_gap_reaches {j} {S} {G}
    {C x h} {a}
    (ha : a ∈ S) (hh : h ∈ G) (hfloor : h ≤ ofOrd (key j S a))
    (hx : ofOrd (Ordinal.omega0 * gapStart j S a) ≤ x) :
    h ≤ decode j S G C x := by
  have hg : gap j S G a x = RightFilledGap.floor G (ofOrd (key j S a)) :=
    stepShifter_of_ge hx
  calc h ≤ gap j S G a x := hg ▸ RightFilledGap.le_floor hh hfloor
    _ ≤ S.sup (fun b => gap j S G b x) := Finset.le_sup (f := fun b => gap j S G b x) ha
    _ ≤ decode j S G C x := (le_max_left _ _).trans (le_max_right _ _)

theorem decode_tail {j} {S} {G}
    {C x} (hx : ofOrd (Ordinal.omega0 * tailStart j S) ≤ x) :
    C ≤ decode j S G C x := by
  have he := stepShifter_of_ge (c₀ := (⊥)) (c₁ := C) hx
  rw [decode, he]
  exact (le_max_right _ _).trans (le_max_right _ _)

theorem ceiling_eq_replace {j} {S} {a}
    (ha : a ∈ S) : ofOrd (ceiling j S a) = extVisibilityReplace (ofOrd a) j j := by
  by_cases hf : finitePart a < j
  · simp  [ceiling, ite_eq_left (orbit_of_invisible ha hf),
      extVisibilityReplace_of_finitePart_lt hf]
  · rw [extVisibilityReplace_of_le_finitePart (not_lt.mp hf)]
    unfold ceiling
    split_ifs with ho
    · have he : finitePart a = j := le_antisymm ho.1 (not_lt.mp hf)
      rw [← he, limitPart_add_finitePart]
    · rfl

theorem decode_le {j} {S} {G} {C}
    (hC : SelfVis j C) (hS : ∀ a ∈ S, ofOrd a ≤ C) x :
    decode j S G C x ≤ C := by
  apply max_le
  · apply Finset.sup_le
    intro a ha
    apply (piece_le).trans
    rw [ceiling_eq_replace ha]
    exact extVisibilityReplace_le_of_le_selfVis le_rfl hC (hS a ha)
  · apply max_le
    · apply Finset.sup_le
      intro a ha
      exact (step_zero_le).trans ((RightFilledGap.floor_le _ _).trans
        ((ofOrd_le_ofOrd.mpr (key_le)).trans (hS a ha)))
    · exact step_zero_le

section
variable {X : Type*} [Fintype X]

theorem decode_normalize {j : ℕ} {p : X → ExtOrd} {G : Finset ExtOrd} {C : ExtOrd}
    (hG : VisibleOn j G) (hC : SelfVis j C)
    (hp : AvoidsValue p ⊤) {d : X} :
    decode j (values p) G C (PairedSlotEncoding.normalize j p d) = p d := by
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · simp  [PairedSlotEncoding.normalize, hb]
    exact (decode_witness hG hC).bot
  · exact (hp d ht).elim
  · rw [normalize_ofOrd ha, ha]
    exact decode_encode (mem_values.mpr ⟨d, ha⟩)

omit [Fintype X] in
private theorem supported_max {K} {G} {p : X → ExtOrd} {a b}
    (ha : OrbitPrefixSupport.Supported K G p a)
    (hb : OrbitPrefixSupport.Supported K G p b) :
    OrbitPrefixSupport.Supported K G p (max a b) := by grind

omit [Fintype X] in
private def supported_sup {I : Type*} (s : Finset I) {K : ℕ} {G : Set ExtOrd}
    {p : X → ExtOrd} {f : I → ExtOrd}
    (hf : ∀ a ∈ s, OrbitPrefixSupport.Supported K G p (f a)) := by
  classical
  apply Finset.sup_induction (p := OrbitPrefixSupport.Supported K G p)
  · exact Or.inl rfl
  · grind
  · exact hf

omit [Fintype X] in
private theorem supported_boundary {K} {G} {p : X → ExtOrd} d :
    OrbitPrefixSupport.Supported K G p (p d) := by
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · exact Or.inl hb
  · exact Or.inr (Or.inr ⟨d, K, le_rfl, by rw [ht, extVisibilityReplace_top]⟩)
  · by_cases hk : finitePart a < K
    · exact Or.inr (Or.inr ⟨d, finitePart a, hk.le, by
        rw [ha, extVisibilityReplace_of_finitePart_lt hk, limitPart_add_finitePart]⟩)
    · exact Or.inr (Or.inr ⟨d, K, le_rfl, by
        grind [extVisibilityReplace_of_le_finitePart]⟩)

theorem piece_supported {j K : ℕ} {p : X → ExtOrd} {G : Set ExtOrd}
    (hj : j ≤ K) {a : Ordinal₀} (ha : a ∈ values p) (x : ExtOrd) :
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
  let core1 := OrbitPrefixSupport.Supported K (G) p
  apply supported_max
  · exact supported_sup _ (fun a ha => piece_supported hj ha x)
  · apply supported_max
    · apply supported_sup
      intro a _
      have hs : core1
          (RightFilledGap.floor G (ofOrd (key j (values p) a))) := by
        rcases RightFilledGap.floor_eq_bot_or_mem G _ with hb | hm
        · exact Or.inl hb
        · exact Or.inr (Or.inl hm)
      rcases ExtOrd.cases x with rfl | rfl | ⟨b, rfl⟩
      · exact Or.inl rfl
      · exact hs
      · change core1 (if _ then _ else _)
        split_ifs <;> first | exact Or.inl rfl | exact hs
    · rcases ExtOrd.cases x with rfl | rfl | ⟨b, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl hC)
      · change core1 (if _ then _ else _)
        split_ifs <;> first | exact Or.inl rfl | exact Or.inr (Or.inl hC)


