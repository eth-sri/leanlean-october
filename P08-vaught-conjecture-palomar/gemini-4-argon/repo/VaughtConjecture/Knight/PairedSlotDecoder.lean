/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PairedSlotEncoding
public import VaughtConjecture.Knight.FiniteOrbitEmbedding
public import VaughtConjecture.Knight.RightFilledGap

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

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.PairedSlotDecoder
open Transform Value ExtOrd PairedSlotEncoding

def piece (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) : ExtOrd → ExtOrd := by
  classical
  exact if Orbit j S a then
    FiniteOrbitEmbedding.ray j (Ordinal.omega0 * block j S a) (limitPart a)
  else stepShifter (block j S a) ⊥ (ofOrd a)

theorem step_zero_le (n : ℕ) (c x : ExtOrd) : stepShifter n ⊥ c x ≤ c := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨b, rfl⟩
  · exact bot_le
  · exact le_rfl
  · change (if _ then _ else _) ≤ _; split_ifs <;> simp

theorem piece_le (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) (x : ExtOrd) :
    piece j S a x ≤ ofOrd (ceiling j S a) := by
  unfold piece ceiling
  split_ifs
  · exact FiniteOrbitEmbedding.ray_le _ _ _ _
  · exact step_zero_le _ _ _

def occupied (j : ℕ) (S : Finset Ordinal.{0}) (x : ExtOrd) : ExtOrd :=
  S.sup fun a => piece j S a x

theorem occupied_witness (j : ℕ) (S : Finset Ordinal.{0}) : Witness (gTop j) (occupied j S) :=
  Witness.finset_sup (MixedGradeInterpolation.zero_witness j) S fun a ha => by
    unfold piece
    split_ifs with ho
    · exact (FiniteOrbitEmbedding.ray_step j (limitPart_idem a)).normalizedWitness
    · exact Witness.stepLimit j _ bot_le (selfVis_bot j)
        (selfVis_ofOrd_iff.mpr (not_lt.mp fun hn => ho (orbit_of_invisible ha hn)))

theorem occupied_encode {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}}
    (ha : a ∈ S) : occupied j S (encode j S a) = ofOrd a := by
  have hat {b c : Ordinal.{0}} (hb : b ∈ S) (hc : c ∈ S) (hk : key j S b = key j S c) :
      piece j S b (encode j S c) = ofOrd c := by
    have hblock := block_eq_of_key_eq hb hc hk
    have ho := orbit_iff_of_key_eq hb hc hk
    by_cases hob : Orbit j S b
    · have hoc := ho.mp hob
      have hl : limitPart b = limitPart c := by
        simpa only [key, ite_eq_left hob, ite_eq_left hoc] using hk
      simp only [piece, ite_eq_left hob, encode, offset, ite_eq_left hoc, hblock]
      rw [FiniteOrbitEmbedding.ray_at j (limitPart_mul_nat _) hoc.1, hl, limitPart_add_finitePart]
    · have hoc : ¬ Orbit j S c := fun h => hob (ho.mpr h)
      have hbc : b = c := by simpa only [key, ite_eq_right hob, ite_eq_right hoc] using hk
      simp only [piece, ite_eq_right hob, hbc]
      exact stepShifter_of_ge (ofOrd_le_ofOrd.mpr le_self_add)
  refine le_antisymm (Finset.sup_le fun b hb => ?_)
    ((hat ha ha rfl).symm ▸ Finset.le_sup (f := fun b => piece j S b (encode j S a)) ha)
  rcases lt_trichotomy (key j S b) (key j S a) with hk | hk | hk
  · exact (piece_le j S b _).trans (ofOrd_le_ofOrd.mpr (ceiling_le_of_key_lt hk))
  · exact (hat hb ha hk).le
  · have hbo : (block j S a : Ordinal.{0}) < block j S b :=
      Nat.cast_lt.mpr (block_lt_of_key_lt ha hk)
    unfold piece
    split_ifs
    · rw [encode, FiniteOrbitEmbedding.ray_ofOrd, limitPart_mul_add,
        ite_eq_left (by simpa only [Nat.cast_zero, add_zero] using code_add_lt_mul hbo 0)]
      exact bot_le
    · exact (stepShifter_of_lt (ofOrd_ne_bot _)
        (ofOrd_lt_ofOrd.mpr (code_add_lt_mul hbo _))).le.trans bot_le

/-- The first source block not occupied by an earlier group. -/
def gapStart (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) : ℕ :=
  S.sup fun b => if key j S b < key j S a then block j S b + 1 else 0

theorem gapStart_le (j : ℕ) (S : Finset Ordinal.{0}) (a : Ordinal.{0}) :
    gapStart j S a ≤ block j S a :=
  Finset.sup_le fun _ hb => by
    split_ifs with hk <;> [exact block_lt_of_key_lt hb hk; exact Nat.zero_le _]

theorem block_lt_gapStart {j : ℕ} {S : Finset Ordinal.{0}} {a b : Ordinal.{0}}
    (ha : a ∈ S) (hk : key j S a < key j S b) : block j S a < gapStart j S b := by
  change block j S a + 1 ≤ gapStart j S b
  exact Finset.le_sup_of_le ha (by simp only [ite_eq_left hk, le_refl])

def gap (j : ℕ) (S : Finset Ordinal.{0}) (G : Finset ExtOrd)
    (a : Ordinal.{0}) : ExtOrd → ExtOrd :=
  stepShifter (gapStart j S a) ⊥ (RightFilledGap.floor G (ofOrd (key j S a)))

def tailStart (j : ℕ) (S : Finset Ordinal.{0}) : ℕ := S.sup (block j S) + 1

/-- Occupied pieces, right-filled gaps, and the terminal ceiling. -/
def decode (j : ℕ) (S : Finset Ordinal.{0}) (G : Finset ExtOrd) (C x : ExtOrd) : ExtOrd :=
  max (occupied j S x)
    (max (S.sup fun a => gap j S G a x) (stepShifter (tailStart j S) ⊥ C x))

theorem decode_witness {j : ℕ} {S : Finset Ordinal.{0}} {G : Finset ExtOrd} {C : ExtOrd}
    (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C) :
    Witness (gTop j) (decode j S G C) :=
  (occupied_witness j S).max
    ((Witness.finset_sup (MixedGradeInterpolation.zero_witness j) S fun a _ =>
      Witness.stepLimit j _ bot_le (selfVis_bot j)
        ((RightFilledGap.floor_eq_bot_or_mem G (ofOrd (key j S a))).elim
          (fun hb => hb ▸ selfVis_bot j) (hG _))).max
      (Witness.stepLimit j _ bot_le (selfVis_bot j) hC))

theorem decode_encode {j : ℕ} {S : Finset Ordinal.{0}} {G : Finset ExtOrd} {C : ExtOrd}
    {a : Ordinal.{0}} (ha : a ∈ S) : decode j S G C (encode j S a) = ofOrd a := by
  have htail : stepShifter (tailStart j S) ⊥ C (encode j S a) = ⊥ :=
    stepShifter_of_lt (ofOrd_ne_bot _) (ofOrd_lt_ofOrd.mpr (code_add_lt_mul
      (Nat.cast_lt.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := block j S) ha))) _))
  rw [decode, occupied_encode ha, htail, max_eq_left bot_le]
  refine max_eq_left (Finset.sup_le fun b _ => ?_)
  by_cases hk : key j S b ≤ key j S a
  · exact (step_zero_le _ _ _).trans ((RightFilledGap.floor_le _ _).trans
      (ofOrd_le_ofOrd.mpr (hk.trans (key_le j S a))))
  · exact (stepShifter_of_lt (ofOrd_ne_bot _)
      (ofOrd_lt_ofOrd.mpr (code_add_lt_mul (Nat.cast_lt.mpr
        (block_lt_gapStart ha (not_le.mp hk))) _))).le.trans bot_le

theorem decode_gap_reaches {j : ℕ} {S : Finset Ordinal.{0}} {G : Finset ExtOrd}
    {C x h : ExtOrd} {a : Ordinal.{0}}
    (ha : a ∈ S) (hh : h ∈ G) (hfloor : h ≤ ofOrd (key j S a))
    (hx : ofOrd (Ordinal.omega0 * gapStart j S a) ≤ x) : h ≤ decode j S G C x := by
  have hg : gap j S G a x = RightFilledGap.floor G (ofOrd (key j S a)) := stepShifter_of_ge hx
  exact (hg ▸ RightFilledGap.le_floor hh hfloor).trans
    ((Finset.le_sup (f := fun b => gap j S G b x) ha).trans
      ((le_max_left _ _).trans (le_max_right _ _)))

theorem decode_tail {j : ℕ} {S : Finset Ordinal.{0}} {G : Finset ExtOrd}
    {C x : ExtOrd} (hx : ofOrd (Ordinal.omega0 * tailStart j S) ≤ x) :
    C ≤ decode j S G C x := by
  rw [decode, stepShifter_of_ge (c₀ := (⊥ : ExtOrd)) (c₁ := C) hx]
  exact (le_max_right _ _).trans (le_max_right _ _)

theorem ceiling_eq_replace {j : ℕ} {S : Finset Ordinal.{0}} {a : Ordinal.{0}}
    (ha : a ∈ S) : ofOrd (ceiling j S a) = extVisibilityReplace (ofOrd a) j j := by
  by_cases hf : finitePart a < j
  · simp only [ceiling, ite_eq_left (orbit_of_invisible ha hf),
      extVisibilityReplace_of_finitePart_lt hf]
  · rw [extVisibilityReplace_of_le_finitePart (not_lt.mp hf)]
    unfold ceiling
    split_ifs with ho
    · rw [← le_antisymm ho.1 (not_lt.mp hf), limitPart_add_finitePart]
    · rfl

theorem decode_le {j : ℕ} {S : Finset Ordinal.{0}} {G : Finset ExtOrd} {C : ExtOrd}
    (hC : SelfVis j C) (hS : ∀ a ∈ S, ofOrd a ≤ C) (x : ExtOrd) :
    decode j S G C x ≤ C :=
  max_le (Finset.sup_le fun a ha => (piece_le j S a x).trans
    ((ceiling_eq_replace ha).le.trans (extVisibilityReplace_le_of_le_selfVis le_rfl hC (hS a ha))))
    (max_le (Finset.sup_le fun a ha => (step_zero_le _ _ _).trans
      ((RightFilledGap.floor_le _ _).trans ((ofOrd_le_ofOrd.mpr (key_le j S a)).trans (hS a ha))))
      (step_zero_le _ _ _))

section Profile
variable {X : Type*} [Fintype X]

theorem decode_normalize {j : ℕ} {p : X → ExtOrd} {G : Finset ExtOrd} {C : ExtOrd}
    (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C) (hp : ∀ d, p d ≠ ⊤) (d : X) :
    decode j (values p) G C (PairedSlotEncoding.normalize j p d) = p d := by
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · simp only [PairedSlotEncoding.normalize, hb]; exact (decode_witness hG hC).bot
  · exact (hp d ht).elim
  · rw [normalize_ofOrd ha, ha]; exact decode_encode (mem_values.mpr ⟨d, ha⟩)

/-- Every output, not only the represented boundary values, has orbit support. -/
theorem decode_supported {j K : ℕ} {p : X → ExtOrd} {G : Finset ExtOrd} {C : ExtOrd}
    (hj : j ≤ K) (hC : C ∈ G) (x : ExtOrd) :
    OrbitPrefixSupport.Supported K (G : Set ExtOrd) p (decode j (values p) G C x) := by
  classical
  have hmax {a b : ExtOrd} (ha : OrbitPrefixSupport.Supported K (G : Set ExtOrd) p a)
      (hb : OrbitPrefixSupport.Supported K (G : Set ExtOrd) p b) :
      OrbitPrefixSupport.Supported K (G : Set ExtOrd) p (max a b) := by
    rcases le_total a b with h | h <;> [rwa [max_eq_right h]; rwa [max_eq_left h]]
  have hsup (s : Finset Ordinal.{0}) {f : Ordinal.{0} → ExtOrd}
      (hf : ∀ a ∈ s, OrbitPrefixSupport.Supported K (G : Set ExtOrd) p (f a)) :
      OrbitPrefixSupport.Supported K (G : Set ExtOrd) p (s.sup f) :=
    Finset.sup_induction (p := OrbitPrefixSupport.Supported K (G : Set ExtOrd) p)
      (Or.inl rfl) (fun _ ha _ hb => hmax ha hb) hf
  have hstep (n : ℕ) {c : ExtOrd} (hc : OrbitPrefixSupport.Supported K (G : Set ExtOrd) p c) :
      OrbitPrefixSupport.Supported K (G : Set ExtOrd) p (stepShifter n ⊥ c x) := by
    rcases ExtOrd.cases x with rfl | rfl | ⟨b, rfl⟩
    · exact Or.inl rfl
    · exact hc
    · change OrbitPrefixSupport.Supported K (G : Set ExtOrd) p (if _ then _ else _)
      split_ifs <;> first | exact Or.inl rfl | exact hc
  unfold decode occupied gap
  refine hmax (hsup _ fun a ha => ?_) (hmax (hsup _ fun a _ => hstep _ ?_) (hstep _ (Or.inr (Or.inl hC))))
  · unfold piece
    split_ifs with ho
    · obtain ⟨b, hb, hbj, hba⟩ := ho.2
      obtain ⟨d, hd⟩ := mem_values.mp hb
      have hs (i : ℕ) (hi : i ≤ j) :
          OrbitPrefixSupport.Supported K (G : Set ExtOrd) p (ofOrd (limitPart a + i)) :=
        Or.inr (Or.inr ⟨d, i, hi.trans hj, by
          rw [hd, extVisibilityReplace_of_finitePart_lt (hbj.trans_le hj), hba]⟩)
      rcases ExtOrd.cases x with rfl | rfl | ⟨b, rfl⟩
      · exact Or.inl rfl
      · exact hs j le_rfl
      · rw [FiniteOrbitEmbedding.ray_ofOrd]
        split_ifs <;> [exact Or.inl rfl; exact hs _ (min_le_right _ _); exact hs j le_rfl]
    · obtain ⟨d, hd⟩ := mem_values.mp ha
      refine hstep _ (Or.inr (Or.inr ⟨d, min (finitePart a) K, min_le_right _ _, ?_⟩))
      rw [hd]
      by_cases hk : finitePart a < K
      · rw [min_eq_left hk.le, extVisibilityReplace_of_finitePart_lt hk, limitPart_add_finitePart]
      · rw [extVisibilityReplace_of_le_finitePart (not_lt.mp hk)]
  · rcases RightFilledGap.floor_eq_bot_or_mem G _ with hb | hm
    · exact Or.inl hb
    · exact Or.inr (Or.inl hm)

