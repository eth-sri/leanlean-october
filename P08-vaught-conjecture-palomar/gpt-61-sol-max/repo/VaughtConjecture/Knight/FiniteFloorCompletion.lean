import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CountedEncoding

/-! # Finite floor completion for the block-bridge kernel

Port of the sibling's finite floor-completion lemmas (its `PaperFiniteBlockFloorDomain`,
`PaperFiniteBlockFloorCompletion`, `PaperFiniteFullStripBridge`,
`PaperFiniteBottomAwareFloorBridge`)
to V-C's kernel `Knight/FiniteBlockBridge.lean` — the lemmas only, not the sibling's stack
architecture.

* `blockFloor` — the limit part of an ordinal label (`⊥`, `⊤` fixed); `stripDomain K s` — a
  finite inventory completed by the full strips `⌊x⌋ + i`, `i ≤ K`, of its blocks: closed under
  every replacement at thresholds `≤ K` (`stripDomain_closed`), containing every floor.
* `roundUp s` — raise an unrepresented initial part of a block to the block's least represented
  input: monotone, identity on `s`, block-preserving, commuting with bounded replacements when `s`
  is closed (`roundUp_commutes`), and landing in `s` on the strip domain (`roundUp_mem`).
* `exists_source_below_replace` — on a full-strip domain, every domain point visible below a
  replaced input is dominated by the replacement of a domain point below the original input; hence
  the bounded bridge (`fullStrip_bridge`) from monotonicity and bounded commutation.
* `FloorSupport` / `bridge_tail_of_floorSupport` — above the suppressor cutoff only nonbottom
  floor support is needed; a shifter whose `⊥`-fibre is a union of blocks (`bot_of_same_block`, from
  clause 5 at `⊥`) supplies it.
* `floorCompletion` — the assembled table `τ ∘ roundUp s` on `stripDomain K s` has bottom,
  monotonicity, the weak orbit law and the unrestricted bridge, from a bounded, monotone,
  bottom-preserving shifter commuting with all bounded replacements.

Construction-private (not root-exported). -/

namespace VaughtConjecture.Knight

open  Value ExtOrd

/-! ## Block floors -/

/-- The block floor of a label. -/
noncomputable def blockFloor : LabelMap
  | ⊥ => ⊥
  | some ⊤ => ⊤
  | some (some a) => ofOrd (limitPart a)



@[simp] theorem blockFloor_bot : blockFloor ⊥ = ⊥ := rfl
@[simp] theorem blockFloor_top : blockFloor ⊤ = ⊤ := rfl

@[simp] theorem blockFloor_ofOrd a :
    blockFloor (ofOrd a) = ofOrd (limitPart a) := rfl

theorem blockFloor_le x : blockFloor x ≤ x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · exact le_rfl
  · exact le_rfl
  · simp_all [limitPart_le]

theorem blockFloor_idem x : blockFloor (blockFloor x) = blockFloor x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · rfl
  · rfl
  · simp_all [limitPart_idem]

theorem blockFloor_mono {x y} (h : x ≤ y) : blockFloor x ≤ blockFloor y := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · exact bot_le
  · rw [top_le_iff.mp h]
  · rcases ExtOrd.cases y with rfl | rfl | ⟨b, rfl⟩
    · simp_all
    · exact le_top
    · simp_all [limitPart_mono]

theorem blockFloor_evr x k i :
    blockFloor (extVisibilityReplace x k i) = blockFloor x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · rfl
  · rfl
  · rw [extVisibilityReplace_ofOrd, blockFloor_ofOrd, blockFloor_ofOrd, ofOrd_inj]
    unfold visibilityReplace
    split_ifs
    · exact limitPart_limitPart_add_nat a i
    · rfl

theorem blockFloor_eq_of_between {x y z} (hxy : x ≤ y) (hyz : y ≤ z)
    (hxz : blockFloor x = blockFloor z) : blockFloor y = blockFloor x :=
  le_antisymm (hxz ▸ blockFloor_mono hyz) (blockFloor_mono hxy)

/-- A moving replacement at offset `0` is the block floor. -/
theorem evr_zero_eq_blockFloor {a} {k} (h : finitePart a < k) :
    extVisibilityReplace (ofOrd a) k 0 = blockFloor (ofOrd a) := by
  rw [extVisibilityReplace_of_finitePart_lt h, blockFloor_ofOrd, Nat.cast_zero, add_zero]

/-! ## The strip domain -/

/-- The full strips of the blocks of a finite inventory, through offset `K`. -/
noncomputable def stripDomain (K : ℕ) (s : Finset ExtOrd) :=
  s ∪ s.biUnion fun x =>
    match x with
    | some (some a) => (Finset.range (K + 1)).image fun i : ℕ => ofOrd (limitPart a + i)
    | _ => ∅

theorem subset_stripDomain K s : s ⊆ stripDomain K s :=
  Finset.subset_union_left

theorem mem_stripDomain_of_lp {K} {s} {a} (ha : ofOrd a ∈ s)
    {i} (hi : i ≤ K) : ofOrd (limitPart a + i) ∈ stripDomain K s := by
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨ofOrd a, ha,
    Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩⟩

theorem stripDomain_exists_sameBlock {K} {s} {z}
    (hz : z ∈ stripDomain K s) : ∃ x ∈ s, blockFloor z = blockFloor x := by
  rcases Finset.mem_union.mp hz with h | h
  · exact ⟨z, h, rfl⟩
  · obtain ⟨x, hx, hm⟩ := Finset.mem_biUnion.mp h
    rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
    · simp at hm
    · simp at hm
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hm
      exact ⟨ofOrd a, hx, by simp_all [limitPart_limitPart_add_nat]⟩

theorem stripDomain_fullStrips {K} {s} {a}
    (ha : ofOrd a ∈ stripDomain K s) {i} (hi : i ≤ K) :
    ofOrd (limitPart a + i) ∈ stripDomain K s := by
  obtain ⟨x, hx, hb⟩ := stripDomain_exists_sameBlock ha
  rcases ExtOrd.cases x with rfl | rfl | ⟨b, rfl⟩
  · simp_all
  · simp_all
  · simp_all [mem_stripDomain_of_lp]

theorem stripDomain_floor_mem {K} {s} {z} (hz : z ∈ stripDomain K s) :
    blockFloor z ∈ stripDomain K s := by
  rcases ExtOrd.cases z with rfl | rfl | ⟨a, rfl⟩
  · exact hz
  · exact hz
  · 
    have := stripDomain_fullStrips hz (Nat.zero_le K)
    rwa [Nat.cast_zero, add_zero] at this

/-- **The strip domain is closed under every replacement at thresholds `≤ K`.** -/
theorem stripDomain_closed {K} {s} {z} (hz : z ∈ stripDomain K s)
    {k i} (hk : k ≤ K) (hi : i ≤ k) : extVisibilityReplace z k i ∈ stripDomain K s := by
  rcases ExtOrd.cases z with rfl | rfl | ⟨a, rfl⟩
  · simpa using hz
  · simpa using hz
  · by_cases hfp : finitePart a < k
    · rw [extVisibilityReplace_of_finitePart_lt hfp]; exact stripDomain_fullStrips hz (hi.trans hk)
    · grind [extVisibilityReplace_of_le_finitePart]

/-! ## Rounding up to the least represented input of a block -/

open Classical in
/-- The represented inputs of the block of `x`. -/
noncomputable def sourceBlock (s : Finset ExtOrd) x :=
  s.filter fun y => blockFloor y = blockFloor x

open Classical in
/-- Raise `x` to at least the least represented input of its block. -/
noncomputable def roundUp s x :=
  if h : (sourceBlock s x).Nonempty then max x ((sourceBlock s x).min' h) else x

theorem sourceBlock_eq {s} {x y} (h : blockFloor x = blockFloor y) :
    sourceBlock s x = sourceBlock s y := by
  classical
  unfold sourceBlock; simp  [h]

theorem roundUp_of_mem {s} {x} (hx : x ∈ s) : roundUp s x = x := by
  classical
  have hm : x ∈ sourceBlock s x := Finset.mem_filter.mpr ⟨hx, rfl⟩
  unfold roundUp
  rw [dite_eq_left ⟨x, hm⟩, max_eq_left (Finset.min'_le _ _ hm)]

theorem blockFloor_roundUp s x :
    blockFloor (roundUp s x) = blockFloor x := by
  classical
  unfold roundUp
  split_ifs with h
  · have hm := (Finset.mem_filter.mp (Finset.min'_mem (sourceBlock s x) h)).2
    rcases le_total x ((sourceBlock s x).min' h) with hx | hx
    · rw [max_eq_right hx]; exact hm
    · rw [max_eq_left hx]
  · rfl

theorem roundUp_mono s : Monotone (roundUp s) := by
  classical
  intro x y hxy
  by_cases hb : blockFloor x = blockFloor y
  · grind [sourceBlock_eq, roundUp]
  · grind [blockFloor_eq_of_between, blockFloor_roundUp]

theorem roundUp_bot s : roundUp s ⊥ = ⊥ := by
  have h := blockFloor_roundUp s ⊥
  
  rcases ExtOrd.cases (roundUp s ⊥) with h0 | h0 | ⟨a, h0⟩
  · exact h0
  · simp_all
  · simp_all

theorem roundUp_mem_of_nonempty {s} {x} (h : (sourceBlock s x).Nonempty)
    (hle : x ≤ (sourceBlock s x).min' h) : roundUp s x ∈ s := by
  classical
  unfold roundUp
  rw [dite_eq_left h, max_eq_right hle]
  exact (Finset.mem_filter.mp (Finset.min'_mem _ h)).1

/-- **Rounding commutes with bounded replacements** when the inventory is closed under them: a
low minimum forces its own block floor to be represented; otherwise it is fixed by every bounded
replacement. -/
theorem roundUp_commutes s K
    (hClosed : ∀ x ∈ s, ∀ k i : ℕ, k ≤ K → i ≤ k → extVisibilityReplace x k i ∈ s)
    x k i (hk : k ≤ K) (hi : i ≤ k) :
    roundUp s (extVisibilityReplace x k i) = extVisibilityReplace (roundUp s x) k i := by
  classical
  have hs := sourceBlock_eq (s := s) (blockFloor_evr x k i)
  unfold roundUp
  rw [hs]
  split_ifs with h
  · set m := (sourceBlock s x).min' h with hm_def
    have hm : m ∈ sourceBlock s x := Finset.min'_mem _ _
    have hmS := (Finset.mem_filter.mp hm).1
    have hmB := (Finset.mem_filter.mp hm).2
    by_cases hv : SelfVis K m
    · have hvk : extVisibilityReplace m k i = m := evr_eq_self_of_selfVis (selfVis_mono hv hk)
      rw [(extVisibilityReplace_mono k i hi).map_max, hvk]
    · -- `m` is an ordinal moving at `K`; its floor is represented and below it
      rcases ExtOrd.cases m with hm0 | hm0 | ⟨a, hma⟩
      · aesop
      · aesop
      · have hfp : finitePart a < K := by
          by_contra hc
          exact hv (hma ▸ selfVis_ofOrd_iff.mpr (not_lt.mp hc))
        have hf  := by
          have := hClosed m hmS K 0 le_rfl (Nat.zero_le _)
          rwa [hma, evr_zero_eq_blockFloor hfp, ← hma] at this
        have hfB : blockFloor (blockFloor m) = blockFloor x := by
          rw [blockFloor_idem, hmB]
        have hmf : m ≤ blockFloor m :=
          Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hf, hfB⟩)
        have hmx : m ≤ x := hmf.trans (by rw [hmB]; exact blockFloor_le x)
        have hmr : m ≤ extVisibilityReplace x k i := hmf.trans (by
          grind [blockFloor_evr, blockFloor_le])
        rw [max_eq_left hmx, max_eq_left hmr]
  · rfl

/-- The rounded floor of a represented input is represented. -/
def roundUp_floor_mem {s : Finset ExtOrd} {x : ExtOrd} (hx : x ∈ s) := by
  classical
  have hxB : x ∈ sourceBlock s (blockFloor x) :=
    Finset.mem_filter.mpr ⟨hx, (blockFloor_idem x).symm⟩
  apply roundUp_mem_of_nonempty ⟨x, hxB⟩
  have hm := Finset.min'_mem (sourceBlock s (blockFloor x)) ⟨x, hxB⟩
  have hmB := (Finset.mem_filter.mp hm).2
  rw [blockFloor_idem] at hmB
  exact hmB.symm.le.trans (blockFloor_le _)

/-- **Every strip point rounds back into the inventory.** -/
theorem roundUp_mem K s
    (hClosed : ∀ x ∈ s, ∀ k i : ℕ, k ≤ K → i ≤ k → extVisibilityReplace x k i ∈ s)
    {z} (hz : z ∈ stripDomain K s) : roundUp s z ∈ s := by
  rcases Finset.mem_union.mp hz with hz | hz
  · rw [roundUp_of_mem hz]; exact hz
  · obtain ⟨x, hx, hm⟩ := Finset.mem_biUnion.mp hz
    rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
    · simp at hm
    · simp at hm
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
      have hi' : i ≤ K := by simp_all
      rcases Nat.eq_zero_or_pos K with hK | hK
      · subst hK
        have hi0 : i = 0 := by omega
        subst hi0
        rw [Nat.cast_zero, add_zero, ← blockFloor_ofOrd]
        exact roundUp_floor_mem hx
      · have hz' : ofOrd (limitPart a + i) = extVisibilityReplace (blockFloor (ofOrd a)) K i := by
          rw [blockFloor_ofOrd,
            extVisibilityReplace_of_finitePart_lt (by rw [finitePart_limitPart]; exact hK),
            limitPart_idem]
        rw [hz', roundUp_commutes s K hClosed _ K i le_rfl hi']
        exact hClosed _ (roundUp_floor_mem hx) K i le_rfl hi'

/-! ## The bottom fibre of a faithful shifter is a union of blocks -/

/-- A shifter whose `⊥`-points propagate to all their replacements is `⊥` on whole blocks. -/
theorem bot_of_same_block {f : LabelMap}
    (hbot : ∀ x, f x = ⊥ → ∀ k i, i ≤ k → f (extVisibilityReplace x k i) = ⊥)
    {x y : ExtOrd} (hb : blockFloor x = blockFloor y) (hx : f x = ⊥) : f y = ⊥ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · rcases ExtOrd.cases y with rfl | rfl | ⟨b, rfl⟩
    · exact hx
    · exact absurd hb (by simp)
    · rw [ ] at hb; exact absurd hb.symm (ofOrd_ne_bot _)
  · rcases ExtOrd.cases y with rfl | rfl | ⟨b, rfl⟩
    · exact absurd hb (by simp)
    · exact hx
    · rw [ ] at hb; exact absurd hb.symm (ofOrd_ne_top _)
  · rcases ExtOrd.cases y with rfl | rfl | ⟨b, rfl⟩
    · simp_all
    · simp_all
    · rw [blockFloor_ofOrd, blockFloor_ofOrd, ofOrd_inj] at hb
      -- replace `a` at a threshold above both finite parts by the finite part of `b`
      have h := hbot _ hx (max (finitePart a) (finitePart b) + 1) (finitePart b) (by omega)
      rw [extVisibilityReplace_of_finitePart_lt (by omega), hb, limitPart_add_finitePart] at h
      exact h

/-! ## The bottom-aware tail of the bridge -/

/-- Only nonbottom points strictly above their floor need a blocker. -/
def FloorSupport (s : Finset ExtOrd) (f : LabelMap) :=
  ∀ z ∈ s, blockFloor z < z → f z ≠ ⊥ → ∃ y ∈ s, y ≤ blockFloor z ∧ f y ≠ ⊥

theorem table_eq_bot_after_replace_of_floorSupport s f
    (hFloor : FloorSupport s f) (x : ExtOrd) (k i : ℕ)
    (hActive : finiteLowerEnvelope s f x ≤ ⊥) (z : ExtOrd) (hz : z ∈ s)
    (hzReplace : z ≤ extVisibilityReplace x k i) : f z = ⊥ := by
  have hOld : ∀ y ∈ s, y ≤ x → f y = ⊥ := by
    simp_all [VaughtConjecture.Knight.finiteLowerEnvelope]
  by_cases hzOld : z ≤ x
  · exact hOld z hz hzOld
  · by_contra hzBot
    have hFloorLe  :=
      calc blockFloor z ≤ blockFloor (extVisibilityReplace x k i) := blockFloor_mono hzReplace
        _ = blockFloor x := blockFloor_evr x k i
        _ ≤ x := blockFloor_le x
    obtain ⟨y, hy, hyFloor, hyBot⟩ := hFloor z hz (hFloorLe.trans_lt (lt_of_not_ge hzOld)) hzBot
    exact hyBot (hOld y hy (hyFloor.trans hFloorLe))

/-- A `⊥` suppressor supplies every tail bridge from floor support alone. -/
theorem bridge_tail_of_floorSupport (s : Finset ExtOrd) (f : LabelMap) (g : ℕ → ExtOrd)
    (K : ℕ) (hTail : ∀ k, K < k → g k = ⊥) (hFloor : FloorSupport s f)
    (x : ExtOrd) (k : ℕ) (hk : K < k) (hActive : finiteLowerEnvelope s f x ≤ g k) (i : ℕ)
    (z : ExtOrd) (hz : z ∈ s) (hzReplace : z ≤ extVisibilityReplace x k i) :
    f z = ⊥ ∨ ∃ y ∈ s, y ≤ x ∧ f z ≤ extVisibilityReplace (f y) k i := by grind [table_eq_bot_after_replace_of_floorSupport]

/-! ## The full-strip bridge below the controller grade -/

def limitPart_le_of_le_limitPart_add {a b : Ordinal₀} {i : ℕ} (h : a ≤ limitPart b + i) := by
  have := limitPart_mono h
  rwa [limitPart_limitPart_add_nat] at this

def finitePart_le_of_le_limitPart_add {a b} {i : ℕ} (h : a ≤ limitPart b + i)
    (heq : limitPart a = limitPart b) := by
  rw [← limitPart_add_finitePart a, heq] at h
  exact_mod_cast (add_le_add_iff_left _).mp h

/-- **On a full-strip domain, every point visible below a replaced input is dominated by the
replacement of a point below the original input.** -/
theorem exists_source_below_replace (K : ℕ) (t : Finset ExtOrd)
    (hStrip : ∀ a : Ordinal₀, ofOrd a ∈ t → ∀ i : ℕ, i ≤ K → ofOrd (limitPart a + i) ∈ t)
    (x : ExtOrd) {k i : ℕ} (hk : k ≤ K) (_hi : i ≤ k) {z : ExtOrd} (hz : z ∈ t)
    (hzx : z ≤ extVisibilityReplace x k i) :
    ∃ y ∈ t, y ≤ x ∧ z ≤ extVisibilityReplace y k i := by
  rcases ExtOrd.cases z with rfl | rfl | ⟨a, rfl⟩
  · exact ⟨⊥, hz, bot_le, le_rfl⟩
  · have hx : x = ⊤ := by
      simp_all [VaughtConjecture.Knight.Value.extVisibilityReplace] <;> aesop
    exact ⟨⊤, hz, hx ▸ le_rfl, le_rfl⟩
  · -- the strip points `⌊a⌋ + k` (fixed by the replacement) and `⌊a⌋` (the floor)
    have hstripK  := hStrip a hz k hk
    have hfixK : extVisibilityReplace (ofOrd (limitPart a + k)) k i = ofOrd (limitPart a + k) :=
      extVisibilityReplace_of_le_finitePart (by rw [finitePart_limitPart_add_nat]) i
    have hstrip0  := by
      have := hStrip a hz 0 (Nat.zero_le _); rwa [Nat.cast_zero, add_zero] at this
    have ha_le_K : ofOrd a ≤ ofOrd (limitPart a + k) ↔ finitePart a ≤ k := by
      rw [ofOrd_le_ofOrd]
      constructor
      · exact?
      · intro h; conv_lhs => rw [← limitPart_add_finitePart a]
        exact add_le_add le_rfl (by exact_mod_cast h)
    rcases ExtOrd.cases x with rfl | rfl | ⟨b, rfl⟩
    · simp_all
    · -- `x = ⊤`: use `z` itself if it does not move, else the fixed strip point
      by_cases hza : k ≤ finitePart a
      · exact ⟨ofOrd a, hz, le_top, by rw [extVisibilityReplace_of_le_finitePart hza]⟩
      · exact ⟨_, hstripK, le_top, by grind⟩
    · by_cases hfb : finitePart b < k
      · -- `x` moves: `a ≤ ⌊b⌋ + i`
        rw [extVisibilityReplace_of_finitePart_lt hfb, ofOrd_le_ofOrd] at hzx
        have hl := limitPart_le_of_le_limitPart_add hzx
        rcases lt_or_eq_of_le hl with hlt | heq
        · -- `⌊a⌋ < ⌊b⌋`: the fixed strip point `⌊a⌋ + k` lies below `x`
          by_cases hza : k ≤ finitePart a
          · refine ⟨ofOrd a, hz, ?_, by rw [extVisibilityReplace_of_le_finitePart hza]⟩
            rw [ofOrd_le_ofOrd]
            calc a = limitPart a + (finitePart a) := (limitPart_add_finitePart a).symm
              _ ≤ limitPart b := limitPart_add_nat_le_of_lt hlt _
              _ ≤ b := limitPart_le
          · refine ⟨_, hstripK, ?_, by grind⟩
            rw [ofOrd_le_ofOrd]
            exact (limitPart_add_nat_le_of_lt hlt k).trans (limitPart_le)
        · -- same block: `fp a ≤ i`; the floor `⌊a⌋ = ⌊b⌋` lies below `x` and replaces to `⌊b⌋ + i`
          have hfa  := finitePart_le_of_le_limitPart_add hzx heq
          refine ⟨ofOrd (limitPart a), hstrip0, ?_, ?_⟩
          · simp_all [limitPart_le]
          · rw [extVisibilityReplace_of_finitePart_lt (by rw [finitePart_limitPart]; omega),
              limitPart_idem,
              ofOrd_le_ofOrd]
            conv_lhs => rw [← limitPart_add_finitePart a]
            exact add_le_add le_rfl (by exact_mod_cast hfa)
      · -- `x` does not move: `a ≤ b`
        rw [extVisibilityReplace_of_le_finitePart (not_lt.mp hfb)] at hzx
        by_cases hza : k ≤ finitePart a
        · exact ⟨ofOrd a, hz, hzx, by rw [extVisibilityReplace_of_le_finitePart hza]⟩
        · by_cases hai : finitePart a ≤ i
          · exact ⟨ofOrd a, hz, hzx, by
              rw [extVisibilityReplace_of_finitePart_lt (by omega), ofOrd_le_ofOrd]
              conv_lhs => rw [← limitPart_add_finitePart a]
              exact add_le_add le_rfl (by exact_mod_cast hai)⟩
          · refine ⟨_, hstripK, ?_, by grind⟩
            rw [ofOrd_le_ofOrd] at hzx ⊢
            rcases lt_or_eq_of_le (limitPart_mono hzx) with hlt | heq
            · exact (limitPart_add_nat_le_of_lt hlt k).trans (limitPart_le)
            · rw [heq]
              calc limitPart b + (k) ≤ limitPart b + (finitePart b) :=
                    add_le_add le_rfl (by exact_mod_cast (not_lt.mp hfb))
                _ = b := limitPart_add_finitePart b

/-- **The bounded bridge on a full-strip domain**, from monotonicity and bounded commutation. -/
theorem fullStrip_bridge (K : ℕ) (t : Finset ExtOrd) (f : LabelMap)
    (hStrip : ∀ a : Ordinal₀, ofOrd a ∈ t → ∀ i : ℕ, i ≤ K → ofOrd (limitPart a + i) ∈ t)
    (hMono : ∀ a ∈ t, ∀ b ∈ t, a ≤ b → f a ≤ f b)
    (hComm : ∀ a ∈ t, ∀ k i : ℕ, k ≤ K → i ≤ k →
      f (extVisibilityReplace a k i) = extVisibilityReplace (f a) k i)
    (hClosed : ∀ a ∈ t, ∀ k i : ℕ, k ≤ K → i ≤ k → extVisibilityReplace a k i ∈ t)
    (x : ExtOrd) {k : ℕ} (hk : k ≤ K) {i : ℕ} (hi : i ≤ k) {z : ExtOrd} (hz : z ∈ t)
    (hzx : z ≤ extVisibilityReplace x k i) :
    ∃ y ∈ t, y ≤ x ∧ f z ≤ extVisibilityReplace (f y) k i := by
  obtain ⟨y, hy, hyx, hzy⟩ := exists_source_below_replace K t hStrip x hk hi hz hzx
  exact ⟨y, hy, hyx, (hMono z hz _ (hClosed y hy k i hk hi) hzy).trans_eq (hComm y hy k i hk hi)⟩

/-! ## The assembled floor completion -/

/-- **Floor completion**: on the strip domain of a closed inventory, the table `τ ∘ roundUp`
of a bounded, monotone, bottom-preserving shifter that commutes with all bounded replacements
and whose `⊥`-fibre propagates has bottom, monotonicity, the weak orbit law, and the
unrestricted block bridge, against any suppressor vanishing above `K`. -/
theorem floorCompletion (K : ℕ) (s : Finset ExtOrd) (τ : LabelMap) (g : ℕ → ExtOrd)
    (hClosed : ∀ x ∈ s, ∀ k i : ℕ, k ≤ K → i ≤ k → extVisibilityReplace x k i ∈ s)
    (hBot : τ ⊥ = ⊥) (hMono : Monotone τ)
    (hBotProp : ∀ x, τ x = ⊥ → ∀ k i, i ≤ k → τ (extVisibilityReplace x k i) = ⊥)
    (hComm : ∀ x k i, k ≤ K → i ≤ k →
      τ (extVisibilityReplace x k i) = extVisibilityReplace (τ x) k i)
    (hTail : ∀ k, K < k → g k = ⊥) :
    (∀ y ∈ stripDomain K s, y = ⊥ → τ (roundUp s y) = ⊥) ∧
    (∀ a ∈ stripDomain K s, ∀ b ∈ stripDomain K s, a ≤ b → τ (roundUp s a) ≤ τ (roundUp s b)) ∧
    FiniteShifterWeakOrbit (stripDomain K s) (fun x => τ (roundUp s x)) g ∧
    FiniteShifterBlockBridge (stripDomain K s) (fun x => τ (roundUp s x)) g := by
  set t := stripDomain K s with ht
  set F : LabelMap := fun x => τ (roundUp s x) with hF
  have hFM  := hMono.comp (roundUp_mono s)
  have hFC : ∀ x k i, k ≤ K → i ≤ k →
      F (extVisibilityReplace x k i) = extVisibilityReplace (F x) k i := by
    grind [roundUp_commutes]
  have hFloor : FloorSupport t F := by
    intro z hz _ hzBot
    refine ⟨blockFloor z, stripDomain_floor_mem hz, le_rfl, ?_⟩
    intro hBad
    apply hzBot
    exact bot_of_same_block hBotProp  
      (by simp_all [blockFloor_roundUp, blockFloor_idem]) hBad
  refine ⟨?_, ?_, ?_, ?_⟩
  · grind [roundUp_bot]
  · aesop
  · intro x hx k i hi hActive
    by_cases hk : k ≤ K
    · simp_all [stripDomain_closed]
    · simp_all
  · intro x k hActive i hi z hz hzx
    by_cases hk : k ≤ K
    · exact Or.inr (fullStrip_bridge K t F (fun a ha i hi => stripDomain_fullStrips ha hi)
        (fun a _ b _ hab => hFM hab) (fun a _ k i hk hi => hFC a k i hk hi)
        (fun a ha k i hk hi => stripDomain_closed ha hk hi) x hk hi hz hzx)
    · exact bridge_tail_of_floorSupport t F g K hTail hFloor x k (lt_of_not_ge hk) hActive i z hz
        hzx

