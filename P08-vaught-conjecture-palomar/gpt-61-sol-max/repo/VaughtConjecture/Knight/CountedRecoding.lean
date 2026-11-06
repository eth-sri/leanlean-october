import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.RowCorrectness
import VaughtConjecture.Knight.VisibilityAlgebra
import VaughtConjecture.Knight.SemScheme
import VaughtConjecture.Knight.Reduction
import VaughtConjecture.Knight.NormalForm
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat

/-! # The counted recoding of a finite row at a target grade

**The one-step interface of construction-time sharp coding.**  Given a finite set `S` of ordinal
values (the nonbottom values of a row), a cap `γ` self-visible at the target grade `l ≥ 1` and
dominating `S`, this module codes each `v ∈ S` at grade `l` and builds the decoder `σ` that is
the Def. 2.3.9 shifter of the clause-4 witness `G ⇒ (F ↾ dom G) ∧ F(G)` of Knight's stacks
(Def. 4.3.5): `transformsTo_of_shift` is the packaged `TransformsTo` witness with the step
suppressor at a cap `ρ` up to grade `l`.

**Why the code has this shape.**  Def. 2.3.9 clause 5 is unguarded: for every `α` with
`σ α ≤ g k` and every `i ≤ k`, `σ (α ⊔⁺_k i) = σ α ⊔⁺_k i`.  At `k = l` this forces the decoder,
on the code block hosting a value `v`, to be `j ↦ v ⊔⁺_l (min j l)`; so the code must carry `v`'s
finite part up to `l`, values of one `ω`-block with finite part `≤ l` share a code block, and a
value with larger finite part needs its own constant block.  (A value-counted code `ω·cnt v + l`
with a block-constant decoder fails clause 5 exactly on values whose finite part is below `l`,
which every row with cells of grade `< l` contains.)  Hence:

* the **key** of `v = lp + fp` is `lp` if `fp ≤ l`, else `v` (`keyOrd`);
* the **block** of `v` is the number of keys of `S` at most its key (`blockOf`) — a count, so
  no enumeration is chosen;
* the **code** is `ω·blockOf v + min (fp v) l` (`code`): coded at `l` (`code_isCoded`),
  self-visible at every cell grade `a ≤ fp v`, `a ≤ l` (`code_selfVis`);
* the **decoder** `shift`: on the block of an `ω`-block key `κ`, `j ↦ κ + min j l`; on the block
  of a large key, constantly that key; `⊥` on block `0`; `γ` on every block past the last key;
  `⊥ ↦ ⊥`, `⊤ ↦ γ`.

**Proved**: `shift_mono` (across blocks a key's block never reaches the next key,
`key_add_le_next`, through the block-key bijection `exists_key_of_block`), `shift_code` (exact
decoding), `shift_capCode` (the cap code `ω·(|keys| + 1) + l` decodes to `γ`),
`shift_evr_of_le` (clause 5 for every `k ≤ l`, unguarded) and `shift_evr_of_bot` (for `k > l`
under `σ α = ⊥`), and `transformsTo_of_shift`.

**Integration notes.**  Positive cell grades come from graded-plan membership
(`CellScheme.grade_pos`), and coded labels are never `⊤` (`IsCodedLabel.ne_top`); neither is a
construction hypothesis.  The value set fed to the recoding is the **primitive** lower-grade range of
the row (its nonbottom values at proper cells of grade at most the target), and nothing else:
auxiliary cap values must not enter it, since they would change the key count; and the derived
directed values a recursive construction introduces should need no keys of their own, because
each should lie in the decoder image of an already represented lower-stratum value.  That
decoder-image invariant is **proved at three levels** (`Knight/ThreeLevelFragment.lean`,
`Core3.rho1_eq_dec2_rho`); an arbitrary-depth recursion must preserve it level by level — it is
not yet a compiled general theorem.

Construction-private (not root-exported).  Reviewer scout (2026-09-05), graduated: the algebra
has passed unguarded clause 5 above grade one and the `3 → 2 → 1` coherence triangle
(`Knight/RecodingTriangle.lean`). -/

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-! ## Value lemmas -/

/-- The block index `α / ω`. -/
noncomputable def blockIdx (α : Ordinal₀) := α / Ordinal.omega0

theorem blockIdx_mul_add (t j : ℕ) : blockIdx (Ordinal.omega0 * t + j) = t := by
  unfold blockIdx
  rw [Ordinal.mul_add_div _ Ordinal.omega0_ne_zero,
    Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 j), add_zero]

theorem blockIdx_mono {α β} (h : α ≤ β) : blockIdx α ≤ blockIdx β :=  (Ordinal.mul_le_iff_le_div Ordinal.omega0_ne_zero).mp
    ((Ordinal.mul_div_le α Ordinal.omega0).trans h)

theorem limitPart_eq_mul_blockIdx α :
    limitPart α = Ordinal.omega0 * blockIdx α := rfl

theorem blockIdx_visibilityReplace α k i :
    blockIdx (visibilityReplace α k i) = blockIdx α := by
  unfold visibilityReplace
  split_ifs with h
  · simp_all [ordinalReplace, limitPart_eq_mul_blockIdx, blockIdx, Ordinal.mul_add_div, Ordinal.div_eq_zero_of_lt]
  · rfl

theorem finitePart_visibilityReplace α k i :
    finitePart (visibilityReplace α k i) = if finitePart α < k then i else finitePart α := by
  unfold visibilityReplace
  split_ifs with h
  · unfold ordinalReplace; exact finitePart_limitPart_add_nat _ _
  · rfl

theorem limitPart_mul_nat (t : ℕ) : limitPart (Ordinal.omega0 * t) = Ordinal.omega0 * t := by
  unfold limitPart
  rw [Ordinal.mul_div_cancel _ Ordinal.omega0_ne_zero]

theorem finitePart_mul_add (t j : ℕ) : finitePart (Ordinal.omega0 * t + j) = j := by simp_all [VaughtConjecture.Knight.Value.finitePart]

theorem limitPart_mul_add (t j : ℕ) : limitPart (Ordinal.omega0 * t + j) = Ordinal.omega0 * t := by
  have := limitPart_limitPart_add_nat (Ordinal.omega0 * t) j
  rwa [limitPart_mul_nat] at this

theorem selfVis_ofOrd_iff {α} {k} : SelfVis k (ofOrd α) ↔ k ≤ finitePart α := by
  unfold SelfVis
  rw [extVisibilityReplace_ofOrd, ofOrd_inj]
  unfold visibilityReplace
  constructor
  · exact visibilityReplace_self_iff.mp
  · simp_all

/-- The limit part of a limit part is itself. -/
def limitPart_idem α := by
  have := limitPart_limitPart_add_nat α 0
  simpa using this

/-- Two ordinals with the same limit part compare by their finite parts. -/
theorem le_of_finitePart_le {α β} (hl : limitPart α = limitPart β)
    (hf : finitePart α ≤ finitePart β) : α ≤ β := by
  rw [← limitPart_add_finitePart α, ← limitPart_add_finitePart β, hl]
  exact add_le_add le_rfl (by exact_mod_cast hf)

/-- A larger limit part dominates any finite offset. -/
theorem limitPart_add_nat_le_of_lt {α β : Ordinal₀} (h : limitPart α < limitPart β) (j : ℕ) :
    limitPart α + j ≤ limitPart β := by
  rw [limitPart_eq_mul_blockIdx, limitPart_eq_mul_blockIdx] at *
  
  calc Ordinal.omega0 * blockIdx α + j ≤ Ordinal.omega0 * blockIdx α + Ordinal.omega0 :=
        add_le_add le_rfl (Ordinal.natCast_lt_omega0 j).le
    _ = Ordinal.omega0 * (blockIdx α + 1) := by rw [mul_add, mul_one]
    _ ≤ Ordinal.omega0 * blockIdx β := by simp_all

/-! ## Keys, blocks, codes -/

section

variable (l : ℕ) (S : Finset Ordinal₀) (γ : ExtOrd)

/-- The key of a value: its `ω`-block when the finite part is `≤ l`, itself otherwise. -/
noncomputable def keyOrd v :=
  if finitePart v ≤ l then limitPart v else v

local notation "keyOrd₀" => keyOrd l

theorem keyOrd_le v : keyOrd₀ v ≤ v := by
  unfold keyOrd; split_ifs
  · exact limitPart_le
  · exact le_rfl

/-- A key is an `ω`-block key (finite part `0`) or a large value (finite part `> l`). -/
theorem finitePart_keyOrd v :
    finitePart (keyOrd₀ v) = 0 ∨ l < finitePart (keyOrd₀ v) := by
  unfold keyOrd; split_ifs with h
  · simp_all [finitePart_limitPart]
  · exact Or.inr (not_le.mp h)

/-- The key set of the row. -/
noncomputable def keys := S.image (keyOrd₀)

local notation "keys₀" => keys l S

/-- The block of a key: the number of keys at most it. -/
noncomputable def blockOfKey κ := ((keys₀).filter fun κ' => κ' ≤ κ).card

local notation "blockOfKey₀" => blockOfKey l S

/-- The block of a value. -/
noncomputable def blockOf v := blockOfKey₀ (keyOrd₀ v)

theorem blockOfKey_le κ : blockOfKey₀ κ ≤ (keys₀).card :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem blockOfKey_mono {κ κ'} (h : κ ≤ κ') : blockOfKey₀ κ ≤ blockOfKey₀ κ' := by unfold blockOfKey; gcongr

theorem blockOfKey_lt {κ κ'} (hκ' : κ' ∈ keys₀) (h : κ < κ') :
    blockOfKey₀ κ < blockOfKey₀ κ' := by
  apply Finset.card_lt_card
  refine ⟨fun x hx => ?_, fun hsub => ?_⟩
  · grind
  · have := hsub (Finset.mem_filter.mpr ⟨hκ', le_rfl⟩)
    exact absurd (Finset.mem_filter.mp this).2 (not_le.mpr h)

theorem blockOfKey_pos {κ : Ordinal₀} (hκ : κ ∈ keys₀) : 0 < blockOfKey₀ κ :=
  Finset.card_pos.mpr ⟨κ, Finset.mem_filter.mpr ⟨hκ, le_rfl⟩⟩

theorem keyOrd_mem_keys {v : Ordinal₀} (hv : v ∈ S) : keyOrd₀ v ∈ keys₀ :=
  Finset.mem_image.mpr ⟨v, hv, rfl⟩

/-- **The code** of a value: `ω·block + min (fp v) l`. -/
noncomputable def code (v : Ordinal₀) : Ordinal₀ :=
  Ordinal.omega0 * (blockOf l S v : ℕ) + (min (finitePart v) l : ℕ)

theorem code_isCoded (v : Ordinal₀) : IsCodedLabel l (ofOrd (code l S v)) :=
  Or.inr ⟨blockOf l S v, min (finitePart v) l, by omega, rfl⟩

theorem code_selfVis {v : Ordinal₀} {a : ℕ} (ha : a ≤ finitePart v) (hal : a ≤ l) :
    SelfVis a (ofOrd (code l S v)) := by
  rw [selfVis_ofOrd_iff]
  unfold code
  rw [finitePart_mul_add]
  exact le_min ha hal

/-- The cap code: one block past every key, finite part `l`. -/
noncomputable def capCode : Ordinal₀ := Ordinal.omega0 * (((keys₀).card + 1 : ℕ) : Ordinal) + l

theorem capCode_selfVis : SelfVis l (ofOrd (capCode l S)) := by
  rw [selfVis_ofOrd_iff]; unfold capCode; rw [finitePart_mul_add]

theorem capCode_isCoded : IsCodedLabel l (ofOrd (capCode l S)) :=
  Or.inr ⟨(keys₀).card + 1, l, by omega, rfl⟩

theorem code_le_capCode (v : Ordinal₀) : code l S v ≤ capCode l S := by
  
  have h1  := by
    exact_mod_cast (by solve_by_elim [blockOfKey_le] :
      blockOf l S v ≤ (keys l S).card + 1)
  have h2 : ((min (finitePart v) l : ℕ)) ≤ (l : Ordinal) := by
    exact_mod_cast min_le_right _ _
  calc Ordinal.omega0 * (blockOf l S v) + (min (finitePart v) l)
      ≤ Ordinal.omega0 * (blockOf l S v) + (l) := add_le_add le_rfl h2
    _ ≤ Ordinal.omega0 * (((keys l S).card + 1 : ℕ)) + l := by gcongr

/-! ## The decoder -/

/-- The key hosted on block `t`: the largest key with block `≤ t` (`⊥` if none). -/
noncomputable def keyAt (t : Ordinal₀) :=
  ((keys l S).filter fun κ => ((blockOfKey l S κ : ℕ) : Ordinal) ≤ t).max

/-- Decoding on the block of a key `κ` at finite offset `j`. -/
noncomputable def decodeIn (κ : Ordinal₀) (j : ℕ) :=
  if finitePart κ = 0 then κ + (min j l : ℕ) else κ

local notation "keyAt₀" => keyAt l S

/-- **The decoder.** -/
noncomputable def shift : LabelMap
  | ⊥ => ⊥
  | some ⊤ => γ
  | some (some α) =>
      if (((keys₀).card + 1 : ℕ) : Ordinal) ≤ blockIdx α then γ
      else match keyAt₀ (blockIdx α) with
        | ⊥ => ⊥
        | some κ => ofOrd (decodeIn l κ (finitePart α))

local notation "shift₀" => shift l S γ

theorem shift_bot : shift₀ ⊥ = ⊥ := rfl
theorem shift_top : shift₀ ⊤ = γ := rfl
theorem shift_ofOrd (α : Ordinal₀) :
    shift₀ (ofOrd α) =
      if (((keys₀).card + 1 : ℕ) : Ordinal) ≤ blockIdx α then γ
      else match keyAt₀ (blockIdx α) with
        | ⊥ => ⊥
        | some κ => ofOrd (decodeIn l κ (finitePart α)) := rfl

theorem keyAt_eq_of_mem {κ : Ordinal₀} (hκ : κ ∈ keys₀) :
    keyAt₀ (blockOfKey₀ κ) = some κ := by
  
  apply le_antisymm
  · apply Finset.max_le
    intro κ' hκ'
    have h := (Finset.mem_filter.mp hκ').2
    have h' : blockOfKey₀ κ' ≤ blockOfKey₀ κ := by exact_mod_cast h
    by_contra hlt
    have hlt' : κ < κ' := by
      rcases lt_or_ge κ κ' with hh | hh
      · exact hh
      · solve_by_elim
    exact absurd h' (not_le.mpr (blockOfKey_lt l S (Finset.mem_filter.mp hκ').1 hlt'))
  · exact Finset.le_max (Finset.mem_filter.mpr ⟨hκ, le_rfl⟩)

theorem keyAt_zero : keyAt₀ 0 = ⊥ := by
  
  apply Finset.max_eq_bot.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro κ hκ h
  have  := le_antisymm h zero_le
  have h0 : blockOfKey₀ κ = 0 := by exact_mod_cast this
  exact absurd h0 (Nat.pos_iff_ne_zero.mp (blockOfKey_pos l S hκ))

/-- **Exact decoding**: the code of a member of `S` decodes to it. -/
theorem shift_code {v : Ordinal₀} (hv : v ∈ S) : shift₀ (ofOrd (code l S v)) = ofOrd v := by
  rw [shift_ofOrd]
  unfold code
  rw [blockIdx_mul_add, finitePart_mul_add]
  have hb : blockOf l S v ≤ (keys₀).card := blockOfKey_le l S _
  rw [if_neg (by
    simp_all)]
  unfold blockOf
  rw [keyAt_eq_of_mem l S (keyOrd_mem_keys l S hv)]
  simp 
  congr 1
  unfold decodeIn
  rcases finitePart_keyOrd l v with h0 | hl
  · 
    unfold keyOrd at h0 ⊢
    split_ifs at h0 ⊢ with hfp
    · simp_all [limitPart_add_finitePart]
    · simp_all
  · rw [if_neg (by omega)]
    unfold keyOrd at hl ⊢
    split_ifs at hl ⊢ with hfp
    · simp_all [finitePart_limitPart]
    · rfl

/-- **Cap decoding**: the cap code decodes to `γ`. -/
theorem shift_capCode : shift₀ (ofOrd (capCode l S)) = γ := by
  rw [shift_ofOrd]
  unfold capCode
  rw [blockIdx_mul_add, if_pos le_rfl]

/-! ### Monotonicity -/

/-- The values decoded on the block of a key `κ` lie in `[κ, κ + l]`. -/
theorem decodeIn_ge (κ : Ordinal₀) (j : ℕ) : κ ≤ decodeIn l κ j := by
  unfold decodeIn; split_ifs
  · exact le_self_add
  · exact le_rfl

theorem decodeIn_le (κ : Ordinal₀) (j : ℕ) : decodeIn l κ j ≤ κ + l := by simp_all [decodeIn] <;> aesop

theorem decodeIn_mono (κ : Ordinal₀) {j j' : ℕ} (h : j ≤ j') :
    decodeIn l κ j ≤ decodeIn l κ j' := by simp_all [decodeIn] <;> aesop

/-- **A key's block never reaches the next key**: for keys `κ < κ'`, `κ + l ≤ κ'`. -/
theorem key_add_le_next {κ κ' : Ordinal₀} (hκ : κ ∈ keys₀) (hκ' : κ' ∈ keys₀)
    (h : κ < κ') (h0 : finitePart κ = 0) : κ + l ≤ κ' := by
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hκ
  obtain ⟨v', -, rfl⟩ := Finset.mem_image.mp hκ'
  rcases lt_or_ge (limitPart (keyOrd₀ v)) (limitPart (keyOrd₀ v')) with hlt | hge
  · -- a later `ω`-block dominates any finite offset
    have h1 : keyOrd₀ v = limitPart (keyOrd₀ v) := by
      exact?
    rw [h1]
    exact (limitPart_add_nat_le_of_lt hlt l).trans (limitPart_le)
  · -- same `ω`-block: `κ'` is a large value, `κ` the block key
    have heq  :=
      le_antisymm (limitPart_mono h.le) hge
    rcases finitePart_keyOrd l v' with h0' | hl'
    · simp_all only [keyOrd, limitPart] <;> aesop
    · have e1 : keyOrd₀ v = limitPart (keyOrd₀ v) := by
        exact?
      rw [e1, heq]
      conv_rhs => rw [← limitPart_add_finitePart (keyOrd₀ v')]
      exact add_le_add le_rfl (by exact_mod_cast hl'.le)

theorem keyAt_mem {t κ : Ordinal₀} (h : keyAt₀ t = some κ) : κ ∈ keys₀ :=
  (Finset.mem_filter.mp (Finset.mem_of_max h)).1

/-- Below a cap `γ` self-visible at `l` that dominates the values, the key-block values
`κ + l` stay below `γ`. -/
theorem key_add_l_le {v g : Ordinal₀} (hv : v ≤ g) (hg : l ≤ finitePart g)
    (h0 : finitePart (keyOrd₀ v) = 0) : keyOrd₀ v + l ≤ g := by
  have e1 : keyOrd₀ v = limitPart v := by
    grind [keyOrd]
  rw [e1]
  rcases lt_or_ge (limitPart v) (limitPart g) with hlt | hge
  · exact (limitPart_add_nat_le_of_lt hlt l).trans (limitPart_le)
  · have heq : limitPart v = limitPart g := le_antisymm (limitPart_mono hv) hge
    rw [heq]
    conv_rhs => rw [← limitPart_add_finitePart g]
    exact add_le_add le_rfl (by exact_mod_cast hg)

theorem decodeIn_le_of_key {v g : Ordinal₀} (hv : v ≤ g)
    (hg : l ≤ finitePart g) (j : ℕ) : decodeIn l (keyOrd₀ v) j ≤ g := by
  unfold decodeIn
  split_ifs with h0
  · exact (add_le_add le_rfl (by exact_mod_cast min_le_right j l)).trans (key_add_l_le l hv hg h0)
  · exact (keyOrd_le l v).trans hv

theorem shift_ofOrd_le_γ (hγ : SelfVis l γ) (hS : ∀ v ∈ S, ofOrd v ≤ γ) (α : Ordinal₀) :
    shift₀ (ofOrd α) ≤ γ := by
  rw [shift_ofOrd]
  split_ifs with h
  · exact le_rfl
  · rcases hk : keyAt₀ (blockIdx α) with _ | κ
    · exact bot_le
    · 
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (keyAt_mem l S hk)
      have hvγ := hS v hv
      rcases ExtOrd.cases γ with rfl | rfl | ⟨g, rfl⟩
      · simp_all
      · exact le_top
      · rw [ofOrd_le_ofOrd] at hvγ ⊢
        exact decodeIn_le_of_key l hvγ (selfVis_ofOrd_iff.mp hγ) _

/-! ### The block-key bijection -/

theorem blockOfKey_injOn : Set.InjOn (blockOfKey₀) (keys₀) := by (
  intro κ hκ κ' hκ' h
  by_contra hne
  rcases lt_or_gt_of_ne hne <;> simp_all [lt_or_gt_of_ne, ne_of_lt, blockOfKey_lt, ne_of_gt])

theorem blockOfKey_mem_Icc {κ : Ordinal₀} (hκ : κ ∈ keys₀) :
    blockOfKey₀ κ ∈ Finset.Icc 1 (keys₀).card := by grind [blockOfKey_pos, blockOfKey_le]

/-- Every block `1 … |keys|` is the block of exactly one key. -/
theorem exists_key_of_block {n : ℕ} (h1 : 1 ≤ n) (hn : n ≤ (keys₀).card) :
    ∃ κ ∈ keys₀, blockOfKey₀ κ = n := by
  have himg : (keys₀).image (blockOfKey₀) = Finset.Icc 1 (keys₀).card := by
    apply Finset.eq_of_subset_of_card_le
    · grind [blockOfKey_mem_Icc]
    · grind [blockOfKey_injOn, Nat.card_Icc]
  have : n ∈ (keys₀).image (blockOfKey₀) := by
    simp_all
  obtain ⟨κ, hκ, hb⟩ := Finset.mem_image.mp this
  exact ⟨κ, hκ, hb⟩

theorem keyAt_nat_eq_some {t : ℕ} (h1 : 1 ≤ t) (ht : t ≤ (keys₀).card) :
    ∃ κ ∈ keys₀, keyAt₀ t = some κ ∧ blockOfKey₀ κ = t := by grind only [exists_key_of_block, keyAt_eq_of_mem]

/-- Block indices below `|keys| + 1` are naturals. -/
theorem exists_nat_of_lt_card {t : Ordinal₀} (h : t < (((keys₀).card + 1 : ℕ) : Ordinal)) :
    ∃ n : ℕ, t = n ∧ n ≤ (keys₀).card := by
  obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp (h.trans_le (Ordinal.natCast_lt_omega0 _).le)
  
  exact ⟨n, rfl, by simp_all⟩

/-! ### Monotonicity -/

theorem finitePart_le_of_le_of_limitPart_eq {α β : Ordinal₀} (h : α ≤ β)
    (hl : limitPart α = limitPart β) : finitePart α ≤ finitePart β := by exact?

theorem shift_mono (hγ : SelfVis l γ) (hS : ∀ v ∈ S, ofOrd v ≤ γ) : Monotone (shift₀) := by
  intro x y hxy
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · rw [shift_bot]; exact bot_le
  · simp_all
  · rcases ExtOrd.cases y with rfl | rfl | ⟨β, rfl⟩
    · simp_all
    · exact?
    · have hαβ := ofOrd_le_ofOrd.mp hxy
      have hb := blockIdx_mono hαβ
      rw [shift_ofOrd, shift_ofOrd]
      by_cases h1 : (((keys₀).card + 1 : ℕ) : Ordinal) ≤ blockIdx α
      · grind
      · rw [if_neg h1]
        by_cases h2 : (((keys₀).card + 1 : ℕ) : Ordinal) ≤ blockIdx β
        · rw [if_pos h2]
          have := shift_ofOrd_le_γ l S γ hγ hS α
          rw [shift_ofOrd, if_neg h1] at this
          exact this
        · rw [if_neg h2]
          obtain ⟨n, hn, hnle⟩ := exists_nat_of_lt_card l S (not_le.mp h1)
          obtain ⟨m, hm, hmle⟩ := exists_nat_of_lt_card l S (not_le.mp h2)
          rw [hn, hm]
          rw [hn, hm] at hb
          have hnm  := by exact_mod_cast hb
          rcases Nat.eq_zero_or_pos n with rfl | hnpos
          · simp_all [keyAt_zero]
          · obtain ⟨κ, hκ, hk, hbκ⟩ := keyAt_nat_eq_some l S hnpos hnle
            obtain ⟨κ', hκ', hk', hbκ'⟩ := keyAt_nat_eq_some l S (hnpos.trans_le hnm) hmle
            rw [hk, hk']
            simp only
            rw [ofOrd_le_ofOrd]
            rcases Nat.eq_or_lt_of_le hnm with heq | hlt
            · -- same block: same key, compare finite parts
              grind only [limitPart_eq_mul_blockIdx, decodeIn_mono, finitePart_le_of_le_of_limitPart_eq]
            · -- different blocks: `κ < κ'`, and the block of `κ` never reaches `κ'`
              have hκlt : κ < κ' := by
                by_contra hge
                have := blockOfKey_mono l S (not_lt.mp hge)
                omega
              rcases Nat.eq_zero_or_pos (finitePart κ) with h0 | hpos
              · exact (decodeIn_le l κ _).trans
                  ((key_add_le_next l S hκ hκ' hκlt h0).trans (decodeIn_ge l κ' _))
              · grind [decodeIn, decodeIn_ge]

/-! ### Clause 5 -/

theorem limitPart_mul (μ : Ordinal₀) : limitPart (Ordinal.omega0 * μ) = Ordinal.omega0 * μ := by
  unfold limitPart
  rw [Ordinal.mul_div_cancel _ Ordinal.omega0_ne_zero]

theorem finitePart_mul_add' (μ : Ordinal₀) (m : ℕ) :
    finitePart (Ordinal.omega0 * μ + m) = m := by simp_all [VaughtConjecture.Knight.Value.finitePart]

theorem limitPart_mul_add' (μ : Ordinal₀) (m : ℕ) :
    limitPart (Ordinal.omega0 * μ + m) = Ordinal.omega0 * μ := by
  have := limitPart_limitPart_add_nat (Ordinal.omega0 * μ) m
  rwa [limitPart_mul] at this

theorem finitePart_mul (μ : Ordinal₀) : finitePart (Ordinal.omega0 * μ) = 0 := by
  rw [← limitPart_mul μ]
  exact finitePart_limitPart _

theorem key_finitePart {κ : Ordinal₀} (hκ : κ ∈ keys₀) : finitePart κ = 0 ∨ l < finitePart κ := by
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hκ
  exact finitePart_keyOrd l v

/-- **Clause 5 below the target grade, unguarded**: for `k ≤ l`, the decoder commutes with
visibility replacement at threshold `k`. -/
theorem shift_evr_of_le (hγ : SelfVis l γ) {k : ℕ} (hk : k ≤ l) (x : ExtOrd) {i : ℕ} (hi : i ≤ k) :
    shift₀ (extVisibilityReplace x k i) = extVisibilityReplace (shift₀ x) k i := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · simp [shift_bot]
  · rw [extVisibilityReplace_top, shift_top]
    exact (evr_eq_self_of_selfVis (hγ.mono hk)).symm
  · rw [extVisibilityReplace_ofOrd, shift_ofOrd, shift_ofOrd, blockIdx_visibilityReplace]
    split_ifs with h
    · exact (evr_eq_self_of_selfVis (hγ.mono hk)).symm
    · rcases hkA : keyAt₀ (blockIdx α) with _ | κ
      · simp
      · simp only
        rw [extVisibilityReplace_ofOrd, ofOrd_inj, finitePart_visibilityReplace]
        have hκ := keyAt_mem l S hkA
        rcases key_finitePart l S hκ with h0 | hl
        · -- an `ω`-block key: `κ = ω·μ`
          obtain ⟨μ, rfl⟩ : ∃ μ, κ = Ordinal.omega0 * μ :=
            ⟨blockIdx κ, by
              rw [← limitPart_eq_mul_blockIdx]
              conv_lhs => rw [← limitPart_add_finitePart κ]
              rw [h0]; simp⟩
          unfold decodeIn
          rw [if_pos (finitePart_mul μ), if_pos (finitePart_mul μ)]
          unfold visibilityReplace
          rw [finitePart_mul_add']
          by_cases hfp : finitePart α < k
          · grind [ordinalReplace, limitPart_mul_add']
          · grind
        · -- a large key: constant block, finite part `> l ≥ k`
          grind [decodeIn, visibilityReplace]

/-- **Clause 5 above the target grade**: a `⊥` value stays `⊥` under replacement. -/
theorem shift_evr_of_bot (x : ExtOrd) (k i : ℕ) (h : shift₀ x = ⊥) :
    shift₀ (extVisibilityReplace x k i) = ⊥ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · simp [shift_bot]
  · simp_all
  · rw [extVisibilityReplace_ofOrd, shift_ofOrd, blockIdx_visibilityReplace]
    rw [shift_ofOrd] at h
    split_ifs at h ⊢ with h1
    · exact h
    · aesop

/-- **The packaged transformation witness**: any row `G` transforms to its decoding capped at a
self-visible `ρ` up to grade `l`. -/
theorem transformsTo_of_shift {D : Type*} (grade : D → ℕ) (hγ : SelfVis l γ)
    (hS : ∀ v ∈ S, ofOrd v ≤ γ) (G : D → ExtOrd) {ρ : ExtOrd} (hρ : SelfVis l ρ) :
    TransformsTo grade G (fun d => min (shift₀ (G d)) (if grade d ≤ l then ρ else ⊥)) := by
  refine ⟨fun k => if k ≤ l then ρ else ⊥, shift₀, ?_, ?_, shift_bot l S γ,
    shift_mono l S γ hγ hS, ?_, fun _ => rfl⟩
  · grind [bot_le]
  · intro n
    dsimp only
    split_ifs with h
    · exact (hρ.mono h).symm
    · simp
  · intro α k hle i hi
    by_cases hk : k ≤ l
    · exact?
    · simp_all [shift_evr_of_bot]


/-! ## Integration bridges: nothing here is a construction hypothesis -/

