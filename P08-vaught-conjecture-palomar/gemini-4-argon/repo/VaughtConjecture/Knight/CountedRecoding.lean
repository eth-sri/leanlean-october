/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RowCorrectness
public import VaughtConjecture.Knight.VisibilityAlgebra
public import VaughtConjecture.Knight.SemScheme
public import VaughtConjecture.Knight.Reduction
public import VaughtConjecture.Knight.NormalForm
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Nat

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

@[expose] public noncomputable section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-! ## Value lemmas -/

/-- The block index `α / ω`. -/
def blockIdx (α : Ordinal.{0}) : Ordinal.{0} := α / Ordinal.omega0

theorem blockIdx_mul_add (t : ℕ) (j : ℕ) : blockIdx (Ordinal.omega0 * t + j) = t := by
  unfold blockIdx
  rw [Ordinal.mul_add_div _ Ordinal.omega0_ne_zero,
    Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 j), add_zero]

theorem blockIdx_mono {α β : Ordinal.{0}} (h : α ≤ β) : blockIdx α ≤ blockIdx β := by
  unfold blockIdx
  exact (Ordinal.mul_le_iff_le_div Ordinal.omega0_ne_zero).mp
    ((Ordinal.mul_div_le α Ordinal.omega0).trans h)

theorem limitPart_eq_mul_blockIdx (α : Ordinal.{0}) :
    limitPart α = Ordinal.omega0 * blockIdx α := rfl

theorem blockIdx_visibilityReplace (α : Ordinal.{0}) (k i : ℕ) :
    blockIdx (visibilityReplace α k i) = blockIdx α := by
  unfold visibilityReplace
  split_ifs
  · exact code_div_omega0 (blockIdx α) i
  · rfl

theorem finitePart_visibilityReplace (α : Ordinal.{0}) (k i : ℕ) :
    finitePart (visibilityReplace α k i) = if finitePart α < k then i else finitePart α := by
  unfold visibilityReplace
  split_ifs
  · exact finitePart_limitPart_add_nat _ _
  · rfl

theorem limitPart_mul_nat (t : ℕ) : limitPart (Ordinal.omega0 * t) = Ordinal.omega0 * t :=
  limitPart_omega0_mul t

theorem finitePart_mul_add (t j : ℕ) : finitePart (Ordinal.omega0 * t + j) = j :=
  finitePart_code t j

theorem limitPart_mul_add (t j : ℕ) : limitPart (Ordinal.omega0 * t + j) = Ordinal.omega0 * t :=
  limitPart_code t j

theorem selfVis_ofOrd_iff {α : Ordinal.{0}} {k : ℕ} : SelfVis k (ofOrd α) ↔ k ≤ finitePart α := by
  unfold SelfVis
  rw [extVisibilityReplace_ofOrd, ofOrd_inj]
  exact visibilityReplace_self_iff α k

/-- The limit part of a limit part is itself. -/
theorem limitPart_idem (α : Ordinal.{0}) : limitPart (limitPart α) = limitPart α :=
  Value.limitPart_idem α

/-- Two ordinals with the same limit part compare by their finite parts. -/
theorem le_of_finitePart_le {α β : Ordinal.{0}} (hl : limitPart α = limitPart β)
    (hf : finitePart α ≤ finitePart β) : α ≤ β := by
  rw [← limitPart_add_finitePart α, ← limitPart_add_finitePart β, hl]
  exact add_le_add le_rfl (Nat.cast_le.mpr hf)

/-- A larger limit part dominates any finite offset. -/
theorem limitPart_add_nat_le_of_lt {α β : Ordinal.{0}} (h : limitPart α < limitPart β) (j : ℕ) :
    limitPart α + j ≤ limitPart β :=
  (add_le_add le_rfl (Ordinal.natCast_lt_omega0 j).le).trans (limitPart_add_omega0_le h)

/-! ## Keys, blocks, codes -/

section Recoding

variable (l : ℕ) (S : Finset Ordinal.{0}) (γ : ExtOrd)

/-- The key of a value: its `ω`-block when the finite part is `≤ l`, itself otherwise. -/
def keyOrd (v : Ordinal.{0}) : Ordinal.{0} :=
  if finitePart v ≤ l then limitPart v else v

theorem keyOrd_le (v : Ordinal.{0}) : keyOrd l v ≤ v := by
  unfold keyOrd; split_ifs; exacts [limitPart_le v, le_rfl]

theorem limitPart_keyOrd (v : Ordinal.{0}) : limitPart (keyOrd l v) = limitPart v := by
  unfold keyOrd; split_ifs; exacts [limitPart_idem v, rfl]

/-- A key is an `ω`-block key (finite part `0`) or a large value (finite part `> l`). -/
theorem finitePart_keyOrd (v : Ordinal.{0}) :
    finitePart (keyOrd l v) = 0 ∨ l < finitePart (keyOrd l v) := by
  unfold keyOrd; split_ifs with h
  · exact Or.inl (finitePart_limitPart v)
  · exact Or.inr (not_le.mp h)

/-- The key set of the row. -/
def keys : Finset Ordinal.{0} := S.image (keyOrd l)

/-- The block of a key: the number of keys at most it. -/
def blockOfKey (κ : Ordinal.{0}) : ℕ := ((keys l S).filter fun κ' => κ' ≤ κ).card

/-- The block of a value. -/
def blockOf (v : Ordinal.{0}) : ℕ := blockOfKey l S (keyOrd l v)

theorem blockOfKey_le (κ : Ordinal.{0}) : blockOfKey l S κ ≤ (keys l S).card :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem blockOfKey_mono {κ κ' : Ordinal.{0}} (h : κ ≤ κ') : blockOfKey l S κ ≤ blockOfKey l S κ' :=
  Finset.card_le_card fun _ hx =>
    Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2.trans h⟩

theorem blockOfKey_lt {κ κ' : Ordinal.{0}} (hκ' : κ' ∈ keys l S) (h : κ < κ') :
    blockOfKey l S κ < blockOfKey l S κ' :=
  Finset.card_lt_card ⟨fun _ hx => Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2.trans h.le⟩,
    fun hsub => h.not_ge (Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨hκ', le_rfl⟩))).2⟩

theorem blockOfKey_pos {κ : Ordinal.{0}} (hκ : κ ∈ keys l S) : 0 < blockOfKey l S κ :=
  Finset.card_pos.mpr ⟨κ, Finset.mem_filter.mpr ⟨hκ, le_rfl⟩⟩

theorem keyOrd_mem_keys {v : Ordinal.{0}} (hv : v ∈ S) : keyOrd l v ∈ keys l S :=
  Finset.mem_image.mpr ⟨v, hv, rfl⟩

/-- **The code** of a value: `ω·block + min (fp v) l`. -/
def code (v : Ordinal.{0}) : Ordinal.{0} :=
  Ordinal.omega0 * (blockOf l S v : ℕ) + (min (finitePart v) l : ℕ)

theorem code_isCoded (v : Ordinal.{0}) : IsCodedLabel l (ofOrd (code l S v)) :=
  Or.inr ⟨blockOf l S v, min (finitePart v) l, by omega, rfl⟩

theorem code_selfVis {v : Ordinal.{0}} {a : ℕ} (ha : a ≤ finitePart v) (hal : a ≤ l) :
    SelfVis a (ofOrd (code l S v)) := by
  rw [selfVis_ofOrd_iff, code, finitePart_mul_add]
  exact le_min ha hal

/-- The cap code: one block past every key, finite part `l`. -/
def capCode : Ordinal.{0} := Ordinal.omega0 * (((keys l S).card + 1 : ℕ) : Ordinal) + l

theorem capCode_selfVis : SelfVis l (ofOrd (capCode l S)) := by
  rw [selfVis_ofOrd_iff, capCode, finitePart_mul_add]

theorem capCode_isCoded : IsCodedLabel l (ofOrd (capCode l S)) :=
  Or.inr ⟨(keys l S).card + 1, l, by omega, rfl⟩

theorem code_le_capCode (v : Ordinal.{0}) : code l S v ≤ capCode l S :=
  code_le_code (Nat.cast_le.mpr (by have := blockOfKey_le l S (keyOrd l v); unfold blockOf; omega))
    (min_le_right _ _)

/-! ## The decoder -/

/-- The key hosted on block `t`: the largest key with block `≤ t` (`⊥` if none). -/
def keyAt (t : Ordinal.{0}) : WithBot Ordinal.{0} :=
  ((keys l S).filter fun κ => ((blockOfKey l S κ : ℕ) : Ordinal) ≤ t).max

/-- Decoding on the block of a key `κ` at finite offset `j`. -/
def decodeIn (κ : Ordinal.{0}) (j : ℕ) : Ordinal.{0} :=
  if finitePart κ = 0 then κ + (min j l : ℕ) else κ

/-- **The decoder.** -/
def shift : ExtOrd → ExtOrd
  | ⊥ => ⊥
  | some ⊤ => γ
  | some (some α) =>
      if (((keys l S).card + 1 : ℕ) : Ordinal) ≤ blockIdx α then γ
      else match keyAt l S (blockIdx α) with
        | ⊥ => ⊥
        | some κ => ofOrd (decodeIn l κ (finitePart α))

theorem shift_bot : shift l S γ ⊥ = ⊥ := rfl
theorem shift_top : shift l S γ ⊤ = γ := rfl
theorem shift_ofOrd (α : Ordinal.{0}) :
    shift l S γ (ofOrd α) =
      if (((keys l S).card + 1 : ℕ) : Ordinal) ≤ blockIdx α then γ
      else match keyAt l S (blockIdx α) with
        | ⊥ => ⊥
        | some κ => ofOrd (decodeIn l κ (finitePart α)) := rfl

theorem keyAt_eq_of_mem {κ : Ordinal.{0}} (hκ : κ ∈ keys l S) :
    keyAt l S (blockOfKey l S κ) = some κ := by
  refine le_antisymm (Finset.max_le fun κ' hκ' => ?_)
    (Finset.le_max (Finset.mem_filter.mpr ⟨hκ, le_rfl⟩))
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hκ'
  exact WithBot.coe_le_coe.mpr (not_lt.mp fun hlt =>
    not_lt_of_ge (Nat.cast_le.mp h2) (blockOfKey_lt l S h1 hlt))

theorem keyAt_zero : keyAt l S 0 = ⊥ :=
  Finset.max_eq_bot.mpr (Finset.filter_eq_empty_iff.mpr fun _ hκ h =>
    (Nat.cast_lt.mpr (blockOfKey_pos l S hκ)).not_ge h)

/-- **Exact decoding**: the code of a member of `S` decodes to it. -/
theorem shift_code {v : Ordinal.{0}} (hv : v ∈ S) : shift l S γ (ofOrd (code l S v)) = ofOrd v := by
  rw [shift_ofOrd, code, blockIdx_mul_add, finitePart_mul_add, blockOf,
    ite_eq_right (not_le.mpr (Nat.cast_lt.mpr (Nat.lt_succ_of_le (blockOfKey_le l S (keyOrd l v))))),
    keyAt_eq_of_mem l S (keyOrd_mem_keys l S hv)]
  dsimp only [decodeIn, keyOrd]
  split_ifs with hfp h0 h0
  · rw [min_eq_left hfp, min_eq_left hfp, limitPart_add_finitePart]
  · exact absurd (finitePart_limitPart v) h0
  · omega
  · rfl

/-- **Cap decoding**: the cap code decodes to `γ`. -/
theorem shift_capCode : shift l S γ (ofOrd (capCode l S)) = γ := by
  rw [shift_ofOrd, capCode, blockIdx_mul_add, ite_eq_left le_rfl]

/-! ### Monotonicity -/

/-- The values decoded on the block of a key `κ` lie in `[κ, κ + l]`. -/
theorem decodeIn_ge (κ : Ordinal.{0}) (j : ℕ) : κ ≤ decodeIn l κ j := by
  unfold decodeIn; split_ifs; exacts [le_self_add, le_rfl]

theorem decodeIn_le (κ : Ordinal.{0}) (j : ℕ) : decodeIn l κ j ≤ κ + l := by
  unfold decodeIn; split_ifs
  · exact add_le_add le_rfl (Nat.cast_le.mpr (min_le_right _ _))
  · exact le_self_add

theorem decodeIn_mono (κ : Ordinal.{0}) {j j' : ℕ} (h : j ≤ j') :
    decodeIn l κ j ≤ decodeIn l κ j' := by
  unfold decodeIn; split_ifs
  · exact add_le_add le_rfl (Nat.cast_le.mpr (min_le_min_right l h))
  · exact le_rfl

/-- **A key's block never reaches the next key**: for keys `κ < κ'`, `κ + l ≤ κ'`. -/
theorem key_add_le_next {κ κ' : Ordinal.{0}} (hκ : κ ∈ keys l S) (hκ' : κ' ∈ keys l S)
    (h : κ < κ') (h0 : finitePart κ = 0) : κ + l ≤ κ' := by
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hκ
  obtain ⟨v', -, rfl⟩ := Finset.mem_image.mp hκ'
  have e1 := (eq_limitPart_of_finitePart_eq_zero h0).symm
  rcases lt_or_ge (limitPart (keyOrd l v)) (limitPart (keyOrd l v')) with hlt | hge
  · exact e1 ▸ (limitPart_add_nat_le_of_lt hlt l).trans (limitPart_le _)
  · have heq : limitPart (keyOrd l v) = limitPart (keyOrd l v') :=
      le_antisymm (limitPart_mono h.le) hge
    rcases finitePart_keyOrd l v' with h0' | hl'
    · exact absurd (e1.trans (heq.trans (eq_limitPart_of_finitePart_eq_zero h0'))) h.ne
    · rw [e1, heq]
      conv_rhs => rw [← limitPart_add_finitePart (keyOrd l v')]
      exact add_le_add le_rfl (Nat.cast_le.mpr hl'.le)

theorem keyAt_mem {t : Ordinal.{0}} {κ : Ordinal.{0}} (h : keyAt l S t = some κ) : κ ∈ keys l S :=
  (Finset.mem_filter.mp (Finset.mem_of_max h)).1

/-- Below a cap `γ` self-visible at `l` that dominates the values, the key-block values
`κ + l` stay below `γ`. -/
theorem key_add_l_le {v : Ordinal.{0}} {g : Ordinal.{0}} (hv : v ≤ g) (hg : l ≤ finitePart g)
    (h0 : finitePart (keyOrd l v) = 0) : keyOrd l v + l ≤ g := by
  rw [← eq_limitPart_of_finitePart_eq_zero h0, limitPart_keyOrd]
  rcases lt_or_ge (limitPart v) (limitPart g) with hlt | hge
  · exact (limitPart_add_nat_le_of_lt hlt l).trans (limitPart_le g)
  · rw [le_antisymm (limitPart_mono hv) hge]
    conv_rhs => rw [← limitPart_add_finitePart g]
    exact add_le_add le_rfl (Nat.cast_le.mpr hg)

theorem decodeIn_le_of_key {v : Ordinal.{0}} {g : Ordinal.{0}} (hv : v ≤ g)
    (hg : l ≤ finitePart g) (j : ℕ) : decodeIn l (keyOrd l v) j ≤ g := by
  unfold decodeIn
  split_ifs with h0
  · exact (add_le_add le_rfl (Nat.cast_le.mpr (min_le_right j l))).trans (key_add_l_le l hv hg h0)
  · exact (keyOrd_le l v).trans hv

theorem shift_ofOrd_le_γ (hγ : SelfVis l γ) (hS : ∀ v ∈ S, ofOrd v ≤ γ) (α : Ordinal.{0}) :
    shift l S γ (ofOrd α) ≤ γ := by
  rw [shift_ofOrd]
  split_ifs with h
  · exact le_rfl
  · rcases hk : keyAt l S (blockIdx α) with _ | κ
    · exact bot_le
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (keyAt_mem l S hk)
      have hvγ := hS v hv
      rcases ExtOrd.cases γ with rfl | rfl | ⟨g, rfl⟩
      · exact absurd hvγ (not_ofOrd_le_bot v)
      · exact le_top
      · exact ofOrd_le_ofOrd.mpr (decodeIn_le_of_key l (ofOrd_le_ofOrd.mp hvγ)
          (selfVis_ofOrd_iff.mp hγ) _)

/-! ### The block-key bijection -/

theorem blockOfKey_injOn : Set.InjOn (blockOfKey l S) (keys l S) := fun _ hκ _ hκ' h =>
  by_contra fun hne => (lt_or_gt_of_ne hne).elim
    (fun hlt => (blockOfKey_lt l S hκ' hlt).ne h)
    (fun hgt => (blockOfKey_lt l S hκ hgt).ne' h)

theorem blockOfKey_mem_Icc {κ : Ordinal.{0}} (hκ : κ ∈ keys l S) :
    blockOfKey l S κ ∈ Finset.Icc 1 (keys l S).card :=
  Finset.mem_Icc.mpr ⟨blockOfKey_pos l S hκ, blockOfKey_le l S κ⟩

/-- Every block `1 … |keys|` is the block of exactly one key. -/
theorem exists_key_of_block {n : ℕ} (h1 : 1 ≤ n) (hn : n ≤ (keys l S).card) :
    ∃ κ ∈ keys l S, blockOfKey l S κ = n := by
  have himg : (keys l S).image (blockOfKey l S) = Finset.Icc 1 (keys l S).card := by
    refine Finset.eq_of_subset_of_card_le (fun b hb => ?_) ?_
    · obtain ⟨κ, hκ, rfl⟩ := Finset.mem_image.mp hb; exact blockOfKey_mem_Icc l S hκ
    · rw [Finset.card_image_of_injOn (blockOfKey_injOn l S), Nat.card_Icc]; omega
  exact Finset.mem_image.mp (himg ▸ Finset.mem_Icc.mpr ⟨h1, hn⟩)

theorem keyAt_nat_eq_some {t : ℕ} (h1 : 1 ≤ t) (ht : t ≤ (keys l S).card) :
    ∃ κ ∈ keys l S, keyAt l S t = some κ ∧ blockOfKey l S κ = t := by
  obtain ⟨κ, hκ, hb⟩ := exists_key_of_block l S h1 ht
  exact ⟨κ, hκ, hb ▸ keyAt_eq_of_mem l S hκ, hb⟩

/-- Block indices below `|keys| + 1` are naturals. -/
theorem exists_nat_of_lt_card {t : Ordinal.{0}} (h : t < (((keys l S).card + 1 : ℕ) : Ordinal)) :
    ∃ n : ℕ, t = n ∧ n ≤ (keys l S).card := by
  obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp (h.trans_le (Ordinal.natCast_lt_omega0 _).le)
  exact ⟨n, rfl, Nat.lt_succ_iff.mp (Nat.cast_lt.mp h)⟩

/-! ### Monotonicity -/

theorem finitePart_le_of_le_of_limitPart_eq {α β : Ordinal.{0}} (h : α ≤ β)
    (hl : limitPart α = limitPart β) : finitePart α ≤ finitePart β :=
  finitePart_le_of_le hl h

theorem shift_mono (hγ : SelfVis l γ) (hS : ∀ v ∈ S, ofOrd v ≤ γ) : Monotone (shift l S γ) := by
  intro x y hxy
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · exact bot_le
  · rw [top_le_iff.mp hxy]
  · rcases ExtOrd.cases y with rfl | rfl | ⟨β, rfl⟩
    · exact absurd hxy (not_ofOrd_le_bot α)
    · exact shift_ofOrd_le_γ l S γ hγ hS α
    · have hαβ := ofOrd_le_ofOrd.mp hxy
      have hb := blockIdx_mono hαβ
      by_cases h2 : (((keys l S).card + 1 : ℕ) : Ordinal) ≤ blockIdx β
      · rw [shift_ofOrd (α := β), ite_eq_left h2]
        exact shift_ofOrd_le_γ l S γ hγ hS α
      · have h1 : ¬ (((keys l S).card + 1 : ℕ) : Ordinal) ≤ blockIdx α :=
          fun h => h2 (h.trans hb)
        rw [shift_ofOrd, shift_ofOrd, ite_eq_right h1, ite_eq_right h2]
        obtain ⟨n, hn, hnle⟩ := exists_nat_of_lt_card l S (not_le.mp h1)
        obtain ⟨m, hm, hmle⟩ := exists_nat_of_lt_card l S (not_le.mp h2)
        rw [hn, hm] at hb ⊢
        have hnm : n ≤ m := Nat.cast_le.mp hb
        rcases Nat.eq_zero_or_pos n with rfl | hnpos
        · rw [Nat.cast_zero, keyAt_zero]; exact bot_le
        · obtain ⟨κ, hκ, hk, hbκ⟩ := keyAt_nat_eq_some l S hnpos hnle
          obtain ⟨κ', hκ', hk', hbκ'⟩ := keyAt_nat_eq_some l S (hnpos.trans_le hnm) hmle
          rw [hk, hk']
          dsimp only
          rw [ofOrd_le_ofOrd]
          rcases Nat.eq_or_lt_of_le hnm with rfl | hlt
          · cases blockOfKey_injOn l S hκ hκ' (hbκ.trans hbκ'.symm)
            exact decodeIn_mono l κ (finitePart_le_of_le
              (by rw [limitPart_eq_mul_blockIdx, limitPart_eq_mul_blockIdx, hn, hm]) hαβ)
          · have hκlt : κ < κ' := not_le.mp fun hge => by
              have := blockOfKey_mono l S hge; omega
            rcases Nat.eq_zero_or_pos (finitePart κ) with h0 | hpos
            · exact (decodeIn_le l κ _).trans
                ((key_add_le_next l S hκ hκ' hκlt h0).trans (decodeIn_ge l κ' _))
            · rw [decodeIn, ite_eq_right (by omega)]
              exact hκlt.le.trans (decodeIn_ge l κ' _)

/-! ### Clause 5 -/

theorem key_finitePart {κ : Ordinal.{0}} (hκ : κ ∈ keys l S) : finitePart κ = 0 ∨ l < finitePart κ := by
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hκ
  exact finitePart_keyOrd l v

/-- **Clause 5 below the target grade, unguarded**: for `k ≤ l`, the decoder commutes with
visibility replacement at threshold `k`. -/
theorem shift_evr_of_le (hγ : SelfVis l γ) {k : ℕ} (hk : k ≤ l) (x : ExtOrd) {i : ℕ} (hi : i ≤ k) :
    shift l S γ (extVisibilityReplace x k i) = extVisibilityReplace (shift l S γ x) k i := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · rfl
  · exact (evr_eq_self_of_selfVis (hγ.mono hk) i).symm
  · rw [extVisibilityReplace_ofOrd, shift_ofOrd, shift_ofOrd, blockIdx_visibilityReplace]
    split_ifs with h
    · exact (evr_eq_self_of_selfVis (hγ.mono hk) i).symm
    · rcases hkA : keyAt l S (blockIdx α) with _ | κ
      · rfl
      · dsimp only
        rw [extVisibilityReplace_ofOrd, ofOrd_inj, finitePart_visibilityReplace]
        rcases key_finitePart l S (keyAt_mem l S hkA) with h0 | hl
        · obtain ⟨μ, rfl⟩ : ∃ μ, κ = Ordinal.omega0 * μ :=
            ⟨blockIdx κ, (eq_limitPart_of_finitePart_eq_zero h0).symm⟩
          unfold decodeIn visibilityReplace ordinalReplace
          rw [ite_eq_left (finitePart_omega0_mul μ), ite_eq_left (finitePart_omega0_mul μ),
            finitePart_code, limitPart_code]
          split_ifs with hfp hlt hlt
          · rw [min_eq_left (hi.trans hk)]
          · exact absurd (lt_of_le_of_lt (min_le_left _ _) hfp) hlt
          · omega
          · rfl
        · unfold decodeIn
          rw [ite_eq_right (by omega), ite_eq_right (by omega), visibilityReplace, ite_eq_right (by omega)]

/-- **Clause 5 above the target grade**: a `⊥` value stays `⊥` under replacement. -/
theorem shift_evr_of_bot (x : ExtOrd) (k i : ℕ) (h : shift l S γ x = ⊥) :
    shift l S γ (extVisibilityReplace x k i) = ⊥ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · rfl
  · exact h
  · rw [extVisibilityReplace_ofOrd, shift_ofOrd, blockIdx_visibilityReplace]
    rw [shift_ofOrd] at h
    split_ifs at h ⊢
    · exact h
    · rcases hkA : keyAt l S (blockIdx α) with _ | κ
      · rfl
      · rw [hkA] at h; exact absurd h (ofOrd_ne_bot _)

/-- **The packaged transformation witness**: any row `G` transforms to its decoding capped at a
self-visible `ρ` up to grade `l`. -/
theorem transformsTo_of_shift {D : Type*} (grade : D → ℕ) (hγ : SelfVis l γ)
    (hS : ∀ v ∈ S, ofOrd v ≤ γ) (G : D → ExtOrd) {ρ : ExtOrd} (hρ : SelfVis l ρ) :
    TransformsTo grade G (fun d => min (shift l S γ (G d)) (if grade d ≤ l then ρ else ⊥)) := by
  refine ⟨fun k => if k ≤ l then ρ else ⊥, shift l S γ, ?_, ?_, rfl,
    shift_mono l S γ hγ hS, ?_, fun _ => rfl⟩
  · intro a b hab; dsimp only; split_ifs <;> first | exact le_rfl | exact bot_le | omega
  · intro n; dsimp only; split_ifs with h; exacts [(hρ.mono h).symm, rfl]
  · intro α k hle i hi
    by_cases hk : k ≤ l
    · exact shift_evr_of_le l S γ hγ hk α hi
    · dsimp only at hle
      rw [ite_eq_right hk] at hle
      have h0 : shift l S γ α = ⊥ := le_bot_iff.mp hle
      rw [shift_evr_of_bot l S γ α k i h0, h0, extVisibilityReplace_bot]
