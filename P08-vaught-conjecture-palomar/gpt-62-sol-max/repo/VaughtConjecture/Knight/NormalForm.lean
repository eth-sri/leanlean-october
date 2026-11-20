/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Order.Interval.Finset.Fin
public import VaughtConjecture.Knight.SemScheme
public import VaughtConjecture.Knight.WitnessAlgebra

@[expose] public section

namespace VaughtConjecture.Knight

open Value ExtOrd

namespace Value

/-- The limit part of a natural number is zero. -/
theorem limitPart_natCast (n : ℕ) : limitPart (n : Ordinal.{0}) = 0 := by
  unfold limitPart
  rw [Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 n), mul_zero]

/-- `ω * u` is its own limit part. -/
theorem limitPart_omega0_mul (u : Ordinal.{0}) :
    limitPart (Ordinal.omega0 * u) = Ordinal.omega0 * u := by
  unfold limitPart
  rw [Ordinal.mul_div_cancel u Ordinal.omega0_ne_zero]

/-- The limit part of the code `ω * u + m` is `ω * u`. -/
theorem limitPart_code (u : Ordinal.{0}) (m : ℕ) :
    limitPart (Ordinal.omega0 * u + m) = Ordinal.omega0 * u := by
  conv_lhs => rw [← limitPart_omega0_mul u]
  rw [limitPart_limitPart_add_nat, limitPart_omega0_mul]

/-- The finite part of the code `ω * u + m` is `m`. -/
theorem finitePart_code (u : Ordinal.{0}) (m : ℕ) :
    finitePart (Ordinal.omega0 * u + m) = m := by
  conv_lhs => rw [← limitPart_omega0_mul u]
  rw [finitePart_limitPart_add_nat]

/-- An ordinal with finite part `0` is its own limit part. -/
theorem eq_limitPart_of_finitePart_eq_zero {β : Ordinal.{0}} (h : finitePart β = 0) :
    limitPart β = β := by
  have := decomposition β
  rwa [h, Nat.cast_zero, add_zero] at this

/-- A block member `x` lies below the next block level: `x < limitPart x + ω`. -/
theorem lt_limitPart_add_omega0 (x : Ordinal.{0}) : x < limitPart x + Ordinal.omega0 := by
  conv_lhs => rw [← decomposition x]
  exact add_lt_add_right (Ordinal.natCast_lt_omega0 _) _

/-- Distinct limit parts are at least a block apart:
if `limitPart x < limitPart y` then `limitPart x + ω ≤ limitPart y`. -/
theorem limitPart_add_omega0_le {x y : Ordinal.{0}} (h : limitPart x < limitPart y) :
    limitPart x + Ordinal.omega0 ≤ limitPart y := by
  unfold limitPart at *
  have hdiv : x / Ordinal.omega0 < y / Ordinal.omega0 :=
    (Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono.lt_iff_lt.mp h
  calc Ordinal.omega0 * (x / Ordinal.omega0) + Ordinal.omega0
      = Ordinal.omega0 * Order.succ (x / Ordinal.omega0) := (Ordinal.mul_succ _ _).symm
    _ ≤ Ordinal.omega0 * (y / Ordinal.omega0) :=
        (Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono.monotone
          (Order.succ_le_of_lt hdiv)

/-- Strict block comparison: a member of an earlier block is below every member of a later
block. -/
theorem lt_of_limitPart_lt {x y : Ordinal.{0}} (h : limitPart x < limitPart y) : x < y :=
  lt_of_lt_of_le ((lt_limitPart_add_omega0 x).trans_le (limitPart_add_omega0_le h))
    ((limitPart_le y).trans le_rfl)

/-- Code comparison, strict, across blocks: `ω·u + m < ω·v + n` when `u < v`. -/
theorem code_lt_code_of_lt {u v : Ordinal.{0}} (h : u < v) (m n : ℕ) :
    Ordinal.omega0 * u + m < Ordinal.omega0 * v + n := by
  apply lt_of_limitPart_lt
  rw [limitPart_code, limitPart_code]
  exact (Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono h

/-- Code comparison, non-strict: `ω·u + m ≤ ω·v + n` when `u ≤ v` and `m ≤ n`. -/
theorem code_le_code {u v : Ordinal.{0}} (h : u ≤ v) {m n : ℕ} (hmn : m ≤ n) :
    Ordinal.omega0 * u + m ≤ Ordinal.omega0 * v + n :=
  add_le_add ((Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono.monotone h)
    (Nat.cast_le.mpr hmn : ((m : ℕ) : Ordinal) ≤ _)

end Value

/-- Every finite offset in an earlier block is below the next block. -/
theorem limitPart_add_nat_le_of_lt {a b : Ordinal.{0}} (h : limitPart a < limitPart b) (j : ℕ) :
    limitPart a + j ≤ limitPart b :=
  (add_lt_add_right (Ordinal.natCast_lt_omega0 j) _).le.trans (limitPart_add_omega0_le h)

namespace Transform

/-- A **`K`-step shifter** (the legality pattern of the note's §3, shared by the canonical
normalizer and decoder): a label map `σ` that fixes `⊥`, is monotone, preserves
self-visibility at every threshold `≤ K`, is **affine or constant on the sub-`K` part of
every ω-block** (affine onto a block start `β`, or constant at a label self-visible at `K`),
and whose **`⊥`-fiber is closed under whole blocks**.  These five conditions make `(g_K, σ)`
a legal Def. 2.3.9 witness pair (`IsStepShifter.clause5`, `IsStepShifter.transformsTo`). -/
structure IsStepShifter (K : ℕ) (σ : ExtOrd → ExtOrd) : Prop where
  /-- `σ` fixes the bottom label (clause 3). -/
  map_bot : σ ⊥ = ⊥
  /-- `σ` is monotone (clause 4). -/
  mono : Monotone σ
  /-- `σ` preserves self-visibility at every threshold `≤ K`. -/
  selfVis : ∀ (x : ExtOrd) (k : ℕ), k ≤ K → extVisibilityReplace x k k = x →
    extVisibilityReplace (σ x) k k = σ x
  /-- On the sub-`K` part `{limitPart ξ + i : i ≤ K}` of every block, `σ` is affine onto a
  block start (`finitePart β = 0`) or constant at a label self-visible at `K`. -/
  blockwise : ∀ ξ : Ordinal.{0},
    (∃ β : Ordinal.{0}, finitePart β = 0 ∧
      ∀ i : ℕ, i ≤ K → σ (ofOrd (limitPart ξ + i)) = ofOrd (β + i)) ∨
    (∃ c : ExtOrd, extVisibilityReplace c K K = c ∧
      ∀ i : ℕ, i ≤ K → σ (ofOrd (limitPart ξ + i)) = c)
  /-- The `⊥`-fiber of `σ` on ordinals is a union of whole blocks. -/
  bot_blocks : ∀ ξ ζ : Ordinal.{0}, limitPart ξ = limitPart ζ →
    σ (ofOrd ξ) = ⊥ → σ (ofOrd ζ) = ⊥

/-- **The clause-5 case split, compiled once** (note §3): a `K`-step shifter satisfies
clause 5 of Def. 2.3.9 for the step suppressor `g_K`.  For `k ≤ K` the commutation is
**unguarded**: on self-visible labels both sides are fixed (self-visibility is preserved);
on the sub-`K` part of a block, affine pieces commute with `⊔⁺_k i` and constants are
`⊔⁺_k`-fixed.  For `k > K` the guard `σ α ≤ g_K k = ⊥` pins `σ α = ⊥`, and the
`⊔⁺_k`-orbit of `α` stays in `α`'s block, hence in the `⊥`-fiber (block closure). -/
theorem IsStepShifter.clause5 {K : ℕ} {σ : ExtOrd → ExtOrd} (h : IsStepShifter K σ) :
    ∀ (α : ExtOrd) (k : ℕ), σ α ≤ gTop K k → ∀ i : ℕ, i ≤ k →
      σ (extVisibilityReplace α k i) = extVisibilityReplace (σ α) k i := by
  intro α k hguard i hi
  by_cases hk : k ≤ K
  · -- thresholds `k ≤ K`: unguarded commutation
    rcases ExtOrd.cases α with rfl | rfl | ⟨ξ, rfl⟩
    · rw [extVisibilityReplace_bot, h.map_bot, extVisibilityReplace_bot]
    · rw [extVisibilityReplace_top,
        evr_eq_self_of_selfVis (h.selfVis ⊤ k hk (extVisibilityReplace_top k k)) i]
    · by_cases hfp : k ≤ finitePart ξ
      · -- self-visible at `k`: both sides fixed
        have hself : extVisibilityReplace (ofOrd ξ) k k = ofOrd ξ :=
          (extVisibilityReplace_self_iff _ k).mpr (Or.inr (Or.inr ⟨ξ, rfl, hfp⟩))
        rw [evr_eq_self_of_selfVis hself i,
          evr_eq_self_of_selfVis (h.selfVis _ k hk hself) i]
      · -- inside the sub-`K` part of the block: affine or constant
        rw [not_le] at hfp
        have hrepl : extVisibilityReplace (ofOrd ξ) k i = ofOrd (limitPart ξ + i) := by
          rw [extVisibilityReplace_ofOrd, visibilityReplace, ite_eq_left hfp]; rfl
        have hξ : ofOrd ξ = ofOrd (limitPart ξ + (finitePart ξ : ℕ)) := by
          rw [decomposition]
        rcases h.blockwise ξ with ⟨β, hβ0, haff⟩ | ⟨c, hcvis, hconst⟩
        · have hβ : limitPart β = β := eq_limitPart_of_finitePart_eq_zero hβ0
          rw [hrepl, haff i (hi.trans hk), hξ, haff (finitePart ξ) ((hfp.le).trans hk),
            extVisibilityReplace_ofOrd, visibilityReplace,
            ite_eq_left (by rw [← hβ, finitePart_limitPart_add_nat]; exact hfp),
            ordinalReplace, ← hβ, limitPart_limitPart_add_nat, hβ]
        · rw [hrepl, hconst i (hi.trans hk), hξ, hconst (finitePart ξ) ((hfp.le).trans hk),
            evr_eq_self_of_selfVis
              (extVisReplace_self_of_le hcvis hk) i]
  · -- thresholds `k > K`: the guard pins `σ α = ⊥`; block closure of the `⊥`-fiber
    rw [gTop_of_gt (not_le.mp hk)] at hguard
    have hbot : σ α = ⊥ := le_bot_iff.mp hguard
    rw [hbot, extVisibilityReplace_bot]
    rcases ExtOrd.cases α with rfl | rfl | ⟨ξ, rfl⟩
    · rw [extVisibilityReplace_bot, h.map_bot]
    · rw [extVisibilityReplace_top, hbot]
    · rw [extVisibilityReplace_ofOrd]
      unfold visibilityReplace
      split_ifs with hfp
      · exact h.bot_blocks ξ _ (limitPart_limitPart_add_nat ξ i).symm hbot
      · exact hbot

theorem IsStepShifter.normalizedWitness {K : ℕ} {σ : ExtOrd → ExtOrd} (h : IsStepShifter K σ) :
    Witness (gTop K) σ := ⟨(witness_id K).anti, (witness_id K).vis, h.map_bot, h.mono, h.clause5⟩

theorem IsStepShifter.transformsTo {D : Type*} {grade : D → ℕ} {K : ℕ} {σ : ExtOrd → ExtOrd}
    (h : IsStepShifter K σ) (hK : ∀ d, grade d ≤ K) (p : D → ExtOrd) :
    TransformsTo grade p (fun d => σ (p d)) :=
  h.normalizedWitness.transformsTo_top hK (fun _ => rfl)

end Transform

open Transform

/-- **Corollary 2.B** (note §2; the faithful Lemma 2.5.8): if `r` respects the restricted
semantics `E⟨B,j⟩` and `γ` is self-visible at `j`, then the capped labelling `r ∧ γ`
respects it too.  Locality is the Cap Lemma applied to `r`'s locality (all grades below the
pair are `≤ j` by `GradedLe`); availability is monotonicity of `min (·, γ)`; orderliness is
preservation of self-visibility under `min` with heredity of `γ`'s self-visibility. -/
theorem RespectsSemanticsBelow.cap {ι : Type*} [DecidableEq ι] {A : Finset ι}
    {D : CellScheme A} {sem : Semantics D} {BJ : Finset ι × ℕ} {r : D.below BJ → ExtOrd}
    (h : RespectsSemanticsBelow sem BJ r) {γ : ExtOrd}
    (hγ : extVisibilityReplace γ BJ.2 BJ.2 = γ) :
    RespectsSemanticsBelow sem BJ (fun d => min (r d) γ) where
  orderly d := (selfVis_min (h.orderly d).symm (selfVis_mono hγ d.2.2)).symm
  locality Sig := by
    conv => arg 3; ext d; rw [min_min_min_comm, min_self]
    exact TransformsTo.cap (h.locality Sig) (fun d => (d.2.trans Sig.2).2) hγ
  availability Sig Xi₀ hscope hgrade := by
    obtain ⟨Xi, hcell, hle⟩ := h.availability Sig Xi₀ hscope hgrade
    exact ⟨Xi, hcell, min_le_min hle le_rfl⟩

namespace Value

/-- The limit part has finite part `0`. -/
theorem finitePart_limitPart (x : Ordinal.{0}) : finitePart (limitPart x) = 0 := by
  have h := finitePart_limitPart_add_nat x 0
  rwa [Nat.cast_zero, add_zero] at h

/-- The limit part is idempotent. -/
theorem limitPart_idem (x : Ordinal.{0}) : limitPart (limitPart x) = limitPart x :=
  eq_limitPart_of_finitePart_eq_zero (finitePart_limitPart x)

/-- `ω * u` has finite part `0`. -/
theorem finitePart_omega0_mul (u : Ordinal.{0}) :
    finitePart (Ordinal.omega0 * u) = 0 := by
  conv_lhs => rw [← limitPart_omega0_mul u]
  exact finitePart_limitPart _

/-- Adding a natural number is inflationary. -/
theorem self_le_add_nat (x : Ordinal.{0}) (i : ℕ) : x ≤ x + i := by
  conv_lhs => rw [← add_zero x]
  exact add_le_add_right (by exact_mod_cast Nat.zero_le i) _

/-- A code with a smaller block index is below the larger block level: `ω·u + m < ω·v` for
`u < v`. -/
theorem code_add_lt_mul {u v : Ordinal.{0}} (h : u < v) (m : ℕ) :
    Ordinal.omega0 * u + m < Ordinal.omega0 * v :=
  calc Ordinal.omega0 * u + (m : Ordinal.{0})
      < Ordinal.omega0 * u + Ordinal.omega0 :=
        add_lt_add_right (Ordinal.natCast_lt_omega0 m) _
    _ = Ordinal.omega0 * Order.succ u := (Ordinal.mul_succ _ _).symm
    _ ≤ Ordinal.omega0 * v :=
        (Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono.monotone
          (Order.succ_le_of_lt h)

/-- Within a block, order is finite-part order. -/
theorem finitePart_le_of_le {x y : Ordinal.{0}} (hlim : limitPart x = limitPart y)
    (hxy : x ≤ y) : finitePart x ≤ finitePart y := by
  have h1 : limitPart y + (finitePart x : Ordinal) = x := by rw [← hlim]; exact decomposition x
  have h2 : limitPart y + (finitePart y : Ordinal) = y := decomposition y
  have h3 : limitPart y + (finitePart x : Ordinal) ≤ limitPart y + (finitePart y : Ordinal) := by
    rw [h1, h2]; exact hxy
  exact_mod_cast (add_le_add_iff_left (limitPart y)).mp h3

/-- An ordinal in the half-open block `[limitPart x, limitPart x + ω)` has limit part
`limitPart x`. -/
theorem limitPart_eq_of_mem_block {x q : Ordinal.{0}} (h1 : limitPart x ≤ q)
    (h2 : q < limitPart x + Ordinal.omega0) : limitPart q = limitPart x := by
  refine le_antisymm ?_ ?_
  · by_contra hlt
    rw [not_le] at hlt
    exact absurd ((limitPart_add_omega0_le hlt).trans (limitPart_le q)) (not_le.mpr h2)
  · calc limitPart x = limitPart (limitPart x) := (limitPart_idem x).symm
      _ ≤ limitPart q := limitPart_mono h1

end Value

namespace Transform

/-- The **items** of the canonical alphabet `ν_{S,K}` (note §3), a finite set of ordinals in
increasing order: for each block meeting `S` at finite parts `≤ K`, an *interval item* at the
block start (the image of `limitPart`); for each `s ∈ S` with finite part `≥ K+1`, a
*singleton item* at `s`.  (The top label `⊤` is always tracked separately, by the extra block
`(items S K).card`; see `canonicalNormalizer`.) -/
noncomputable def items (S : Finset Ordinal.{0}) (K : ℕ) : Finset Ordinal.{0} :=
  S.image (fun a => if finitePart a ≤ K then limitPart a else a)

variable {S : Finset Ordinal.{0}} {K : ℕ}

theorem limitPart_mem_items {s : Ordinal.{0}} (hs : s ∈ S) (hfp : finitePart s ≤ K) :
    limitPart s ∈ items S K := Finset.mem_image.mpr ⟨s, hs, if_pos hfp⟩

theorem mem_items_of_high {s : Ordinal.{0}} (hs : s ∈ S) (hfp : K + 1 ≤ finitePart s) :
    s ∈ items S K := Finset.mem_image.mpr ⟨s, hs, if_neg (by omega)⟩

theorem items_fp {p : Ordinal.{0}} (hp : p ∈ items S K) :
    finitePart p = 0 ∨ K + 1 ≤ finitePart p := by
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
  split_ifs
  · exact Or.inl (finitePart_limitPart a)
  · omega

theorem items_card_le : (items S K).card ≤ S.card := Finset.card_image_le

/-- The **rank** of `x`: the number of items `≤ x`. -/
noncomputable def rank (S : Finset Ordinal.{0}) (K : ℕ) (x : Ordinal.{0}) : ℕ :=
  ((items S K).filter fun p => p ≤ x).card

theorem rank_mono {x y : Ordinal.{0}} (hxy : x ≤ y) : rank S K x ≤ rank S K y :=
  Finset.card_le_card fun _q hq => Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hq).1, le_trans (Finset.mem_filter.mp hq).2 hxy⟩

theorem rank_le_card (x : Ordinal.{0}) : rank S K x ≤ (items S K).card :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem rank_eq_zero_iff {x : Ordinal.{0}} :
    rank S K x = 0 ↔ ∀ p ∈ items S K, ¬ p ≤ x := by
  rw [rank, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

theorem rank_pos_of_item {p x : Ordinal.{0}} (hp : p ∈ items S K) (hpx : p ≤ x) :
    1 ≤ rank S K x :=
  Nat.one_le_iff_ne_zero.mpr fun h => (rank_eq_zero_iff.mp h) p hp hpx

/-- Ranks agree when no item separates `x` from `y`. -/
theorem rank_eq_of_forall {x y : Ordinal.{0}} (hxy : x ≤ y)
    (h : ∀ p ∈ items S K, p ≤ y → p ≤ x) : rank S K x = rank S K y := by
  refine le_antisymm (rank_mono hxy) (Finset.card_le_card fun q hq => ?_)
  rw [Finset.mem_filter] at hq ⊢
  exact ⟨hq.1, h q hq.1 hq.2⟩

/-- A new item strictly between `x` and `y` raises the rank. -/
theorem rank_lt_rank_of_item {x y p : Ordinal.{0}} (hxy : x ≤ y) (hp : p ∈ items S K)
    (hpx : x < p) (hpy : p ≤ y) : rank S K x < rank S K y := by
  apply Finset.card_lt_card
  refine ⟨fun q hq => Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hq).1, le_trans (Finset.mem_filter.mp hq).2 hxy⟩, fun hsub => ?_⟩
  have := hsub (Finset.mem_filter.mpr ⟨hp, hpy⟩)
  exact absurd (Finset.mem_filter.mp this).2 (not_le.mpr hpx)

/-- No item lies strictly inside the sub-`K` part of a block: an item `≤ limitPart x + i`
(`i ≤ K`) is already `≤ limitPart x`. -/
theorem item_le_block_of_le {x p : Ordinal.{0}} {i : ℕ} (hp : p ∈ items S K) (hi : i ≤ K)
    (hpy : p ≤ limitPart x + i) : p ≤ limitPart x := by
  by_contra hpx
  rw [not_le] at hpx
  have hblock : limitPart p = limitPart x :=
    limitPart_eq_of_mem_block hpx.le
      (hpy.trans_lt (add_lt_add_right (Ordinal.natCast_lt_omega0 i) _))
  rcases items_fp hp with h0 | hhigh
  · exact absurd ((eq_limitPart_of_finitePart_eq_zero h0).symm.trans hblock) (ne_of_gt hpx)
  · have hpe : p = limitPart x + (finitePart p : Ordinal) := by
      conv_lhs => rw [← decomposition p]
      rw [hblock]
    have hlt : limitPart x + (i : Ordinal) < limitPart x + (finitePart p : Ordinal) :=
      add_lt_add_right (Nat.cast_lt.mpr (lt_of_le_of_lt hi (Nat.lt_of_succ_le hhigh))) _
    rw [← hpe] at hlt
    exact absurd hpy (not_le.mpr hlt)

/-- Self-visibility of coded values: `ω·u + m` is self-visible at every threshold `≤ m`. -/
theorem code_selfVis {u : Ordinal.{0}} {m k : ℕ} (h : k ≤ m) :
    extVisibilityReplace (ofOrd (Ordinal.omega0 * u + m)) k k
      = ofOrd (Ordinal.omega0 * u + m) :=
  (extVisibilityReplace_self_iff _ _).mpr
    (Or.inr (Or.inr ⟨_, rfl, by rw [finitePart_code]; exact h⟩))

abbrev beforeFirst (S : Finset Ordinal.{0}) (K : ℕ) (x : Ordinal.{0}) : Prop := (∃ p ∈ items S K, limitPart p = limitPart x) ∧
  ∀ p ∈ items S K, limitPart p = limitPart x → x < p

/-- The **canonical normalizer** `ν_{S,K}` (note §3).  On an ordinal `x` with `r := rank x`:

* if `x`'s block contains items, all above `x` — the below-first-item region of a
  singleton-only block — the value is the constant `ω·r + K`, just below the block's first
  item code;
* if `x`'s block starts with an interval item and `finitePart x ≤ K`, the value is the
  **affine** code `ω·(r−1) + finitePart x`;
* if no item is `≤ x` and none shares `x`'s block, the value is `⊥` (the `⊥`-fiber is a
  downward-closed union of whole blocks — the load-bearing design point);
* otherwise the value is the **plateau** `ω·(r−1) + (K+1)` of the greatest item `≤ x`.

`⊥ ↦ ⊥`, and `⊤` is always tracked by the extra top block `ω·(items S K).card`. -/
noncomputable def canonicalNormalizer (S : Finset Ordinal.{0}) (K : ℕ) : ExtOrd → ExtOrd
  | ⊥ => ⊥
  | some ⊤ => ofOrd (Ordinal.omega0 * (items S K).card + ((K + 1 : ℕ) : Ordinal))
  | some (some x) =>
    if beforeFirst S K x then
      ofOrd (Ordinal.omega0 * rank S K x + K)
    else if limitPart x ∈ items S K ∧ finitePart x ≤ K then
      ofOrd (Ordinal.omega0 * (rank S K x - 1 : ℕ) + finitePart x)
    else if rank S K x = 0 then ⊥
    else ofOrd (Ordinal.omega0 * (rank S K x - 1 : ℕ) + ((K + 1 : ℕ) : Ordinal))

@[simp] theorem canonicalNormalizer_top :
    canonicalNormalizer S K ⊤ = ofOrd (Ordinal.omega0 * (items S K).card + ((K + 1 : ℕ) : Ordinal)) := rfl

/-- The **`3b` branch** (below-first-item region of a block with items): constant
`ω·rank + K`. -/
theorem canonicalNormalizer_3b {x : Ordinal.{0}}
    (h1 : ∃ p ∈ items S K, limitPart p = limitPart x)
    (h2 : ∀ p ∈ items S K, limitPart p = limitPart x → x < p) :
    canonicalNormalizer S K (ofOrd x) = ofOrd (Ordinal.omega0 * rank S K x + K) := by
  erw [canonicalNormalizer, ite_eq_left ⟨h1, h2⟩]

/-- The **affine branch**: on the sub-`K` part of an interval-item block, `ν` shifts the
block affinely to code block `rank − 1`. -/
theorem canonicalNormalizer_affine {x : Ordinal.{0}} (hmem : limitPart x ∈ items S K)
    (hfp : finitePart x ≤ K) :
    canonicalNormalizer S K (ofOrd x)
      = ofOrd (Ordinal.omega0 * (rank S K x - 1 : ℕ) + finitePart x) := by
  have hno3b : ¬ beforeFirst S K x := by
    rintro ⟨-, hall⟩
    exact absurd (hall (limitPart x) hmem (limitPart_idem x)) (not_lt.mpr (limitPart_le x))
  erw [canonicalNormalizer, ite_eq_right hno3b, ite_eq_left ⟨hmem, hfp⟩]

/-- The **plateau branch**: the code of the greatest item `≤ x`, at offset `K+1`. -/
theorem canonicalNormalizer_plateau {x : Ordinal.{0}}
    (h3b : ¬ beforeFirst S K x)
    (haff : ¬ (limitPart x ∈ items S K ∧ finitePart x ≤ K)) (h0 : rank S K x ≠ 0) :
    canonicalNormalizer S K (ofOrd x)
      = ofOrd (Ordinal.omega0 * (rank S K x - 1 : ℕ) + ((K + 1 : ℕ) : Ordinal)) := by
  erw [canonicalNormalizer, ite_eq_right h3b, ite_eq_right haff, ite_eq_right h0]

/-- The **`⊥` branch**: blocks entirely below every item. -/
theorem canonicalNormalizer_of_rank_zero {x : Ordinal.{0}}
    (hb : ¬ ∃ p ∈ items S K, limitPart p = limitPart x) (h0 : rank S K x = 0) :
    canonicalNormalizer S K (ofOrd x) = ⊥ := by
  have haff : ¬ (limitPart x ∈ items S K ∧ finitePart x ≤ K) := by
    rintro ⟨hm, -⟩
    exact hb ⟨limitPart x, hm, limitPart_idem x⟩
  erw [canonicalNormalizer, ite_eq_right (fun hc => hb hc.1), ite_eq_right haff,
    ite_eq_left h0]

/-- **`⊥`-fiber characterization**: `ν` sends an ordinal to `⊥` exactly when no item is
`≤ x` and no item shares `x`'s block.  In particular the `⊥`-fiber is a downward-closed
union of whole blocks. -/
theorem canonicalNormalizer_eq_bot_iff {x : Ordinal.{0}} :
    canonicalNormalizer S K (ofOrd x) = ⊥ ↔
      rank S K x = 0 ∧ ¬ ∃ p ∈ items S K, limitPart p = limitPart x := by
  constructor
  · intro h
    erw [canonicalNormalizer] at h
    split_ifs at h with hb ha hr
    · exact (ofOrd_ne_bot _ h).elim
    · exact (ofOrd_ne_bot _ h).elim
    · exact ⟨hr, fun he => hb ⟨he, fun p hp _ => lt_of_not_ge (rank_eq_zero_iff.mp hr p hp)⟩⟩
    · exact (ofOrd_ne_bot _ h).elim
  · rintro ⟨h0, hb⟩
    exact canonicalNormalizer_of_rank_zero hb h0

/-- **The block bound** (note §3): the block indices of `ν_{S,K}` form an initial segment of
length at most `(items S K).card + 1 ≤ S.card + 1`. -/
theorem canonicalNormalizer_blockIdx_le (x : ExtOrd) :
    canonicalNormalizer S K x = ⊥ ∨ ∃ u m : ℕ, u ≤ (items S K).card ∧ m ≤ K + 1 ∧
      canonicalNormalizer S K x = ofOrd (Ordinal.omega0 * u + m) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨ξ, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨(items S K).card, K + 1, le_rfl, le_rfl, rfl⟩
  · erw [canonicalNormalizer]
    split_ifs with h1 h2 h3
    · exact Or.inr ⟨rank S K ξ, K, rank_le_card ξ, Nat.le_succ K, rfl⟩
    · exact Or.inr ⟨rank S K ξ - 1, finitePart ξ,
        le_trans (Nat.sub_le _ 1) (rank_le_card ξ), le_trans h2.2 (Nat.le_succ K), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨rank S K ξ - 1, K + 1,
        le_trans (Nat.sub_le _ 1) (rank_le_card ξ), le_rfl, rfl⟩

theorem canonicalNormalizer_le_top (x : ExtOrd) :
    canonicalNormalizer S K x ≤ canonicalNormalizer S K ⊤ := by
  rw [canonicalNormalizer_top]
  rcases canonicalNormalizer_blockIdx_le (S := S) (K := K) x with h | ⟨u, m, hu, hm, h⟩
  · rw [h]; exact bot_le
  · rw [h]; exact ofOrd_le_ofOrd.mpr (code_le_code (Nat.cast_le.mpr hu) hm)

private theorem norm_lower {y : Ordinal.{0}} (h0 : rank S K y ≠ 0) :
    ofOrd (Ordinal.omega0 * (rank S K y - 1 : ℕ)) ≤ canonicalNormalizer S K (ofOrd y) := by
  erw [canonicalNormalizer]
  split_ifs
  · exact ofOrd_le_ofOrd.mpr (le_trans (by gcongr; exact Nat.sub_le _ _) le_self_add)
  · exact ofOrd_le_ofOrd.mpr le_self_add
  · exact ofOrd_le_ofOrd.mpr le_self_add

private theorem norm_upper {x : Ordinal.{0}} (h : ¬ beforeFirst S K x) :
    canonicalNormalizer S K (ofOrd x) ≤ ofOrd (Ordinal.omega0 * (rank S K x - 1 : ℕ) + (K + 1 : ℕ)) := by
  erw [canonicalNormalizer, if_neg h]
  split_ifs with ha
  · exact ofOrd_le_ofOrd.mpr (code_le_code le_rfl (ha.2.trans (Nat.le_succ K)))
  · exact bot_le
  · exact le_rfl

private theorem code_le_next {a b i j : ℕ} (h : a < b) :
    ofOrd (Ordinal.omega0 * a + i) ≤ ofOrd (Ordinal.omega0 * b + j) :=
  ofOrd_le_ofOrd.mpr ((code_add_lt_mul (Nat.cast_lt.mpr h) i).le.trans le_self_add)

private theorem mono_beforeFirst {x y : Ordinal.{0}} (hxy : x ≤ y)
    (hx : beforeFirst S K x) :
    canonicalNormalizer S K (ofOrd x) ≤ canonicalNormalizer S K (ofOrd y) := by
  rw [canonicalNormalizer_3b hx.1 hx.2]
  obtain ⟨p, hp, hpx⟩ := hx.1
  rcases lt_or_eq_of_le (rank_mono (S := S) (K := K) hxy) with hlt | he
  · erw [canonicalNormalizer]
    split_ifs with hy ha h0
    · exact ofOrd_le_ofOrd.mpr (code_le_code (Nat.cast_le.mpr hlt.le) le_rfl)
    · have hl : limitPart x < limitPart y := lt_of_le_of_ne (limitPart_mono hxy)
        (fun he => (hx.2 _ ha.1 (limitPart_idem y |>.trans he.symm)).not_ge
          (he ▸ limitPart_le x))
      have hpY : p < limitPart y := (lt_limitPart_add_omega0 p).trans_le
        (limitPart_add_omega0_le (hpx ▸ hl))
      have h2 := rank_lt_rank_of_item (hpY.le.trans (limitPart_le y)) ha.1 hpY (limitPart_le y)
      have h3 := rank_lt_rank_of_item (hx.2 p hp hpx).le hp (hx.2 p hp hpx) (le_refl p)
      exact code_le_next (by omega)
    · omega
    · exact ofOrd_le_ofOrd.mpr (code_le_code (Nat.cast_le.mpr (by omega)) (Nat.le_succ K))
  · have hnot (q) (hq : q ∈ items S K) (hqx : limitPart q = limitPart x) : y < q :=
      lt_of_not_ge fun hle => (rank_lt_rank_of_item hxy hq (hx.2 q hq hqx) hle).ne he
    have hl : limitPart y = limitPart x :=
      le_antisymm ((limitPart_mono (hnot p hp hpx).le).trans_eq hpx) (limitPart_mono hxy)
    rw [canonicalNormalizer_3b ⟨p, hp, hpx.trans hl.symm⟩
      (fun q hq hqY => hnot q hq (hqY.trans hl)), he]

private theorem norm_mono_ofOrd {x y : Ordinal.{0}} (hxy : x ≤ y) :
    canonicalNormalizer S K (ofOrd x) ≤ canonicalNormalizer S K (ofOrd y) := by
  by_cases hx : beforeFirst S K x
  · exact mono_beforeFirst hxy hx
  by_cases h0 : rank S K x = 0
  · rw [canonicalNormalizer_eq_bot_iff.mpr ⟨h0, fun h => hx ⟨h, fun p hp _ =>
      lt_of_not_ge fun hle => (Nat.ne_of_gt (rank_pos_of_item hp hle)) h0⟩⟩]
    exact bot_le
  rcases lt_or_eq_of_le (rank_mono (S := S) (K := K) hxy) with hlt | he
  · exact (norm_upper hx).trans (ofOrd_le_ofOrd.mpr
      (code_add_lt_mul (Nat.cast_lt.mpr (by omega : rank S K x - 1 < rank S K y - 1))
        (K + 1)).le |>.trans (norm_lower (by omega)))
  erw [canonicalNormalizer.eq_3 S K y]
  split_ifs with hy ha hz
  · exact (norm_upper hx).trans (code_le_next (by omega))
  · have hl : limitPart y ≤ x := le_of_not_gt fun h =>
      (rank_lt_rank_of_item hxy ha.1 h (limitPart_le y)).ne he
    have hlim : limitPart x = limitPart y := le_antisymm (limitPart_mono hxy)
      ((limitPart_idem y).symm ▸ limitPart_mono hl)
    have hf := finitePart_le_of_le hlim hxy
    rw [canonicalNormalizer_affine (hlim.symm ▸ ha.1) (hf.trans ha.2), he]
    exact ofOrd_le_ofOrd.mpr (code_le_code le_rfl hf)
  · omega
  · rw [← he]; exact norm_upper hx

theorem canonicalNormalizer_mono : Monotone (canonicalNormalizer S K) :=
  monotone_ofOrd (fun _ => bot_le) canonicalNormalizer_le_top (fun _ _ h => norm_mono_ofOrd h)

/-- The natural number represented by an ordinal `< ω` (junk above). -/
noncomputable def ordToNat (o : Ordinal.{0}) : ℕ := Cardinal.toNat o.card

@[simp] theorem ordToNat_natCast (n : ℕ) : ordToNat (n : Ordinal.{0}) = n := by
  rw [ordToNat, Ordinal.card_nat, Cardinal.toNat_natCast]

theorem ordToNat_cast_eq {o : Ordinal.{0}} (h : o < Ordinal.omega0) :
    ((ordToNat o : ℕ) : Ordinal.{0}) = o := by
  obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp h
  rw [ordToNat_natCast]

/-- The `u`-th item in increasing order (junk `0` beyond the item count). -/
noncomputable def itemOfIdx (S : Finset Ordinal.{0}) (K : ℕ) (u : ℕ) : Ordinal.{0} :=
  if h : u < (items S K).card then (items S K).orderEmbOfFin rfl ⟨u, h⟩ else 0

private theorem itemOfIdx_mem {u : ℕ} (h : u < (items S K).card) : itemOfIdx S K u ∈ items S K := by
  simp [itemOfIdx, h]

private theorem rank_pred_lt_card {p : Ordinal.{0}} (hp : p ∈ items S K) :
    rank S K p - 1 < (items S K).card := by
  have := rank_le_card (S := S) (K := K) p
  have := rank_pos_of_item hp le_rfl
  omega

private theorem itemOfIdx_rank {p : Ordinal.{0}} (hp : p ∈ items S K) :
    itemOfIdx S K (rank S K p - 1) = p := by
  classical
  let s := items S K
  let e := s.orderEmbOfFin rfl
  let i := (s.orderIsoOfFin rfl).symm ⟨p, hp⟩
  have hi : e i = p := congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨p, hp⟩)
  have hset : s.filter (· ≤ p) = (Finset.Iic i).map e.toEmbedding := by
    calc
      _ = (Finset.univ.map e.toEmbedding).filter (· ≤ p) := by rw [Finset.map_orderEmbOfFin_univ]
      _ = _ := by
        rw [Finset.filter_map]
        congr 1
        ext j
        simp [← hi]
  have hr : rank S K p = i.val + 1 := by
    change (s.filter (· ≤ p)).card = _
    rw [hset, Finset.card_map, Fin.card_Iic]
  rw [hr, Nat.add_sub_cancel, itemOfIdx, dif_pos i.2]
  exact hi

/-- The sub-`K+1` value of a singleton code block: just below the item and above every
earlier item — `max (limitPart p + K) (the greatest item < p)`. -/
noncomputable def decoderLow (S : Finset Ordinal.{0}) (K : ℕ) (p : Ordinal.{0}) :
    Ordinal.{0} :=
  max (limitPart p + K) (((items S K).filter fun q => q < p).sup id)

theorem le_decoderLow_left (p : Ordinal.{0}) :
    limitPart p + (K : Ordinal) ≤ decoderLow S K p := le_max_left _ _

theorem item_le_decoderLow {q p : Ordinal.{0}} (hq : q ∈ items S K) (hqp : q < p) :
    q ≤ decoderLow S K p := by
  refine le_trans ?_ (le_max_right _ _)
  have hmem : q ∈ (items S K).filter fun r => r < p := by
    rw [Finset.mem_filter]
    exact ⟨hq, hqp⟩
  exact Finset.le_sup (f := id) hmem

theorem decoderLow_lt {p : Ordinal.{0}} (hp : K + 1 ≤ finitePart p) :
    decoderLow S K p < p := by
  have hp0 : (0 : Ordinal.{0}) < p := by
    have h0 : finitePart (0 : Ordinal.{0}) = 0 := by
      have := finitePart_natCast 0
      rwa [Nat.cast_zero] at this
    refine lt_of_le_of_ne (by rw [← Ordinal.bot_eq_zero]; exact bot_le) fun h => ?_
    rw [← h, h0] at hp
    omega
  rw [decoderLow, max_lt_iff]
  constructor
  · conv_rhs => rw [← decomposition p]
    exact add_lt_add_right (Nat.cast_lt.mpr (Nat.lt_of_succ_le hp)) _
  · rw [Finset.sup_lt_iff (by rw [Ordinal.bot_eq_zero]; exact hp0)]
    intro q hq
    exact (Finset.mem_filter.mp hq).2

theorem le_finitePart_decoderLow (p : Ordinal.{0}) : K ≤ finitePart (decoderLow S K p) := by
  have h := lt_limitPart_add_omega0 p
  have hlt : decoderLow S K p < limitPart p + Ordinal.omega0 := by
    refine max_lt_iff.mpr ⟨add_lt_add_right (Ordinal.natCast_lt_omega0 K) _, ?_⟩
    exact (Finset.sup_lt_iff (bot_le.trans_lt h)).mpr fun q hq => (Finset.mem_filter.mp hq).2.trans h
  have hle : limitPart p ≤ decoderLow S K p := le_self_add.trans (le_decoderLow_left _)
  have he := limitPart_eq_of_mem_block hle hlt
  simpa only [finitePart_limitPart_add_nat] using
    finitePart_le_of_le ((limitPart_limitPart_add_nat p K).trans he.symm) (le_decoderLow_left (S := S) p)

/-- The item owning the code block of `y`. -/
noncomputable def blockItem (S : Finset Ordinal.{0}) (K : ℕ) (y : Ordinal.{0}) :
    Ordinal.{0} :=
  itemOfIdx S K (ordToNat (y / Ordinal.omega0))

noncomputable def decodeItem (S : Finset Ordinal.{0}) (K : ℕ) (p : Ordinal.{0}) (i : ℕ) : Ordinal.{0} :=
  if finitePart p = 0 then p + min i K
  else if i ≤ K then decoderLow S K p else p

/-- The **canonical decoder** `τ_{S,K}` (note §3), the mirror map on the code side: on the
code block of an item `p` — every block below `ω·(items S K).card` is one — it is affine back
onto `[p, p+K]` when `p` is an interval item (constant `p + K` on the plateau), and for a
singleton item it sends offset `≥ K+1` to `p` and the sub-`K+1` part to the constant
`decoderLow p`; everything at or beyond the top block decodes to `⊤`. -/
noncomputable def canonicalDecoder (S : Finset Ordinal.{0}) (K : ℕ) : ExtOrd → ExtOrd
  | ⊥ => ⊥
  | some ⊤ => ⊤
  | some (some y) => if y < Ordinal.omega0 * (items S K).card then
      ofOrd (decodeItem S K (blockItem S K y) (finitePart y)) else ⊤

@[simp] theorem canonicalDecoder_bot : canonicalDecoder S K ⊥ = ⊥ := rfl

theorem canonicalDecoder_ofOrd (y : Ordinal.{0}) :
    canonicalDecoder S K (ofOrd y) = if y < Ordinal.omega0 * (items S K).card then
      ofOrd (decodeItem S K (blockItem S K y) (finitePart y)) else ⊤ := rfl

theorem canonicalDecoder_topRegion {y : Ordinal.{0}}
    (hy : ¬ y < Ordinal.omega0 * (items S K).card) :
    canonicalDecoder S K (ofOrd y) = ⊤ := by
  rw [canonicalDecoder_ofOrd, ite_eq_right hy]

theorem canonicalDecoder_reflects_bottom (x : ExtOrd)
    (hx : canonicalDecoder S K x = ⊥) : x = ⊥ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨y, rfl⟩
  · rfl
  · exact hx
  · rw [canonicalDecoder_ofOrd] at hx
    split_ifs at hx <;> contradiction

/-- The code division computation: `(ω·u + m) / ω = u`. -/
theorem code_div_omega0 (u : Ordinal.{0}) (m : ℕ) :
    (Ordinal.omega0 * u + m) / Ordinal.omega0 = u := by
  rw [Ordinal.mul_add_div _ Ordinal.omega0_ne_zero,
    Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 m), add_zero]

@[simp] theorem blockItem_code (u m : ℕ) :
    blockItem S K (Ordinal.omega0 * u + m) = itemOfIdx S K u := by
  rw [blockItem, code_div_omega0, ordToNat_natCast]

/-- In the decoding region the block index is a genuine item index, and the block level of
`y` is the corresponding code block. -/
theorem blockIdx_lt {y : Ordinal.{0}} (hy : y < Ordinal.omega0 * (items S K).card) :
    ordToNat (y / Ordinal.omega0) < (items S K).card ∧
      limitPart y = Ordinal.omega0 * (ordToNat (y / Ordinal.omega0) : ℕ) := by
  have hdiv : y / Ordinal.omega0 < ((items S K).card : Ordinal) :=
    (Ordinal.lt_mul_iff_div_lt Ordinal.omega0_ne_zero).mp hy
  have hcast : ((ordToNat (y / Ordinal.omega0) : ℕ) : Ordinal) = y / Ordinal.omega0 :=
    ordToNat_cast_eq (lt_trans hdiv (Ordinal.natCast_lt_omega0 _))
  constructor
  · rw [← hcast] at hdiv
    exact_mod_cast hdiv
  · rw [hcast]
    rfl

/-- **`ν_{S,K}` is a `K`-step shifter** (note §3): with the step suppressor `g_K` it is a
legal Def. 2.3.9 witness — the clause-5 case split is `IsStepShifter.clause5`. -/
theorem isStepShifter_canonicalNormalizer :
    IsStepShifter K (canonicalNormalizer S K) where
  map_bot := rfl
  mono := canonicalNormalizer_mono
  selfVis := by
    intro x k hk hx
    rcases ExtOrd.cases x with rfl | rfl | ⟨ξ, rfl⟩
    · rfl
    · rw [canonicalNormalizer_top]
      exact code_selfVis (hk.trans (Nat.le_succ K))
    · rw [extVisibilityReplace_ofOrd, ofOrd_inj] at hx
      have hfp := (visibilityReplace_self_iff _ _).mp hx
      erw [canonicalNormalizer]
      split_ifs with h1 h2 h3
      · exact code_selfVis hk
      · exact code_selfVis hfp
      · rfl
      · exact code_selfVis (hk.trans (Nat.le_succ K))
  blockwise := by
    intro ξ
    let l := limitPart ξ
    have hl (i : ℕ) : limitPart (l + (i : ℕ)) = l := limitPart_limitPart_add_nat ξ i
    have hf (i : ℕ) : finitePart (l + (i : ℕ)) = i := finitePart_limitPart_add_nat ξ i
    have hr (i : ℕ) (hi : i ≤ K) : rank S K l = rank S K (l + (i : ℕ)) :=
      rank_eq_of_forall (self_le_add_nat _ _) (fun q hq => item_le_block_of_le (x := ξ) hq hi)
    by_cases hmem : l ∈ items S K
    · left
      refine ⟨Ordinal.omega0 * (rank S K l - 1 : ℕ), finitePart_omega0_mul _, fun i hi => ?_⟩
      rw [canonicalNormalizer_affine ((hl i).symm ▸ hmem) ((hf i).symm ▸ hi), ← hr i hi, hf]
    · right
      by_cases hblock : ∃ p ∈ items S K, limitPart p = l
      · refine ⟨ofOrd (Ordinal.omega0 * rank S K l + K), code_selfVis le_rfl, fun i hi => ?_⟩
        obtain ⟨p, hp, hpl⟩ := hblock
        rw [canonicalNormalizer_3b ⟨p, hp, hpl.trans (hl i).symm⟩ ?_, ← hr i hi]
        intro q hq hq'
        by_contra! hle
        have he : q = l := le_antisymm (item_le_block_of_le (x := ξ) hq hi hle)
          (((hq'.trans (hl i)).symm) ▸ limitPart_le q)
        exact hmem (he ▸ hq)
      · refine ⟨if rank S K l = 0 then ⊥ else ofOrd (Ordinal.omega0 * (rank S K l - 1 : ℕ) + (K + 1 : ℕ)),
          ?_, fun i hi => ?_⟩
        · split_ifs
          · rfl
          · exact code_selfVis (Nat.le_succ K)
        · have hn : ¬ beforeFirst S K (l + (i : ℕ)) := fun h => by
            obtain ⟨p, hp, he⟩ := h.1
            exact hblock ⟨p, hp, he.trans (hl i)⟩
          erw [canonicalNormalizer, if_neg hn, hl i, ← hr i hi]
          rw [if_neg (fun h => hmem h.1)]
  bot_blocks := by
    intro ξ ζ hlim hbot
    rw [canonicalNormalizer_eq_bot_iff] at hbot ⊢
    obtain ⟨h0, hb⟩ := hbot
    constructor
    · rw [rank_eq_zero_iff] at h0 ⊢
      intro p hp hpz
      by_cases hpl : limitPart p = limitPart ζ
      · exact hb ⟨p, hp, hpl.trans hlim.symm⟩
      · refine h0 p hp (le_of_lt (lt_of_limitPart_lt ?_))
        rw [hlim]
        exact lt_of_le_of_ne (limitPart_mono hpz) hpl
    · rintro ⟨p, hp, hpl⟩
      exact hb ⟨p, hp, hpl.trans hlim.symm⟩

theorem itemOfIdx_lt {u v : ℕ} (hv : v < (items S K).card) (huv : u < v) :
    itemOfIdx S K u < itemOfIdx S K v := by
  rw [itemOfIdx, itemOfIdx, dite_eq_left (lt_trans huv hv), dite_eq_left hv]
  exact ((items S K).orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr huv)

/-- **The canonical decoder is monotone** (clause 4 of Def. 2.3.9 for `τ_{S,K}`). -/
private theorem decodeItem_mono {p : Ordinal.{0}} (hp : p ∈ items S K) :
    Monotone (decodeItem S K p) := by
  intro i j hij
  unfold decodeItem
  by_cases h0 : finitePart p = 0
  · simp only [h0, if_true]
    exact add_le_add_right (Nat.cast_le.mpr (min_le_min_right _ hij)) _
  · simp only [h0, if_false]
    by_cases hj : j ≤ K
    · rw [if_pos hj, if_pos (hij.trans hj)]
    · rw [if_neg hj]
      split_ifs
      · exact (decoderLow_lt ((items_fp hp).resolve_left h0)).le
      · exact le_rfl

private theorem decodeItem_ordered {p q : Ordinal.{0}} (hp : p ∈ items S K)
    (hq : q ∈ items S K) (hpq : p < q) (i j : ℕ) : decodeItem S K p i ≤ decodeItem S K q j := by
  have hu : decodeItem S K p i ≤ (if finitePart p = 0 then p + K else p) := by
    unfold decodeItem
    split_ifs with h
    · exact add_le_add_right (Nat.cast_le.mpr (min_le_right _ _)) _
    · exact (decoderLow_lt ((items_fp hp).resolve_left h)).le
    · exact le_rfl
  have hl : (if finitePart q = 0 then q else decoderLow S K q) ≤ decodeItem S K q j := by
    unfold decodeItem
    split_ifs with h
    · exact le_self_add
    · exact le_rfl
    · exact (decoderLow_lt ((items_fp hq).resolve_left h)).le
  refine hu.trans (le_trans ?_ hl)
  split_ifs with h0 h0' h0'
  · have he := eq_limitPart_of_finitePart_eq_zero h0
    have he' := eq_limitPart_of_finitePart_eq_zero h0'
    have h := limitPart_add_omega0_le (show limitPart p < limitPart q from he.symm ▸ he'.symm ▸ hpq)
    rw [he, he'] at h
    exact (add_lt_add_right (Ordinal.natCast_lt_omega0 K) p).le.trans h
  · exact (add_le_add ((eq_limitPart_of_finitePart_eq_zero h0) ▸ limitPart_mono hpq.le) le_rfl).trans
      (le_decoderLow_left _)
  · exact hpq.le
  · exact item_le_decoderLow hp hpq

private theorem decodeItem_at {y : Ordinal.{0}} (hy : y < Ordinal.omega0 * (items S K).card) :
    canonicalDecoder S K (ofOrd y) = ofOrd (decodeItem S K (blockItem S K y) (finitePart y)) :=
  if_pos hy

private theorem decoder_mono_ofOrd {y z : Ordinal.{0}} (hyz : y ≤ z) :
    canonicalDecoder S K (ofOrd y) ≤ canonicalDecoder S K (ofOrd z) := by
  by_cases hz : z < Ordinal.omega0 * (items S K).card
  · have hy := hyz.trans_lt hz
    obtain ⟨hy', hly⟩ := blockIdx_lt hy
    obtain ⟨hz', hlz⟩ := blockIdx_lt hz
    have hle : ordToNat (y / Ordinal.omega0) ≤ ordToNat (z / Ordinal.omega0) := by
      apply Nat.cast_le.mp ((Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono.le_iff_le.mp ?_)
      rw [← hly, ← hlz]
      exact limitPart_mono hyz
    rw [decodeItem_at hy, decodeItem_at hz, ofOrd_le_ofOrd]
    rcases lt_or_eq_of_le hle with h | h
    · exact decodeItem_ordered (itemOfIdx_mem hy') (itemOfIdx_mem hz') (itemOfIdx_lt hz' h) _ _
    · have he : limitPart y = limitPart z := by rw [hly, hlz, h]
      have hf := finitePart_le_of_le he hyz
      have hp : blockItem S K y = blockItem S K z := by simp only [blockItem, h]
      rw [hp]
      exact decodeItem_mono (itemOfIdx_mem hz') hf
  · rw [canonicalDecoder_topRegion hz]
    exact le_top

theorem canonicalDecoder_mono : Monotone (canonicalDecoder S K) :=
  monotone_ofOrd (fun _ => bot_le) (fun _ => le_top) (fun _ _ h => decoder_mono_ofOrd h)

/-- **`τ_{S,K}` is a `K`-step shifter** (note §3): the code side has the same block geometry
with exactly one item per block, so the same case split applies. -/
theorem isStepShifter_canonicalDecoder :
    IsStepShifter K (canonicalDecoder S K) where
  map_bot := rfl
  mono := canonicalDecoder_mono
  selfVis := by
    intro x k hk hx
    rcases ExtOrd.cases x with rfl | rfl | ⟨y, rfl⟩
    · rfl
    · rfl
    · by_cases hy : y < Ordinal.omega0 * (items S K).card
      · rw [decodeItem_at hy]
        apply selfVis_ofOrd_iff.mpr
        unfold decodeItem
        split_ifs with h0 hm
        · rw [← eq_limitPart_of_finitePart_eq_zero h0, finitePart_limitPart_add_nat]
          exact le_min (selfVis_ofOrd_iff.mp hx) hk
        · exact hk.trans (le_finitePart_decoderLow _)
        · exact hk.trans (Nat.le_of_succ_le ((items_fp (itemOfIdx_mem (blockIdx_lt hy).1)).resolve_left h0))
      · rw [canonicalDecoder_topRegion hy]
        rfl
  blockwise := by
    intro ξ
    have hblock (i : ℕ) : limitPart ξ + (i : ℕ) < Ordinal.omega0 * (items S K).card ↔
        ξ < Ordinal.omega0 * (items S K).card := by
      simp only [Ordinal.lt_mul_iff_div_lt Ordinal.omega0_ne_zero, limitPart, code_div_omega0]
    by_cases h : ξ < Ordinal.omega0 * (items S K).card
    · have hv (i : ℕ) : canonicalDecoder S K (ofOrd (limitPart ξ + i)) =
          ofOrd (decodeItem S K (blockItem S K ξ) i) := by
        rw [decodeItem_at ((hblock i).mpr h), finitePart_limitPart_add_nat, blockItem, blockItem,
          limitPart, code_div_omega0]
      by_cases h0 : finitePart (blockItem S K ξ) = 0
      · exact Or.inl ⟨_, h0, fun i hi => by rw [hv, decodeItem, if_pos h0, min_eq_left hi]⟩
      · exact Or.inr ⟨_, selfVis_ofOrd_iff.mpr (le_finitePart_decoderLow _),
          fun i hi => by rw [hv, decodeItem, if_neg h0, if_pos hi]⟩
    · exact Or.inr ⟨⊤, rfl, fun i _ => canonicalDecoder_topRegion (mt (hblock i).mp h)⟩
  bot_blocks := fun _ _ _ h => (ofOrd_ne_bot _ (canonicalDecoder_reflects_bottom _ h)).elim

private theorem decode_code {b m : ℕ} (hb : b < (items S K).card) :
    canonicalDecoder S K (ofOrd (Ordinal.omega0 * b + m)) =
      ofOrd (decodeItem S K (itemOfIdx S K b) m) := by
  rw [decodeItem_at (code_add_lt_mul (Nat.cast_lt.mpr hb) m), blockItem_code, finitePart_code]

/-- `τ_{S,K} ∘ ν_{S,K}` is the identity on `⊥`, `⊤`, and the tracked ordinals `S`. -/
theorem canonicalDecoder_canonicalNormalizer {x : ExtOrd}
    (hx : x = ⊥ ∨ x = ⊤ ∨ ∃ s ∈ S, x = ofOrd s) :
    canonicalDecoder S K (canonicalNormalizer S K x) = x := by
  rcases hx with rfl | rfl | ⟨s, hs, rfl⟩
  · rfl
  · rw [canonicalNormalizer_top]
    refine canonicalDecoder_topRegion ?_
    rw [not_lt]
    exact self_le_add_nat _ _
  · by_cases hfp : finitePart s ≤ K
    · have hm := limitPart_mem_items hs hfp
      have hr := rank_eq_of_forall (limitPart_le s) (S := S) (K := K) fun p hp hps =>
        item_le_block_of_le (x := s) hp hfp (by simpa only [decomposition] using hps)
      rw [canonicalNormalizer_affine hm hfp, ← hr,
        decode_code (rank_pred_lt_card hm), itemOfIdx_rank hm, decodeItem, finitePart_limitPart,
        if_pos rfl, min_eq_left hfp, decomposition]
    · have hm := mem_items_of_high hs (by omega : K + 1 ≤ finitePart s)
      have hb : ¬ beforeFirst S K s := fun h => (lt_irrefl s) (h.2 s hm rfl)
      have hz := Nat.one_le_iff_ne_zero.mp (rank_pos_of_item hm le_rfl)
      rw [canonicalNormalizer_plateau hb (fun h => hfp h.2) hz,
        decode_code (rank_pred_lt_card hm), itemOfIdx_rank hm, decodeItem,
        if_neg (by omega : finitePart s ≠ 0), if_neg (by omega : ¬ K + 1 ≤ K)]

end Transform

namespace ExtOrd

/-- The **coded alphabet** at block bound `t` and grade bound `K` (note §§3–4): `⊥` together
with the codes `ω·u + m`, `u ≤ t`, `m ≤ K+1` — a `Finset`. -/
noncomputable def codedAlphabet (t K : ℕ) : Finset ExtOrd :=
  insert ⊥ ((Finset.range (t + 1) ×ˢ Finset.range (K + 2)).image
    fun um => ofOrd (Ordinal.omega0 * um.1 + um.2))

theorem mem_codedAlphabet_iff {t K : ℕ} {x : ExtOrd} :
    x ∈ codedAlphabet t K ↔
      x = ⊥ ∨ ∃ u m : ℕ, u ≤ t ∧ m ≤ K + 1 ∧ x = ofOrd (Ordinal.omega0 * u + m) := by
  simp only [codedAlphabet, Finset.mem_insert, Finset.mem_image, Finset.mem_product,
    Finset.mem_range]
  constructor
  · rintro (h | ⟨⟨u, m⟩, ⟨hu, hm⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨u, m, by omega, by omega, rfl⟩
  · rintro (h | ⟨u, m, hu, hm, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨⟨u, m⟩, ⟨by omega, by omega⟩, rfl⟩

/-- **The finite inventory at the combinatorial level** (note §4; the counting content of
Lemmas 4.3.4/4.3.9/4.3.11): over a finite family, the labellings with values in the coded
alphabet form a finite set. -/
theorem codedLabellings_finite (D : Type*) [Finite D] (t K : ℕ) :
    {F : D → ExtOrd | ∀ d, F d ∈ codedAlphabet t K}.Finite := by
  have h : {F : D → ExtOrd | ∀ d, F d ∈ codedAlphabet t K} =
      Set.pi Set.univ fun _ : D => (codedAlphabet t K : Set ExtOrd) := by
    ext F
    simp [Set.mem_pi]
  rw [h]
  exact Set.Finite.pi fun _ => (codedAlphabet t K).finite_toSet

end ExtOrd

namespace Transform

variable {S : Finset Ordinal.{0}} {K : ℕ}

/-- Canonical forms take values in the coded alphabet at block bound `≥ S.card` (note §4):
the inventory of canonical forms is finite. -/
theorem canonicalNormalizer_mem_codedAlphabet {t : ℕ} (ht : S.card ≤ t) (x : ExtOrd) :
    canonicalNormalizer S K x ∈ ExtOrd.codedAlphabet t K := by
  rw [ExtOrd.mem_codedAlphabet_iff]
  rcases canonicalNormalizer_blockIdx_le x with h | ⟨u, m, hu, hm, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨u, m, le_trans hu (le_trans items_card_le ht), hm, h⟩

end Transform

end VaughtConjecture.Knight
