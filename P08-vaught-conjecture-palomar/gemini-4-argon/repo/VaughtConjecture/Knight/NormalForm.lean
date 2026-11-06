/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Order.Interval.Finset.Fin
public import VaughtConjecture.Knight.SemScheme

/-! # Finite coded respecting normal forms: the unconditional kernel (#121 (2/3))

The Lean kernel of the paper theorem `docs/notes/normal-form.md` (#121 PR 1, merged #127):
everything of §§2–4 and §6 that is unconditional — the Cap Lemma, the canonical coded normal
form with faithful two-sided witnesses, the finite coded inventory at the combinatorial level,
the statement of Normalization Closure (NC, #128), and the two compiled refutations (Knight's
2.3.3-style pointwise map; the pushforward composite witness for (NC)).  No lemma below assumes
`NormalizationClosure`; the definition is *stated only* (#128 is blocked-math).

## Contents

* **Step shifters** (`Transform.stepSuppressor`, `Transform.IsStepShifter`): the legality
  pattern of the note's §3, compiled once.  A `K`-step shifter is a monotone, `⊥`-fixing label
  map that preserves self-visibility at thresholds `≤ K`, is affine-or-constant on the sub-`K`
  part of every ω-block, and has a `⊥`-fiber closed under whole blocks.  The clause-5 case
  split of Def. 2.3.9 for the step suppressor `g_K` (`⊤` up to `K`, `⊥` above) is proved once
  (`IsStepShifter.clause5`): thresholds `k ≤ K` by unguarded commutation (affine pieces
  commute, constants are `⊔⁺_k`-fixed), thresholds `k > K` by the `⊥`-fiber block-closure
  (the guard pins `σ α = ⊥`, and `⊔⁺_k` preserves blocks).  Every step shifter is a legal
  transform witness on families of grade `≤ K` (`IsStepShifter.transformsTo`).
* **Cap Lemma** (`Transform.TransformsTo.cap`, note §2 Lemma 2.A; the faithful content of
  Lemmas 2.3.12/2.4.1 for targets): if `p ⇒ q` and `γ` is self-visible at a bound `K` of all
  grades, then `p ⇒ q ∧ γ`, with the direct witness `(min (g, γ)` below `K`, `⊥` above`, σ)`
  — no transitivity.  (The note prints the witness `min (g, γ)`; above `K` its
  self-visibility can fail, so the compiled witness truncates it to `⊥` there — only values
  at grades `≤ K` enter the row equation, and the smaller suppressor only weakens the
  clause-5 guard.)  **Corollary 2.B** (`RespectsSemanticsBelow.cap`, faithful Lemma 2.5.8):
  respect of a restricted semantics is closed under capping at a label self-visible at the
  pair's grade.
* **Canonical coded normal form** (note §3, Lemma 3.A; faithful Lemmas 2.3.3/2.3.15): the
  canonical normalizer `Transform.canonicalNormalizer S K` (`ν_{S,K}`) and decoder
  `Transform.canonicalDecoder S K` (`τ`), both `K`-step shifters, with
  `τ (ν s) = s` on `⊥`, `⊤`, and `S` (`canonicalDecoder_canonicalNormalizer`); hence the
  **NF Lemma** both ways, `TransformsTo.toCanonical : r ⇒ ⌜r⌝_K` and
  `TransformsTo.ofCanonical : ⌜r⌝_K ⇒ r` (`S ⊇ ran r ∩ Ord`), and the two-sided
  `Equivalent.canonical`.  The values of `ν` are coded at the `grade+1` bound
  (`canonicalNormalizer_isCodedLabel`: `⊥` or `ω·u + m` with `m ≤ K+1`), with block indices
  bounded by the number of items, itself at most `S.card` (+1 block for `⊤`)
  (`canonicalNormalizer_blockIdx_le`, `items_card_le`).
* **Finite inventory, combinatorial level** (note §4's counting bound; the faithful content
  of Lemmas 4.3.4/4.3.9/4.3.11 by pure counting): the coded alphabet
  `ExtOrd.codedAlphabet t K` is a `Finset`, canonical forms take values in it
  (`canonicalNormalizer_mem_codedAlphabet`), and the coded labellings of a finite family form
  a finite set (`codedLabellings_finite`), as do the (labelling, cutoff) pairs
  (`codedInventory_finite`).  No scheme extension is built here (`extendMany`, the inventory
  membership conditions, and the completion are #121 PR 3 material, gated on #128).
* **Normalization Closure** (`NormalizationClosure`, note §6 / #128): canonical images of
  respecting labellings respect.  Stated, not proved, not assumed anywhere.
  The existential finite version — respect closed under `ν_{insert 0 S, K}`, hence a finite
  coded respecting representative with exact decoding on any finite lower domain — is proved
  without (NC) in `Knight/PositiveNormalization.lean`
  (`RespectsSemanticsBelow.canonical_insert_zero`, `exists_coded_representative`).
* **Refutations.**  `pointwiseNormalizer_fails_clause5`: Knight's 2.3.3-style pointwise
  normalizer (tracking the singleton `ω+2` at `K = 1` pointwise, `⊥` below, one plateau
  above) is monotone and fixes `⊥` but violates faithful clause 5 under **every** suppressor
  — its `⊥`-fiber splits the block `[ω, ω+ω)` — which is why the canonical normalizer is
  blockwise (`canonicalNormalizer_block_not_bot` shows the repaired value).
  `normalizationClosure_pushforward_fails` (note §6, new): a fully legal Def. 2.3.9 witness
  pair `(g, σ)` whose pushforward composite `(ν ∘ g, ν ∘ σ)` violates clause 5 — the inner
  shifter jumps, inside a `⊔⁺_2`-orbit on which its own guard fails, out of the `ν`-fiber of
  `⊥`.  What is refuted is that *witness*, not (NC) itself: any proof of (NC) needs a
  re-derived witness.

## Fidelity status

All statements are against the faithful `TransformsTo` (Def. 2.3.9 verbatim, no
inflationarity, unguarded clause 5) and `RespectsSemanticsBelow` (Def. 2.5.4 on a lower set).
No transitivity of `⇒` is used or stated (Lemma 2.3.14 is a proof-gap; the printed composite
witness is refuted, KVC-d5): the Cap Lemma and both NF witnesses are direct, in the pattern of
`TransformsTo.truncExt_target` (#89).  See `docs/CONCORDANCE.md` rows 2.3.3, 2.3.12, 2.3.15,
2.5.13 and `docs/notes/normal-form.md` §10. -/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight

open Value ExtOrd

/-! ### Label arithmetic: ω-blocks and codes -/

namespace Value

/-- Self-visibility at `k` fixes every replacement value, not just `k`:
if `γ = γ ⊔⁺_k k` then `γ = γ ⊔⁺_k i` for every `i`. -/
theorem extVisReplace_eq_self_of_selfVis {v : ExtOrd} {k : ℕ}
    (h : extVisibilityReplace v k k = v) (i : ℕ) : extVisibilityReplace v k i = v := by
  rcases (extVisibilityReplace_self_iff v k).mp h with rfl | rfl | ⟨α, rfl, hfp⟩
  · rfl
  · rfl
  · rw [extVisibilityReplace_ofOrd, visibilityReplace, ite_eq_right (not_lt.mpr hfp)]

/-- The finite part of a natural number is itself. -/
theorem finitePart_natCast (n : ℕ) : finitePart (n : Ordinal.{0}) = n := by
  have h := finitePart_spec (n : Ordinal.{0})
  rw [Ordinal.mod_eq_of_lt (Ordinal.natCast_lt_omega0 n)] at h
  exact_mod_cast h.symm

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

/-- `min` preserves self-visibility (a `min` of two self-visible labels is one of them). -/
theorem extVisReplace_min_self {x y : ExtOrd} {k : ℕ}
    (hx : extVisibilityReplace x k k = x) (hy : extVisibilityReplace y k k = y) :
    extVisibilityReplace (min x y) k k = min x y := by
  rcases min_cases x y with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm] <;> assumption

end Value

namespace Transform

/-! ### The step suppressor and step shifters -/

/-- The **step suppressor** `g_K` (note §3): `⊤` at thresholds `≤ K`, `⊥` above. -/
def stepSuppressor (K : ℕ) : ℕ → ExtOrd := fun k => if k ≤ K then ⊤ else ⊥

@[simp] theorem stepSuppressor_of_le {K k : ℕ} (h : k ≤ K) : stepSuppressor K k = ⊤ :=
  ite_eq_left h

@[simp] theorem stepSuppressor_of_gt {K k : ℕ} (h : K < k) : stepSuppressor K k = ⊥ :=
  ite_eq_right (not_le.mpr h)

theorem stepSuppressor_antitone (K : ℕ) :
    ∀ n m : ℕ, n < m → stepSuppressor K m ≤ stepSuppressor K n := by
  intro n m hnm
  unfold stepSuppressor
  split_ifs <;> first | omega | exact bot_le | exact le_rfl

theorem stepSuppressor_selfVis (K : ℕ) :
    ∀ n : ℕ, stepSuppressor K n = extVisibilityReplace (stepSuppressor K n) n n := by
  intro n; unfold stepSuppressor; split_ifs <;> rfl

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
    ∀ (α : ExtOrd) (k : ℕ), σ α ≤ stepSuppressor K k → ∀ i : ℕ, i ≤ k →
      σ (extVisibilityReplace α k i) = extVisibilityReplace (σ α) k i := by
  intro α k hguard i hi
  by_cases hk : k ≤ K
  · rcases ExtOrd.cases α with rfl | rfl | ⟨ξ, rfl⟩
    · rw [extVisibilityReplace_bot, h.map_bot, extVisibilityReplace_bot]
    · rw [extVisibilityReplace_top,
        extVisReplace_eq_self_of_selfVis (h.selfVis ⊤ k hk (extVisibilityReplace_top k k)) i]
    · by_cases hfp : k ≤ finitePart ξ
      · have hself : extVisibilityReplace (ofOrd ξ) k k = ofOrd ξ :=
          (extVisibilityReplace_self_iff _ k).mpr (Or.inr (Or.inr ⟨ξ, rfl, hfp⟩))
        rw [extVisReplace_eq_self_of_selfVis hself i,
          extVisReplace_eq_self_of_selfVis (h.selfVis _ k hk hself) i]
      · rw [not_le] at hfp
        have hrepl : extVisibilityReplace (ofOrd ξ) k i = ofOrd (limitPart ξ + i) := by
          rw [extVisibilityReplace_ofOrd, visibilityReplace, ite_eq_left hfp]; rfl
        have hξ : ofOrd ξ = ofOrd (limitPart ξ + (finitePart ξ : ℕ)) := by rw [decomposition]
        rcases h.blockwise ξ with ⟨β, hβ0, haff⟩ | ⟨c, hcvis, hconst⟩
        · have hβ : limitPart β = β := eq_limitPart_of_finitePart_eq_zero hβ0
          rw [hrepl, haff i (hi.trans hk), hξ, haff (finitePart ξ) (hfp.le.trans hk),
            extVisibilityReplace_ofOrd, visibilityReplace,
            ite_eq_left (by rw [← hβ, finitePart_limitPart_add_nat]; exact hfp),
            ordinalReplace, ← hβ, limitPart_limitPart_add_nat, hβ]
        · rw [hrepl, hconst i (hi.trans hk), hξ, hconst (finitePart ξ) (hfp.le.trans hk),
            extVisReplace_eq_self_of_selfVis (extVisReplace_self_of_le hcvis hk) i]
  · have hbot : σ α = ⊥ := le_bot_iff.mp (stepSuppressor_of_gt (not_le.mp hk) ▸ hguard)
    rw [hbot, extVisibilityReplace_bot]
    rcases ExtOrd.cases α with rfl | rfl | ⟨ξ, rfl⟩
    · exact h.map_bot
    · exact hbot
    · rw [extVisibilityReplace_ofOrd, visibilityReplace]
      split_ifs
      · exact h.bot_blocks ξ _ (limitPart_limitPart_add_nat ξ i).symm hbot
      · exact hbot

/-- Every `K`-step shifter is a legal transform witness with the step suppressor, on any
family of grades `≤ K`: `p ⇒ σ ∘ p` for **every** labelling `p` (note §3; no hypotheses on
`p`). -/
theorem IsStepShifter.transformsTo {D : Type*} {grade : D → ℕ} {K : ℕ} {σ : ExtOrd → ExtOrd}
    (h : IsStepShifter K σ) (hK : ∀ d, grade d ≤ K) (p : D → ExtOrd) :
    TransformsTo grade p (fun d => σ (p d)) :=
  ⟨stepSuppressor K, σ, stepSuppressor_antitone K, stepSuppressor_selfVis K, h.map_bot,
    h.mono, h.clause5, fun d => by rw [stepSuppressor_of_le (hK d), min_top_right]⟩

/-! ### The Cap Lemma -/

/-- **Cap Lemma** (note §2, Lemma 2.A; the faithful Lemmas 2.3.12/2.4.1 for targets): if
`p ⇒ q` with witness `(g, σ)` and `γ` is self-visible at a bound `K` of every grade of the
family, then `p ⇒ q ∧ γ`, with the direct witness `(g', σ)` where `g' k = min (g k) γ` for
`k ≤ K` and `g' k = ⊥` above.  No transitivity: `g'` is antitone; self-visible at `k` because
`min (g k) γ` is `g k` or `γ`, each self-visible at `k ≤ K` (heredity,
`extVisReplace_self_of_le`); clause 5 for the new guard reduces to the old clause 5 since
`g' k ≤ g k` everywhere.  (The note prints the untruncated witness `min (g, γ)`, whose
self-visibility can fail at thresholds `> K`; the truncation to `⊥` there is the faithful
repair and changes no row value, since every grade is `≤ K`.) -/
theorem TransformsTo.cap {D : Type*} {grade : D → ℕ} {p q : D → ExtOrd} {K : ℕ} {γ : ExtOrd}
    (h : TransformsTo grade p q) (hK : ∀ d, grade d ≤ K)
    (hγ : extVisibilityReplace γ K K = γ) :
    TransformsTo grade p (fun d => min (q d) γ) := by
  obtain ⟨g, σ, hg_dec, hg_vis, hσ_bot, hσ_mono, hσ_vis, hσ_eq⟩ := h
  refine ⟨fun k => if k ≤ K then min (g k) γ else ⊥, σ,
    fun n m hnm => ?_, fun n => ?_, hσ_bot, hσ_mono, fun α k hle i hi => ?_,
    fun d => by dsimp only; rw [ite_eq_left (hK d), ← min_assoc, ← hσ_eq d]⟩
  · dsimp only; split_ifs
    · exact min_le_min (hg_dec n m hnm) le_rfl
    · omega
    · exact bot_le
    · exact le_rfl
  · dsimp only; split_ifs with hn
    · exact (extVisReplace_min_self (hg_vis n).symm (extVisReplace_self_of_le hγ hn)).symm
    · rfl
  · refine hσ_vis α k (hle.trans ?_) i hi
    dsimp only; split_ifs; exacts [min_le_left _ _, bot_le]

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
  orderly d :=
    (extVisReplace_min_self (h.orderly d).symm
      (extVisReplace_self_of_le hγ d.2.2)).symm
  locality Sig := by
    simpa only [min_min_min_comm _ γ _ γ, min_self] using
      (h.locality Sig).cap (fun d => (d.2.trans Sig.2).2) hγ
  availability Sig Xi₀ hscope hgrade := by
    obtain ⟨Xi, hcell, hle⟩ := h.availability Sig Xi₀ hscope hgrade
    exact ⟨Xi, hcell, min_le_min hle le_rfl⟩

/-! ### More label arithmetic for the canonical alphabet -/

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
  have h3 : limitPart x + (finitePart x : Ordinal) ≤ limitPart x + (finitePart y : Ordinal) := by
    rw [decomposition x, hlim, decomposition y]; exact hxy
  exact_mod_cast (add_le_add_iff_left (limitPart x)).mp h3

/-- An ordinal in the half-open block `[limitPart x, limitPart x + ω)` has limit part
`limitPart x`. -/
theorem limitPart_eq_of_mem_block {x q : Ordinal.{0}} (h1 : limitPart x ≤ q)
    (h2 : q < limitPart x + Ordinal.omega0) : limitPart q = limitPart x :=
  le_antisymm (not_lt.mp fun hlt =>
    not_le.mpr h2 ((limitPart_add_omega0_le hlt).trans (limitPart_le q)))
    (limitPart_idem x ▸ limitPart_mono h1)

end Value

namespace Transform

/-! ### The canonical alphabet: items and ranks -/

/-- The **items** of the canonical alphabet `ν_{S,K}` (note §3), a finite set of ordinals in
increasing order: for each block meeting `S` at finite parts `≤ K`, an *interval item* at the
block start (the image of `limitPart`); for each `s ∈ S` with finite part `≥ K+1`, a
*singleton item* at `s`.  (The top label `⊤` is always tracked separately, by the extra block
`(items S K).card`; see `canonicalNormalizer`.) -/
def items (S : Finset Ordinal.{0}) (K : ℕ) : Finset Ordinal.{0} :=
  (S.filter fun s => finitePart s ≤ K).image limitPart ∪
    S.filter fun s => K + 1 ≤ finitePart s

variable {S : Finset Ordinal.{0}} {K : ℕ}

theorem limitPart_mem_items {s : Ordinal.{0}} (hs : s ∈ S) (hfp : finitePart s ≤ K) :
    limitPart s ∈ items S K :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hs, hfp⟩))

theorem mem_items_of_high {s : Ordinal.{0}} (hs : s ∈ S) (hfp : K + 1 ≤ finitePart s) :
    s ∈ items S K :=
  Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hs, hfp⟩)

/-- Items are block starts or high singletons. -/
theorem items_fp {p : Ordinal.{0}} (hp : p ∈ items S K) :
    finitePart p = 0 ∨ K + 1 ≤ finitePart p := by
  rcases Finset.mem_union.mp hp with h | h
  · obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp h
    exact Or.inl (finitePart_limitPart s)
  · exact Or.inr (Finset.mem_filter.mp h).2

/-- The item count is at most `S.card` (one interval item per touched block, one singleton
item per high element). -/
theorem items_card_le : (items S K).card ≤ S.card := by
  refine (Finset.card_union_le _ _).trans ((Nat.add_le_add_right Finset.card_image_le _).trans ?_)
  rw [Finset.filter_congr (p := fun s => K + 1 ≤ finitePart s)
    (q := fun s => ¬ finitePart s ≤ K) (fun _ _ => by omega)]
  exact (Finset.card_filter_add_card_filter_not _).le

/-- The **rank** of `x`: the number of items `≤ x`. -/
def rank (S : Finset Ordinal.{0}) (K : ℕ) (x : Ordinal.{0}) : ℕ :=
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
    (hpx : x < p) (hpy : p ≤ y) : rank S K x < rank S K y :=
  Finset.card_lt_card ⟨fun _ hq => Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hq).1, (Finset.mem_filter.mp hq).2.trans hxy⟩,
    fun hsub => hpx.not_ge (Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨hp, hpy⟩))).2⟩

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
  · exact ((eq_limitPart_of_finitePart_eq_zero h0).symm.trans hblock).not_gt hpx
  · have hlt : limitPart p + (i : Ordinal) < p := by
      conv_rhs => rw [← decomposition p]
      exact add_lt_add_right (Nat.cast_lt.mpr (lt_of_le_of_lt hi (Nat.lt_of_succ_le hhigh))) _
    exact (hblock ▸ hlt).not_ge hpy

/-! ### The canonical normalizer -/

/-- Self-visibility of coded values: `ω·u + m` is self-visible at every threshold `≤ m`. -/
theorem code_selfVis {u : Ordinal.{0}} {m k : ℕ} (h : k ≤ m) :
    extVisibilityReplace (ofOrd (Ordinal.omega0 * u + m)) k k
      = ofOrd (Ordinal.omega0 * u + m) :=
  (extVisibilityReplace_self_iff _ _).mpr
    (Or.inr (Or.inr ⟨_, rfl, by rw [finitePart_code]; exact h⟩))

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
def canonicalNormalizer (S : Finset Ordinal.{0}) (K : ℕ) : ExtOrd → ExtOrd
  | ⊥ => ⊥
  | some ⊤ => ofOrd (Ordinal.omega0 * (items S K).card + ((K + 1 : ℕ) : Ordinal))
  | some (some x) =>
    if (∃ p ∈ items S K, limitPart p = limitPart x) ∧
        ∀ p ∈ items S K, limitPart p = limitPart x → x < p then
      ofOrd (Ordinal.omega0 * rank S K x + K)
    else if limitPart x ∈ items S K ∧ finitePart x ≤ K then
      ofOrd (Ordinal.omega0 * (rank S K x - 1 : ℕ) + finitePart x)
    else if rank S K x = 0 then ⊥
    else ofOrd (Ordinal.omega0 * (rank S K x - 1 : ℕ) + ((K + 1 : ℕ) : Ordinal))

@[simp] theorem canonicalNormalizer_bot : canonicalNormalizer S K ⊥ = ⊥ := rfl

@[simp] theorem canonicalNormalizer_top :
    canonicalNormalizer S K ⊤ = ofOrd (Ordinal.omega0 * (items S K).card + ((K + 1 : ℕ) : Ordinal)) := rfl

theorem canonicalNormalizer_ofOrd (x : Ordinal.{0}) :
    canonicalNormalizer S K (ofOrd x) =
      if (∃ p ∈ items S K, limitPart p = limitPart x) ∧
          ∀ p ∈ items S K, limitPart p = limitPart x → x < p then
        ofOrd (Ordinal.omega0 * rank S K x + K)
      else if limitPart x ∈ items S K ∧ finitePart x ≤ K then
        ofOrd (Ordinal.omega0 * (rank S K x - 1 : ℕ) + finitePart x)
      else if rank S K x = 0 then ⊥
      else ofOrd (Ordinal.omega0 * (rank S K x - 1 : ℕ) + ((K + 1 : ℕ) : Ordinal)) := rfl

/-- The **affine branch**: on the sub-`K` part of an interval-item block, `ν` shifts the
block affinely to code block `rank − 1`. -/
theorem canonicalNormalizer_affine {x : Ordinal.{0}} (hmem : limitPart x ∈ items S K)
    (hfp : finitePart x ≤ K) :
    canonicalNormalizer S K (ofOrd x)
      = ofOrd (Ordinal.omega0 * (rank S K x - 1 : ℕ) + finitePart x) := by
  have hno3b : ¬ ((∃ p ∈ items S K, limitPart p = limitPart x) ∧
      ∀ p ∈ items S K, limitPart p = limitPart x → x < p) :=
    fun ⟨_, hall⟩ => (hall (limitPart x) hmem (limitPart_idem x)).not_ge (limitPart_le x)
  rw [canonicalNormalizer_ofOrd, ite_eq_right hno3b, ite_eq_left ⟨hmem, hfp⟩]

/-- The **plateau branch**: the code of the greatest item `≤ x`, at offset `K+1`. -/
theorem canonicalNormalizer_plateau {x : Ordinal.{0}}
    (h3b : ¬ ((∃ p ∈ items S K, limitPart p = limitPart x) ∧
        ∀ p ∈ items S K, limitPart p = limitPart x → x < p))
    (haff : ¬ (limitPart x ∈ items S K ∧ finitePart x ≤ K)) (h0 : rank S K x ≠ 0) :
    canonicalNormalizer S K (ofOrd x)
      = ofOrd (Ordinal.omega0 * (rank S K x - 1 : ℕ) + ((K + 1 : ℕ) : Ordinal)) := by
  rw [canonicalNormalizer_ofOrd, ite_eq_right h3b, ite_eq_right haff, ite_eq_right h0]

/-- **`⊥`-fiber characterization**: `ν` sends an ordinal to `⊥` exactly when no item is
`≤ x` and no item shares `x`'s block.  In particular the `⊥`-fiber is a downward-closed
union of whole blocks. -/
theorem canonicalNormalizer_eq_bot_iff {x : Ordinal.{0}} :
    canonicalNormalizer S K (ofOrd x) = ⊥ ↔
      rank S K x = 0 ∧ ¬ ∃ p ∈ items S K, limitPart p = limitPart x := by
  rw [canonicalNormalizer_ofOrd]
  split_ifs with h1 h2 h3 <;> simp only [ofOrd_ne_bot, false_iff, true_iff, not_and, not_not]
  · exact fun _ => h1.1
  · exact fun _ => ⟨limitPart x, h2.1, limitPart_idem x⟩
  · exact ⟨h3, fun hp => h1 ⟨hp, fun p hp' _ => not_le.mp (rank_eq_zero_iff.mp h3 p hp')⟩⟩
  · exact fun h => absurd h h3

/-- **The block bound** (note §3): the block indices of `ν_{S,K}` form an initial segment of
length at most `(items S K).card + 1 ≤ S.card + 1`. -/
theorem canonicalNormalizer_blockIdx_le (x : ExtOrd) :
    canonicalNormalizer S K x = ⊥ ∨ ∃ u m : ℕ, u ≤ (items S K).card ∧ m ≤ K + 1 ∧
      canonicalNormalizer S K x = ofOrd (Ordinal.omega0 * u + m) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨ξ, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨(items S K).card, K + 1, le_rfl, le_rfl, rfl⟩
  · rw [canonicalNormalizer_ofOrd]
    split_ifs with h1 h2 h3
    · exact Or.inr ⟨rank S K ξ, K, rank_le_card ξ, Nat.le_succ K, rfl⟩
    · exact Or.inr ⟨rank S K ξ - 1, finitePart ξ,
        le_trans (Nat.sub_le _ 1) (rank_le_card ξ), le_trans h2.2 (Nat.le_succ K), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨rank S K ξ - 1, K + 1,
        le_trans (Nat.sub_le _ 1) (rank_le_card ξ), le_rfl, rfl⟩

/-- Every value of `ν_{S,K}` is at most the top code (the value of `⊤`). -/
theorem canonicalNormalizer_le_top (x : ExtOrd) :
    canonicalNormalizer S K x ≤ canonicalNormalizer S K ⊤ := by
  rcases canonicalNormalizer_blockIdx_le (S := S) (K := K) x with h | ⟨u, m, hu, hm, h⟩
  · simp [h]
  · rw [h, canonicalNormalizer_top]
    exact ofOrd_le_ofOrd.mpr (code_le_code (Nat.cast_le.mpr hu) hm)

/-! ### Monotonicity of the canonical normalizer -/

private theorem code_le_canonicalNormalizer {x y : Ordinal.{0}} {m : ℕ}
    (hxy : x ≤ y) (h0 : rank S K x ≠ 0) (hm : m ≤ K + 1)
    (haff : limitPart y = limitPart x → limitPart y ∈ items S K → finitePart y ≤ K →
      m ≤ finitePart y) :
    ofOrd (Ordinal.omega0 * (rank S K x - 1 : ℕ) + m) ≤ canonicalNormalizer S K (ofOrd y) := by
  have hry : rank S K x ≤ rank S K y := rank_mono hxy
  rw [canonicalNormalizer_ofOrd]
  split_ifs with h1y h2y h3y
  · exact ofOrd_le_ofOrd.mpr ((code_add_lt_mul (Nat.cast_lt.mpr (by omega)) m).le.trans
      (self_le_add_nat _ K))
  · rcases eq_or_lt_of_le (limitPart_mono hxy) with hsame | hlxy
    · exact ofOrd_le_ofOrd.mpr (code_le_code (Nat.cast_le.mpr (by omega))
        (haff hsame.symm h2y.1 h2y.2))
    · have := rank_lt_rank_of_item hxy h2y.1
        ((lt_limitPart_add_omega0 x).trans_le (limitPart_add_omega0_le hlxy)) (limitPart_le y)
      exact ofOrd_le_ofOrd.mpr ((code_add_lt_mul (Nat.cast_lt.mpr (by omega)) m).le.trans
        (self_le_add_nat _ _))
  · omega
  · exact ofOrd_le_ofOrd.mpr (code_le_code (Nat.cast_le.mpr (by omega)) hm)

/-- **The canonical normalizer is monotone** (clause 4 of Def. 2.3.9 for `ν_{S,K}`). -/
theorem canonicalNormalizer_mono : Monotone (canonicalNormalizer S K) := by
  intro a b hab
  rcases ExtOrd.cases a with rfl | rfl | ⟨x, rfl⟩
  · exact bot_le
  · rw [top_le_iff.mp hab]
  · rcases ExtOrd.cases b with rfl | rfl | ⟨y, rfl⟩
    · exact absurd hab (not_ofOrd_le_bot x)
    · exact canonicalNormalizer_le_top _
    · have hxy : x ≤ y := ofOrd_le_ofOrd.mp hab
      rw [canonicalNormalizer_ofOrd]
      split_ifs with h1x h2x h3x
      · rw [canonicalNormalizer_ofOrd]
        split_ifs with h1y h2y h3y
        · exact ofOrd_le_ofOrd.mpr (code_le_code (Nat.cast_le.mpr (rank_mono hxy)) le_rfl)
        all_goals
          obtain ⟨p₀, hp₀, hp₀lim⟩ := h1x.1
          have hry : rank S K x < rank S K y := by
            by_contra hle
            have hno (p) (hp : p ∈ items S K) (hxp : x < p) : y < p :=
              not_le.mp fun hpy => hle (rank_lt_rank_of_item hxy hp hxp hpy)
            have hsame : limitPart y = limitPart x :=
              le_antisymm (hp₀lim ▸ limitPart_mono (hno p₀ hp₀ (h1x.2 p₀ hp₀ hp₀lim)).le)
                (limitPart_mono hxy)
            exact h1y ⟨⟨p₀, hp₀, hp₀lim.trans hsame.symm⟩,
              fun p hp hpl => hno p hp (h1x.2 p hp (hpl.trans hsame))⟩
        · have hlxy : limitPart x < limitPart y := lt_of_le_of_ne (limitPart_mono hxy) fun h =>
            (h1x.2 _ (h ▸ h2y.1) (limitPart_idem x)).not_ge (limitPart_le x)
          have hp₀lt : p₀ < limitPart y :=
            (hp₀lim ▸ lt_limitPart_add_omega0 p₀).trans_le (limitPart_add_omega0_le hlxy)
          have := rank_lt_rank_of_item (h1x.2 p₀ hp₀ hp₀lim).le hp₀ (h1x.2 p₀ hp₀ hp₀lim) le_rfl
          have := rank_lt_rank_of_item (hp₀lt.le.trans (limitPart_le y)) h2y.1 hp₀lt (limitPart_le y)
          exact ofOrd_le_ofOrd.mpr ((code_add_lt_mul (Nat.cast_lt.mpr (by omega)) K).le.trans
            (self_le_add_nat _ _))
        · omega
        · exact ofOrd_le_ofOrd.mpr (code_le_code (Nat.cast_le.mpr (by omega)) (Nat.le_succ K))
      · exact code_le_canonicalNormalizer hxy
          (Nat.one_le_iff_ne_zero.mp (rank_pos_of_item h2x.1 (limitPart_le x)))
          (h2x.2.trans (Nat.le_succ K)) fun hsame _ _ => finitePart_le_of_le hsame.symm hxy
      · exact bot_le
      · exact code_le_canonicalNormalizer hxy h3x le_rfl fun hsame hmy hfpy =>
          absurd ⟨hsame ▸ hmy, (finitePart_le_of_le hsame.symm hxy).trans hfpy⟩ h2x

/-! ### The canonical decoder: item enumeration -/

/-- The natural number represented by an ordinal `< ω` (junk above). -/
def ordToNat (o : Ordinal.{0}) : ℕ := Cardinal.toNat o.card

@[simp] theorem ordToNat_natCast (n : ℕ) : ordToNat (n : Ordinal.{0}) = n := by
  rw [ordToNat, Ordinal.card_nat, Cardinal.toNat_natCast]

theorem ordToNat_cast_eq {o : Ordinal.{0}} (h : o < Ordinal.omega0) :
    ((ordToNat o : ℕ) : Ordinal.{0}) = o := by
  obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp h
  rw [ordToNat_natCast]

/-- The index of an item: the number of items strictly below it. -/
def idx (S : Finset Ordinal.{0}) (K : ℕ) (p : Ordinal.{0}) : ℕ :=
  ((items S K).filter fun q => q < p).card

theorem idx_lt_card {p : Ordinal.{0}} (hp : p ∈ items S K) :
    idx S K p < (items S K).card :=
  Finset.card_lt_card ⟨Finset.filter_subset _ _, fun hsub =>
    absurd (Finset.mem_filter.mp (hsub hp)).2 (lt_irrefl p)⟩

theorem idx_lt_idx {p q : Ordinal.{0}} (hp : p ∈ items S K) (hpq : p < q) :
    idx S K p < idx S K q := by
  apply Finset.card_lt_card
  constructor
  · intro r hr
    rw [Finset.mem_filter] at hr ⊢
    exact ⟨hr.1, lt_trans hr.2 hpq⟩
  · intro hsub
    exact absurd (Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨hp, hpq⟩))).2
      (lt_irrefl p)

theorem item_eq_of_idx_eq {p q : Ordinal.{0}} (hp : p ∈ items S K) (hq : q ∈ items S K)
    (h : idx S K p = idx S K q) : p = q := by
  rcases lt_trichotomy p q with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (idx_lt_idx hp hlt))
  · exact heq
  · exact absurd h.symm (Nat.ne_of_lt (idx_lt_idx hq hgt))

/-- The rank of an item is its index plus one. -/
theorem rank_item {p : Ordinal.{0}} (hp : p ∈ items S K) :
    rank S K p = idx S K p + 1 := by
  have hins : ((items S K).filter fun q => q ≤ p) =
      insert p ((items S K).filter fun q => q < p) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_insert]
    exact ⟨fun ⟨hq, hqp⟩ => hqp.lt_or_eq.symm.imp id (⟨hq, ·⟩),
      by rintro (rfl | ⟨hq, hqp⟩); exacts [⟨hp, le_rfl⟩, ⟨hq, hqp.le⟩]⟩
  rw [rank, idx, hins]
  exact Finset.card_insert_of_notMem fun hmem => (Finset.mem_filter.mp hmem).2.false

/-- The `u`-th item in increasing order (junk `0` beyond the item count). -/
def itemOfIdx (S : Finset Ordinal.{0}) (K : ℕ) (u : ℕ) : Ordinal.{0} :=
  if h : u < (items S K).card then (items S K).orderEmbOfFin rfl ⟨u, h⟩ else 0

theorem itemOfIdx_mem {u : ℕ} (h : u < (items S K).card) : itemOfIdx S K u ∈ items S K := by
  rw [itemOfIdx, dite_eq_left h]
  exact Finset.orderEmbOfFin_mem _ _ _

/-- The enumeration inverts the index: the `u`-th item has index `u`. -/
theorem idx_itemOfIdx {u : ℕ} (h : u < (items S K).card) :
    idx S K (itemOfIdx S K u) = u := by
  rw [itemOfIdx, dite_eq_left h]
  set e := (items S K).orderEmbOfFin rfl with he
  have himg : ((items S K).filter fun q => q < e ⟨u, h⟩) =
      (Finset.Iio (⟨u, h⟩ : Fin (items S K).card)).image e := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Iio]
    refine ⟨fun ⟨hq, hlt⟩ => ?_, ?_⟩
    · obtain ⟨j, rfl⟩ : q ∈ Set.range e := by rwa [he, Finset.range_orderEmbOfFin]
      exact ⟨j, e.strictMono.lt_iff_lt.mp hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem _ _ _, e.strictMono hj⟩
  rw [idx, himg, Finset.card_image_of_injective _ e.injective, Fin.card_Iio]

/-- The index inverts the enumeration on items. -/
theorem itemOfIdx_idx {p : Ordinal.{0}} (hp : p ∈ items S K) :
    itemOfIdx S K (idx S K p) = p :=
  item_eq_of_idx_eq (itemOfIdx_mem (idx_lt_card hp)) hp (idx_itemOfIdx (idx_lt_card hp))

/-! ### The canonical decoder -/

/-- The sub-`K+1` value of a singleton code block: just below the item and above every
earlier item — `max (limitPart p + K) (the greatest item < p)`. -/
def decoderLow (S : Finset Ordinal.{0}) (K : ℕ) (p : Ordinal.{0}) :
    Ordinal.{0} :=
  max (limitPart p + K) (((items S K).filter fun q => q < p).sup id)

theorem le_decoderLow_left (p : Ordinal.{0}) :
    limitPart p + (K : Ordinal) ≤ decoderLow S K p := le_max_left _ _

theorem item_le_decoderLow {q p : Ordinal.{0}} (hq : q ∈ items S K) (hqp : q < p) :
    q ≤ decoderLow S K p :=
  (Finset.le_sup (f := id) (by rw [Finset.mem_filter]; exact ⟨hq, hqp⟩)).trans (le_max_right _ _)

theorem decoderLow_lt {p : Ordinal.{0}} (hp : K + 1 ≤ finitePart p) :
    decoderLow S K p < p := by
  have hp0 : (0 : Ordinal.{0}) < p := by
    refine lt_of_le_of_ne (Ordinal.bot_eq_zero ▸ bot_le) fun h => ?_
    have := finitePart_natCast 0
    rw [Nat.cast_zero, h] at this
    omega
  rw [decoderLow, max_lt_iff]
  refine ⟨?_, (Finset.sup_lt_iff (Ordinal.bot_eq_zero ▸ hp0)).mpr fun _ hq =>
    (Finset.mem_filter.mp hq).2⟩
  conv_rhs => rw [← decomposition p]
  exact add_lt_add_right (Nat.cast_lt.mpr (Nat.lt_of_succ_le hp)) _

theorem le_finitePart_decoderLow (p : Ordinal.{0}) :
    K ≤ finitePart (decoderLow S K p) := by
  rw [decoderLow]
  rcases max_cases (limitPart p + (K : Ordinal))
    (((items S K).filter fun q => q < p).sup id) with ⟨hm, -⟩ | ⟨hm, hlt⟩
  · rw [hm, finitePart_limitPart_add_nat]
  · rw [hm]
    have hne : ((items S K).filter fun q => q < p).Nonempty := by
      rcases Finset.eq_empty_or_nonempty ((items S K).filter fun q => q < p) with he | hne
      · rw [he, Finset.sup_empty, Ordinal.bot_eq_zero] at hlt
        exact absurd hlt (not_lt.mpr (Ordinal.bot_eq_zero ▸ bot_le))
      · exact hne
    obtain ⟨q, hqmem, hsup⟩ := Finset.exists_mem_eq_sup _ hne id
    rw [Finset.mem_filter] at hqmem
    rw [hsup, id_eq] at hlt ⊢
    have hqlim : limitPart q = limitPart p :=
      limitPart_eq_of_mem_block ((self_le_add_nat _ K).trans hlt.le)
        (hqmem.2.trans (lt_limitPart_add_omega0 p))
    rcases items_fp hqmem.1 with h0 | hhigh
    · exact absurd ((eq_limitPart_of_finitePart_eq_zero h0).symm.trans hqlim ▸ self_le_add_nat _ K)
        hlt.not_ge
    · omega

/-- The item owning the code block of `y`. -/
def blockItem (S : Finset Ordinal.{0}) (K : ℕ) (y : Ordinal.{0}) :
    Ordinal.{0} :=
  itemOfIdx S K (ordToNat (y / Ordinal.omega0))

/-- The **canonical decoder** `τ_{S,K}` (note §3), the mirror map on the code side: on the
code block of an item `p` — every block below `ω·(items S K).card` is one — it is affine back
onto `[p, p+K]` when `p` is an interval item (constant `p + K` on the plateau), and for a
singleton item it sends offset `≥ K+1` to `p` and the sub-`K+1` part to the constant
`decoderLow p`; everything at or beyond the top block decodes to `⊤`. -/
def canonicalDecoder (S : Finset Ordinal.{0}) (K : ℕ) : ExtOrd → ExtOrd
  | ⊥ => ⊥
  | some ⊤ => ⊤
  | some (some y) =>
    if y < Ordinal.omega0 * (items S K).card then
      if finitePart (blockItem S K y) = 0 then
        ofOrd (blockItem S K y + min (finitePart y) K)
      else if finitePart y ≤ K then ofOrd (decoderLow S K (blockItem S K y))
      else ofOrd (blockItem S K y)
    else ⊤

@[simp] theorem canonicalDecoder_bot : canonicalDecoder S K ⊥ = ⊥ := rfl

@[simp] theorem canonicalDecoder_top : canonicalDecoder S K ⊤ = ⊤ := rfl

theorem canonicalDecoder_ofOrd (y : Ordinal.{0}) :
    canonicalDecoder S K (ofOrd y) =
      if y < Ordinal.omega0 * (items S K).card then
        if finitePart (blockItem S K y) = 0 then
          ofOrd (blockItem S K y + min (finitePart y) K)
        else if finitePart y ≤ K then ofOrd (decoderLow S K (blockItem S K y))
        else ofOrd (blockItem S K y)
      else ⊤ := rfl

theorem canonicalDecoder_topRegion {y : Ordinal.{0}}
    (hy : ¬ y < Ordinal.omega0 * (items S K).card) :
    canonicalDecoder S K (ofOrd y) = ⊤ := by
  rw [canonicalDecoder_ofOrd, ite_eq_right hy]

theorem canonicalDecoder_interval {y : Ordinal.{0}}
    (hy : y < Ordinal.omega0 * (items S K).card) (h0 : finitePart (blockItem S K y) = 0) :
    canonicalDecoder S K (ofOrd y) = ofOrd (blockItem S K y + min (finitePart y) K) := by
  rw [canonicalDecoder_ofOrd, ite_eq_left hy, ite_eq_left h0]

theorem canonicalDecoder_singLow {y : Ordinal.{0}}
    (hy : y < Ordinal.omega0 * (items S K).card) (h0 : ¬ finitePart (blockItem S K y) = 0)
    (hfp : finitePart y ≤ K) :
    canonicalDecoder S K (ofOrd y) = ofOrd (decoderLow S K (blockItem S K y)) := by
  rw [canonicalDecoder_ofOrd, ite_eq_left hy, ite_eq_right h0, ite_eq_left hfp]

theorem canonicalDecoder_singHigh {y : Ordinal.{0}}
    (hy : y < Ordinal.omega0 * (items S K).card) (h0 : ¬ finitePart (blockItem S K y) = 0)
    (hfp : ¬ finitePart y ≤ K) :
    canonicalDecoder S K (ofOrd y) = ofOrd (blockItem S K y) := by
  rw [canonicalDecoder_ofOrd, ite_eq_left hy, ite_eq_right h0, ite_eq_right hfp]

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
  exact ⟨by exact_mod_cast hcast ▸ hdiv, by rw [hcast]; rfl⟩

/-! ### The canonical normalizer is a step shifter -/

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
    · exact code_selfVis (hk.trans (Nat.le_succ K))
    · have hfp : k ≤ finitePart ξ := by
        rcases (extVisibilityReplace_self_iff _ _).mp hx with h | h | ⟨α, hα, hα_fp⟩
        · exact absurd h (ofOrd_ne_bot ξ)
        · exact absurd h (ofOrd_ne_top ξ)
        · exact ofOrd_inj.mp hα ▸ hα_fp
      rw [canonicalNormalizer_ofOrd]
      split_ifs
      · exact code_selfVis hk
      · exact code_selfVis hfp
      · rfl
      · exact code_selfVis (hk.trans (Nat.le_succ K))
  blockwise := by
    intro ξ
    have hrk (i) (hi : i ≤ K) : rank S K (limitPart ξ) = rank S K (limitPart ξ + (i : ℕ)) :=
      rank_eq_of_forall (self_le_add_nat _ i) fun q hq => item_le_block_of_le hq hi
    by_cases hmem : limitPart ξ ∈ items S K
    · left
      refine ⟨Ordinal.omega0 * (rank S K (limitPart ξ) - 1 : ℕ), finitePart_omega0_mul _,
        fun i hi => ?_⟩
      rw [canonicalNormalizer_affine (by rwa [limitPart_limitPart_add_nat])
        (by rw [finitePart_limitPart_add_nat]; exact hi), ← hrk i hi, finitePart_limitPart_add_nat]
    · right
      refine ⟨canonicalNormalizer S K (ofOrd (limitPart ξ)), ?_, fun i hi => ?_⟩
      · rw [canonicalNormalizer_ofOrd]
        split_ifs with h1 h2
        · exact code_selfVis le_rfl
        · exact absurd (limitPart_idem ξ ▸ h2.1) hmem
        · rfl
        · exact code_selfVis (Nat.le_succ K)
      · have hlt (p) (hp : p ∈ items S K) : limitPart ξ + (i : ℕ) < p ↔ limitPart ξ < p :=
          not_le.symm.trans ((Iff.intro (item_le_block_of_le hp hi)
            fun h => h.trans (self_le_add_nat _ i)).not.trans not_le)
        simp only [canonicalNormalizer_ofOrd, limitPart_limitPart_add_nat, limitPart_idem,
          ← hrk i hi, hmem, false_and, ↓reduceIte]
        congr 1; exact propext (and_congr_right'
          (forall₂_congr fun p hp => imp_congr_right fun _ => hlt p hp))
  bot_blocks := by
    intro ξ ζ hlim hbot
    rw [canonicalNormalizer_eq_bot_iff] at hbot ⊢
    obtain ⟨h0, hb⟩ := hbot
    refine ⟨rank_eq_zero_iff.mpr fun p hp hpz => ?_, fun ⟨p, hp, hpl⟩ => hb ⟨p, hp, hpl.trans hlim.symm⟩⟩
    by_cases hpl : limitPart p = limitPart ζ
    · exact hb ⟨p, hp, hpl.trans hlim.symm⟩
    · exact rank_eq_zero_iff.mp h0 p hp (lt_of_limitPart_lt (hlim ▸ lt_of_le_of_ne (limitPart_mono hpz) hpl)).le

/-! ### The canonical decoder is a step shifter -/

theorem itemOfIdx_lt {u v : ℕ} (hv : v < (items S K).card) (huv : u < v) :
    itemOfIdx S K u < itemOfIdx S K v := by
  rw [itemOfIdx, itemOfIdx, dite_eq_left (lt_trans huv hv), dite_eq_left hv]
  exact ((items S K).orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr huv)

theorem div_omega0_eq_of_limitPart_eq {x y : Ordinal.{0}} (h : limitPart x = limitPart y) :
    x / Ordinal.omega0 = y / Ordinal.omega0 :=
  (Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono.injective h

/-- **The canonical decoder is monotone** (clause 4 of Def. 2.3.9 for `τ_{S,K}`). -/
theorem canonicalDecoder_mono : Monotone (canonicalDecoder S K) := by
  intro a b hab
  rcases ExtOrd.cases a with rfl | rfl | ⟨y, rfl⟩
  · exact bot_le
  · rw [top_le_iff.mp hab]
  · rcases ExtOrd.cases b with rfl | rfl | ⟨y', rfl⟩
    · exact absurd hab (not_ofOrd_le_bot y)
    · exact le_top
    · have hyy : y ≤ y' := ofOrd_le_ofOrd.mp hab
      by_cases hy' : y' < Ordinal.omega0 * (items S K).card
      case neg => rw [canonicalDecoder_topRegion hy']; exact le_top
      have hy : y < Ordinal.omega0 * (items S K).card := lt_of_le_of_lt hyy hy'
      obtain ⟨hu, hlimy⟩ := blockIdx_lt hy
      obtain ⟨hu', hlimy'⟩ := blockIdx_lt hy'
      have hpmem : blockItem S K y ∈ items S K := itemOfIdx_mem hu
      have hp'mem : blockItem S K y' ∈ items S K := itemOfIdx_mem hu'
      have hfp_high (h0 : ¬ finitePart (blockItem S K y) = 0) : K + 1 ≤ finitePart (blockItem S K y) :=
        (items_fp hpmem).resolve_left h0
      have hfp'_high (h0 : ¬ finitePart (blockItem S K y') = 0) : K + 1 ≤ finitePart (blockItem S K y') :=
        (items_fp hp'mem).resolve_left h0
      have huu : ordToNat (y / Ordinal.omega0) ≤ ordToNat (y' / Ordinal.omega0) :=
        Nat.cast_le.mp ((Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono.le_iff_le.mp
          (hlimy ▸ hlimy' ▸ limitPart_mono hyy))
      rcases Nat.lt_or_ge (ordToNat (y / Ordinal.omega0)) (ordToNat (y' / Ordinal.omega0))
        with hlt | hge
      · have hpp' : blockItem S K y < blockItem S K y' := itemOfIdx_lt hu' hlt
        have hhi : canonicalDecoder S K (ofOrd y) ≤
            ofOrd (if finitePart (blockItem S K y) = 0
              then blockItem S K y + (K : Ordinal) else blockItem S K y) := by
          rw [canonicalDecoder_ofOrd, ite_eq_left hy]
          split_ifs with h0
          · exact ofOrd_le_ofOrd.mpr (add_le_add_right (Nat.cast_le.mpr (min_le_right _ _)) _)
          · exact ofOrd_le_ofOrd.mpr (decoderLow_lt (hfp_high h0)).le
          · exact le_rfl
        have hlo : ofOrd (if finitePart (blockItem S K y') = 0 then blockItem S K y'
            else decoderLow S K (blockItem S K y')) ≤ canonicalDecoder S K (ofOrd y') := by
          rw [canonicalDecoder_ofOrd, ite_eq_left hy']
          split_ifs with h0'
          · exact ofOrd_le_ofOrd.mpr (self_le_add_nat _ _)
          · exact le_rfl
          · exact ofOrd_le_ofOrd.mpr (decoderLow_lt (hfp'_high h0')).le
        refine hhi.trans ((ofOrd_le_ofOrd.mpr ?_).trans hlo)
        split_ifs with h0 h0' h0'
        · have hplim := eq_limitPart_of_finitePart_eq_zero h0
          have hplim' := eq_limitPart_of_finitePart_eq_zero h0'
          have hstep := limitPart_add_omega0_le (hplim.symm ▸ hplim'.symm ▸ hpp')
          rw [hplim, hplim'] at hstep
          exact ((add_lt_add_right (Ordinal.natCast_lt_omega0 K) _).trans_le hstep).le
        · exact (add_le_add (eq_limitPart_of_finitePart_eq_zero h0 ▸ limitPart_mono hpp'.le)
            le_rfl).trans (le_decoderLow_left _)
        · exact hpp'.le
        · exact item_le_decoderLow hpmem hpp'
      · have hueq : ordToNat (y / Ordinal.omega0) = ordToNat (y' / Ordinal.omega0) :=
          le_antisymm huu hge
        have hpe : blockItem S K y = blockItem S K y' := by rw [blockItem, blockItem, hueq]
        have hfyy : finitePart y ≤ finitePart y' :=
          finitePart_le_of_le (by rw [hlimy, hlimy', hueq]) hyy
        rw [canonicalDecoder_ofOrd, canonicalDecoder_ofOrd, ite_eq_left hy, ite_eq_left hy', ← hpe]
        split_ifs with h0
        · exact ofOrd_le_ofOrd.mpr (add_le_add_right (Nat.cast_le.mpr (min_le_min hfyy le_rfl)) _)
        · exact le_rfl
        · exact ofOrd_le_ofOrd.mpr (decoderLow_lt (hfp_high h0)).le
        · omega
        · exact le_rfl

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
    · have hfp : k ≤ finitePart y := by
        rcases (extVisibilityReplace_self_iff _ _).mp hx with h | h | ⟨α, hα, hα_fp⟩
        · exact absurd h (ofOrd_ne_bot y)
        · exact absurd h (ofOrd_ne_top y)
        · exact ofOrd_inj.mp hα ▸ hα_fp
      by_cases hy : y < Ordinal.omega0 * (items S K).card
      case neg => rw [canonicalDecoder_topRegion hy]; rfl
      obtain ⟨hu, -⟩ := blockIdx_lt hy
      have hpmem : blockItem S K y ∈ items S K := itemOfIdx_mem hu
      rw [canonicalDecoder_ofOrd, ite_eq_left hy]
      split_ifs with h0 hfpy <;>
        refine (extVisibilityReplace_self_iff _ _).mpr (Or.inr (Or.inr ⟨_, rfl, ?_⟩))
      · rw [← eq_limitPart_of_finitePart_eq_zero h0, finitePart_limitPart_add_nat]
        exact le_min hfp hk
      · exact hk.trans (le_finitePart_decoderLow _)
      · have := (items_fp hpmem).resolve_left h0; omega
  blockwise := by
    intro ξ
    by_cases hy : limitPart ξ < Ordinal.omega0 * (items S K).card
    case neg =>
      exact Or.inr ⟨⊤, extVisibilityReplace_top K K, fun i _ =>
        canonicalDecoder_topRegion (not_lt.mpr ((not_lt.mp hy).trans (self_le_add_nat _ i)))⟩
    · have hyi (i : ℕ) : limitPart ξ + (i : Ordinal) < Ordinal.omega0 * (items S K).card := by
        refine (add_lt_add_right (Ordinal.natCast_lt_omega0 i) _).trans_le ?_
        have h2 := limitPart_add_omega0_le
          (by rwa [limitPart_idem, limitPart_omega0_mul] :
            limitPart (limitPart ξ) < limitPart (Ordinal.omega0 * ((items S K).card : Ordinal)))
        rwa [limitPart_idem, limitPart_omega0_mul] at h2
      have hblockItem (i : ℕ) :
          blockItem S K (limitPart ξ + (i : ℕ)) = blockItem S K (limitPart ξ) := by
        rw [blockItem, blockItem, div_omega0_eq_of_limitPart_eq
          ((limitPart_limitPart_add_nat ξ i).trans (limitPart_idem ξ).symm)]
      by_cases h0 : finitePart (blockItem S K (limitPart ξ)) = 0
      · refine Or.inl ⟨blockItem S K (limitPart ξ), h0, fun i hi => ?_⟩
        rw [canonicalDecoder_interval (hyi i) (by rw [hblockItem i]; exact h0),
          hblockItem i, finitePart_limitPart_add_nat, min_eq_left hi]
      · refine Or.inr ⟨ofOrd (decoderLow S K (blockItem S K (limitPart ξ))),
          (extVisibilityReplace_self_iff _ _).mpr
            (Or.inr (Or.inr ⟨_, rfl, le_finitePart_decoderLow _⟩)), fun i hi => ?_⟩
        rw [canonicalDecoder_singLow (hyi i) (by rw [hblockItem i]; exact h0)
          (by rw [finitePart_limitPart_add_nat]; exact hi), hblockItem i]
  bot_blocks := by
    intro ξ _ _ hbot
    rw [canonicalDecoder_ofOrd] at hbot
    split_ifs at hbot <;> simp at hbot

/-! ### The retraction: decoding inverts encoding on tracked labels -/

/-- `τ_{S,K} ∘ ν_{S,K}` is the identity on `⊥`, `⊤`, and the tracked ordinals `S`. -/
theorem canonicalDecoder_canonicalNormalizer {x : ExtOrd}
    (hx : x = ⊥ ∨ x = ⊤ ∨ ∃ s ∈ S, x = ofOrd s) :
    canonicalDecoder S K (canonicalNormalizer S K x) = x := by
  rcases hx with rfl | rfl | ⟨s, hs, rfl⟩
  · rfl
  · rw [canonicalNormalizer_top]
    exact canonicalDecoder_topRegion (not_lt.mpr (self_le_add_nat _ _))
  · by_cases hfp : finitePart s ≤ K
    · have hmem : limitPart s ∈ items S K := limitPart_mem_items hs hfp
      have hrk : rank S K s - 1 = idx S K (limitPart s) := by
        rw [← rank_eq_of_forall (limitPart_le s) fun p hp hpy =>
          item_le_block_of_le hp hfp (by rwa [decomposition]), rank_item hmem]
        omega
      have hylt : Ordinal.omega0 * (idx S K (limitPart s) : Ordinal) + (finitePart s : Ordinal)
          < Ordinal.omega0 * ((items S K).card : Ordinal) :=
        code_add_lt_mul (Nat.cast_lt.mpr (idx_lt_card hmem)) _
      have hbi : blockItem S K
          (Ordinal.omega0 * (idx S K (limitPart s) : Ordinal) + (finitePart s : Ordinal))
          = limitPart s := by rw [blockItem_code, itemOfIdx_idx hmem]
      rw [canonicalNormalizer_affine hmem hfp, hrk,
        canonicalDecoder_interval hylt (by rw [hbi]; exact finitePart_limitPart s), hbi,
        finitePart_code, min_eq_left hfp, decomposition]
    · rw [not_le] at hfp
      have hmem : s ∈ items S K := mem_items_of_high hs hfp
      have h3b : ¬ ((∃ p ∈ items S K, limitPart p = limitPart s) ∧
          ∀ p ∈ items S K, limitPart p = limitPart s → s < p) :=
        fun ⟨_, hall⟩ => (hall s hmem rfl).false
      have haff : ¬ (limitPart s ∈ items S K ∧ finitePart s ≤ K) := fun ⟨_, h⟩ => by omega
      have h0 : rank S K s ≠ 0 := Nat.one_le_iff_ne_zero.mp (rank_pos_of_item hmem le_rfl)
      have hidx : rank S K s - 1 = idx S K s := by rw [rank_item hmem]; omega
      have hylt : Ordinal.omega0 * (idx S K s : Ordinal) + ((K + 1 : ℕ) : Ordinal)
          < Ordinal.omega0 * ((items S K).card : Ordinal) :=
        code_add_lt_mul (Nat.cast_lt.mpr (idx_lt_card hmem)) _
      have hbi : blockItem S K
          (Ordinal.omega0 * (idx S K s : Ordinal) + ((K + 1 : ℕ) : Ordinal)) = s := by
        rw [blockItem_code, itemOfIdx_idx hmem]
      rw [canonicalNormalizer_plateau h3b haff h0, hidx,
        canonicalDecoder_singHigh hylt (by rw [hbi]; omega) (by rw [finitePart_code]; omega), hbi]

/-! ### The NF Lemma (note §3, Lemma 3.A; faithful Lemmas 2.3.3/2.3.15) -/

end Transform

/-! ### The finite coded inventory, combinatorial level (note §4) -/

namespace ExtOrd

/-- The **coded alphabet** at block bound `t` and grade bound `K` (note §§3–4): `⊥` together
with the codes `ω·u + m`, `u ≤ t`, `m ≤ K+1` — a `Finset`. -/
def codedAlphabet (t K : ℕ) : Finset ExtOrd :=
  insert ⊥ ((Finset.range (t + 1) ×ˢ Finset.range (K + 2)).image
    fun um => ofOrd (Ordinal.omega0 * um.1 + um.2))

theorem mem_codedAlphabet_iff {t K : ℕ} {x : ExtOrd} :
    x ∈ codedAlphabet t K ↔
      x = ⊥ ∨ ∃ u m : ℕ, u ≤ t ∧ m ≤ K + 1 ∧ x = ofOrd (Ordinal.omega0 * u + m) := by
  simp only [codedAlphabet, Finset.mem_insert, Finset.mem_image, Finset.mem_product,
    Finset.mem_range, Prod.exists, Nat.lt_succ_iff, and_assoc, eq_comm (b := x)]

/-- **The finite inventory at the combinatorial level** (note §4; the counting content of
Lemmas 4.3.4/4.3.9/4.3.11): over a finite family, the labellings with values in the coded
alphabet form a finite set. -/
theorem codedLabellings_finite (D : Type*) [Finite D] (t K : ℕ) :
    {F : D → ExtOrd | ∀ d, F d ∈ codedAlphabet t K}.Finite :=
  (Set.Finite.pi fun _ : D => (codedAlphabet t K).finite_toSet).subset fun _ hF d _ => hF d

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
