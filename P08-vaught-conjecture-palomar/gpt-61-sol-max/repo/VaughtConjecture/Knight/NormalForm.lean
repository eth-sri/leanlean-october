
import VaughtConjecture.Knight.PointwiseLabels
import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import Mathlib.Order.Interval.Finset.Fin
import VaughtConjecture.Knight.SemScheme

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

namespace VaughtConjecture.Knight

open Value ExtOrd

/-! ### Label arithmetic: ω-blocks and codes -/

namespace Value

/-- Self-visibility at `k` fixes every replacement value, not just `k`:
if `γ = γ ⊔⁺_k k` then `γ = γ ⊔⁺_k i` for every `i`. -/
theorem extVisReplace_eq_self_of_selfVis {v} {k}
    (h : extVisibilityReplace v k k = v) i : extVisibilityReplace v k i = v := by
  rcases (extVisibilityReplace_self_iff v k).mp h with rfl | rfl | ⟨α, rfl, hfp⟩
  · rfl
  · rfl
  · simp_all [visibilityReplace]

/-- The finite part of a natural number is itself. -/
theorem finitePart_natCast (n : ℕ) : finitePart (n : Ordinal₀) = n := by simp_all [VaughtConjecture.Knight.Value.finitePart]

/-- The limit part of a natural number is zero. -/
theorem limitPart_natCast (n : ℕ) : limitPart (n : Ordinal₀) = 0 := by
  unfold limitPart
  rw [Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 n), mul_zero]

/-- `ω * u` is its own limit part. -/
theorem limitPart_omega0_mul u :
    limitPart (Ordinal.omega0 * u) = Ordinal.omega0 * u := by
  unfold limitPart
  rw [Ordinal.mul_div_cancel u Ordinal.omega0_ne_zero]

/-- The limit part of the code `ω * u + m` is `ω * u`. -/
theorem limitPart_code (u : Ordinal₀) (m : ℕ) :
    limitPart (Ordinal.omega0 * u + m) = Ordinal.omega0 * u := by
  conv_lhs => rw [← limitPart_omega0_mul u]
  rw [limitPart_limitPart_add_nat, limitPart_omega0_mul]

/-- The finite part of the code `ω * u + m` is `m`. -/
theorem finitePart_code (u : Ordinal₀) (m : ℕ) :
    finitePart (Ordinal.omega0 * u + m) = m := by
  conv_lhs => rw [← limitPart_omega0_mul u]
  rw [finitePart_limitPart_add_nat]

/-- An ordinal with finite part `0` is its own limit part. -/
def eq_limitPart_of_finitePart_eq_zero {β} (h : finitePart β = 0) := by
  have := decomposition β
  rwa [h, Nat.cast_zero, add_zero] at this

/-- A block member `x` lies below the next block level: `x < limitPart x + ω`. -/
theorem lt_limitPart_add_omega0 x : x < limitPart x + Ordinal.omega0 := by
  conv_lhs => rw [← decomposition x]
  exact add_lt_add_right (Ordinal.natCast_lt_omega0 _) _

/-- Distinct limit parts are at least a block apart:
if `limitPart x < limitPart y` then `limitPart x + ω ≤ limitPart y`. -/
theorem limitPart_add_omega0_le {x y} (h : limitPart x < limitPart y) :
    limitPart x + Ordinal.omega0 ≤ limitPart y := by
  
  have hdiv  :=
    (Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono.lt_iff_lt.mp h
  calc Ordinal.omega0 * (x / Ordinal.omega0) + Ordinal.omega0
      = Ordinal.omega0 * Order.succ (x / Ordinal.omega0) := (Ordinal.mul_succ _ _).symm
    _ ≤ Ordinal.omega0 * (y / Ordinal.omega0) :=
        (Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono.monotone
          (Order.succ_le_of_lt hdiv)

/-- Strict block comparison: a member of an earlier block is below every member of a later
block. -/
def lt_of_limitPart_lt {x y} (h : limitPart x < limitPart y) :=
  lt_of_lt_of_le ((lt_limitPart_add_omega0 x).trans_le (limitPart_add_omega0_le h))
    ((limitPart_le).trans le_rfl)

/-- Code comparison, strict, across blocks: `ω·u + m < ω·v + n` when `u < v`. -/
theorem code_lt_code_of_lt {u v : Ordinal₀} (h : u < v) (m n : ℕ) :
    Ordinal.omega0 * u + m < Ordinal.omega0 * v + n := by simp_all [lt_of_limitPart_lt, limitPart_code]

/-- Code comparison, non-strict: `ω·u + m ≤ ω·v + n` when `u ≤ v` and `m ≤ n`. -/
theorem code_le_code {u v : Ordinal₀} (h : u ≤ v) {m n : ℕ} (hmn : m ≤ n) :
    Ordinal.omega0 * u + m ≤ Ordinal.omega0 * v + n := by simp_all [add_le_add]

/-- `min` preserves self-visibility (a `min` of two self-visible labels is one of them). -/
theorem extVisReplace_min_self {x y} {k}
    (hx : extVisibilityReplace x k k = x) (hy : extVisibilityReplace y k k = y) :
    extVisibilityReplace (min x y) k k = min x y := by grind

end Value

namespace Transform

/-! ### The step suppressor and step shifters -/

/-- The **step suppressor** `g_K` (note §3): `⊤` at thresholds `≤ K`, `⊥` above. -/
def stepSuppressor (K : ℕ) : ℕ → ExtOrd := fun k => if k ≤ K then ⊤ else ⊥

@[simp] theorem stepSuppressor_of_le {K k} (h : k ≤ K) : stepSuppressor K k = ⊤ :=
  ite_eq_left h

@[simp] theorem stepSuppressor_of_gt {K k} (h : K < k) : stepSuppressor K k = ⊥ :=
  ite_eq_right (not_le.mpr h)

theorem stepSuppressor_antitone K :
    ∀ n m , n < m → stepSuppressor K m ≤ stepSuppressor K n := by
  intro n m hnm
  unfold stepSuppressor
  split_ifs with hm hn hn
  · exact le_rfl
  · omega
  · exact bot_le
  · exact le_rfl

theorem stepSuppressor_selfVis K :
    ∀ n , stepSuppressor K n = extVisibilityReplace (stepSuppressor K n) n n := by
  intro n
  unfold stepSuppressor
  split_ifs <;> rfl

/-- A **`K`-step shifter** (the legality pattern of the note's §3, shared by the canonical
normalizer and decoder): a label map `σ` that fixes `⊥`, is monotone, preserves
self-visibility at every threshold `≤ K`, is **affine or constant on the sub-`K` part of
every ω-block** (affine onto a block start `β`, or constant at a label self-visible at `K`),
and whose **`⊥`-fiber is closed under whole blocks**.  These five conditions make `(g_K, σ)`
a legal Def. 2.3.9 witness pair (`IsStepShifter.clause5`, `IsStepShifter.transformsTo`). -/
structure IsStepShifter (K : ℕ) (σ : LabelMap) : Prop where
  /-- `σ` fixes the bottom label (clause 3). -/
  map_bot : σ ⊥ = ⊥
  /-- `σ` is monotone (clause 4). -/
  mono : Monotone σ
  /-- `σ` preserves self-visibility at every threshold `≤ K`. -/
  selfVis : ∀ x k, k ≤ K → extVisibilityReplace x k k = x →
    extVisibilityReplace (σ x) k k = σ x
  /-- On the sub-`K` part `{limitPart ξ + i : i ≤ K}` of every block, `σ` is affine onto a
  block start (`finitePart β = 0`) or constant at a label self-visible at `K`. -/
  blockwise : ∀ ξ ,
    (∃ β , finitePart β = 0 ∧
      ∀ i , i ≤ K → σ (ofOrd (limitPart ξ + i)) = ofOrd (β + i)) ∨
    (∃ c , extVisibilityReplace c K K = c ∧
      ∀ i , i ≤ K → σ (ofOrd (limitPart ξ + i)) = c)
  /-- The `⊥`-fiber of `σ` on ordinals is a union of whole blocks. -/
  bot_blocks : ∀ ξ ζ , limitPart ξ = limitPart ζ →
    σ (ofOrd ξ) = ⊥ → σ (ofOrd ζ) = ⊥

/-- **The clause-5 case split, compiled once** (note §3): a `K`-step shifter satisfies
clause 5 of Def. 2.3.9 for the step suppressor `g_K`.  For `k ≤ K` the commutation is
**unguarded**: on self-visible labels both sides are fixed (self-visibility is preserved);
on the sub-`K` part of a block, affine pieces commute with `⊔⁺_k i` and constants are
`⊔⁺_k`-fixed.  For `k > K` the guard `σ α ≤ g_K k = ⊥` pins `σ α = ⊥`, and the
`⊔⁺_k`-orbit of `α` stays in `α`'s block, hence in the `⊥`-fiber (block closure). -/
theorem IsStepShifter.clause5 {K} {σ} (h : IsStepShifter K σ) :
    ∀ α k, σ α ≤ stepSuppressor K k → ∀ i , i ≤ k →
      σ (extVisibilityReplace α k i) = extVisibilityReplace (σ α) k i := by
  intro α k hguard i hi
  by_cases hk : k ≤ K
  · -- thresholds `k ≤ K`: unguarded commutation
    rcases ExtOrd.cases α with rfl | rfl | ⟨ξ, rfl⟩
    · rw [extVisibilityReplace_bot, h.map_bot, extVisibilityReplace_bot]
    · rw [extVisibilityReplace_top,
        extVisReplace_eq_self_of_selfVis (h.selfVis ⊤ k hk (extVisibilityReplace_top)) i]
    · by_cases hfp : k ≤ finitePart ξ
      · -- self-visible at `k`: both sides fixed
        have hself  :=
          (extVisibilityReplace_self_iff _ k).mpr (Or.inr (Or.inr ⟨ξ, rfl, hfp⟩))
        rw [extVisReplace_eq_self_of_selfVis hself i,
          extVisReplace_eq_self_of_selfVis (h.selfVis _ k hk hself) i]
      · -- inside the sub-`K` part of the block: affine or constant
        rw [not_le] at hfp
        have hrepl : extVisibilityReplace (ofOrd ξ) k i = ofOrd (limitPart ξ + i) := by
          simp_all [visibilityReplace] <;> aesop
        have hξ : ofOrd ξ = ofOrd (limitPart ξ + (finitePart ξ)) := by
          rw [decomposition]
        rcases h.blockwise ξ with ⟨β, hβ0, haff⟩ | ⟨c, hcvis, hconst⟩
        · have hβ : limitPart β = β := eq_limitPart_of_finitePart_eq_zero hβ0
          rw [hrepl, haff i (hi.trans hk), hξ, haff (finitePart ξ) (hfp.le.trans hk),
            extVisibilityReplace_ofOrd, visibilityReplace,
            ite_eq_left (by rw [← hβ, finitePart_limitPart_add_nat]; exact hfp),
            ordinalReplace, ← hβ, limitPart_limitPart_add_nat, ]
        · rw [hrepl, hconst i (hi.trans hk), hξ, hconst (finitePart ξ) (hfp.le.trans hk),
            extVisReplace_eq_self_of_selfVis
              (extVisReplace_self_of_le hcvis hk) i]
  · -- thresholds `k > K`: the guard pins `σ α = ⊥`; block closure of the `⊥`-fiber
    rw [stepSuppressor_of_gt (not_le.mp hk)] at hguard
    have hbot  := le_bot_iff.mp hguard
    rw [hbot, ]
    rcases ExtOrd.cases α with rfl | rfl | ⟨ξ, rfl⟩
    · simp_all
    · simp_all
    · rw [extVisibilityReplace_ofOrd]
      unfold visibilityReplace
      split_ifs with hfp
      · exact h.bot_blocks ξ _ (limitPart_limitPart_add_nat ξ i).symm hbot
      · exact hbot

/-- Every `K`-step shifter is a legal transform witness with the step suppressor, on any
family of grades `≤ K`: `p ⇒ σ ∘ p` for **every** labelling `p` (note §3; no hypotheses on
`p`). -/
theorem IsStepShifter.transformsTo {D : Type*} {grade : D → ℕ} {K} {σ}
    (h : IsStepShifter K σ) (hK : BoundedBy grade K) p :
    TransformsTo grade p (fun d => σ (p d)) :=
  ⟨stepSuppressor K, σ, stepSuppressor_antitone K, stepSuppressor_selfVis K, h.map_bot,
    h.mono, h.clause5,
    fun d => by rw [stepSuppressor_of_le (hK d), min_top_right]⟩

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
theorem TransformsTo.cap {D : Type*} {grade : D → ℕ} {p q : D → ExtOrd} {K} {γ}
    (h : TransformsTo grade p q) (hK : BoundedBy grade K)
    (hγ : extVisibilityReplace γ K K = γ) :
    TransformsTo grade p (fun d => min (q d) γ) := by
  obtain ⟨g, σ, hg_dec, hg_vis, hσ_bot, hσ_mono, hσ_vis, hσ_eq⟩ := h
  refine ⟨fun k => if k ≤ K then min (g k) γ else ⊥, σ, ?_, ?_, hσ_bot, hσ_mono, ?_, ?_⟩
  · -- antitone
    intro n m hnm
    dsimp only
    split_ifs with hm hn hn
    · grind
    · omega
    · exact bot_le
    · exact le_rfl
  · -- self-visible
    intro n
    dsimp only
    split_ifs with hn
    · rcases min_cases (g n) γ with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm]
      · exact hg_vis n
      · exact?
    · rfl
  · -- clause 5: the truncated guard implies the original guard
    intro α k hle i hi
    dsimp only at hle
    split_ifs at hle with hk
    · grind
    · exact hσ_vis α k ((le_bot_iff.mp hle).le.trans bot_le) i hi
  · -- the row equation: `min (σ (p d)) (min (g (grade d)) γ) = min (q d) γ`
    grind

end Transform

open Transform

/-- **Corollary 2.B** (note §2; the faithful Lemma 2.5.8): if `r` respects the restricted
semantics `E⟨B,j⟩` and `γ` is self-visible at `j`, then the capped labelling `r ∧ γ`
respects it too.  Locality is the Cap Lemma applied to `r`'s locality (all grades below the
pair are `≤ j` by `GradedLe`); availability is monotonicity of `min (·, γ)`; orderliness is
preservation of self-visibility under `min` with heredity of `γ`'s self-visibility. -/
theorem RespectsSemanticsBelow.cap {ι : Type*} [DecidableEq ι] {A : Finset ι}
    {D : CellScheme A} {sem : Semantics D} {BJ : GradedIndex ι} {r : BelowLabels D BJ}
    (h : RespectsSemanticsBelow sem BJ r) {γ : ExtOrd}
    (hγ : extVisibilityReplace γ BJ.2 BJ.2 = γ) :
    RespectsSemanticsBelow sem BJ (fun d => min (r d) γ) where
  orderly d :=
    (extVisReplace_min_self (h.orderly d).symm
      (extVisReplace_self_of_le hγ d.2.2)).symm
  locality Sig := by
    have key : TransformsTo (fun d => D.grade d.1) (sem.E Sig.1)
        (fun d => min (min (r (CellScheme.below.incl Sig d)) (r Sig)) γ) :=
      (h.locality Sig).cap (fun d => (d.2.trans Sig.2).2) hγ
    have heq : (fun d =>
        min (min (r (CellScheme.below.incl Sig d)) (r Sig)) γ) =
        fun d => min (min (r (CellScheme.below.incl Sig d)) γ) (min (r Sig) γ) := by
      funext d
      conv_rhs => rw [min_min_min_comm, min_self]
    rw [heq] at key
    exact key
  availability Sig Xi₀ hscope hgrade := by
    obtain ⟨Xi, hcell, hle⟩ := h.availability Sig Xi₀ hscope hgrade
    exact ⟨Xi, hcell, min_le_min hle le_rfl⟩

/-! ### More label arithmetic for the canonical alphabet -/

namespace Value

/-- The limit part has finite part `0`. -/
def finitePart_limitPart x := by
  have h := finitePart_limitPart_add_nat x 0
  rwa [Nat.cast_zero, add_zero] at h

/-- The limit part is idempotent. -/
theorem limitPart_idem x : limitPart (limitPart x) = limitPart x :=
  eq_limitPart_of_finitePart_eq_zero (finitePart_limitPart x)

/-- `ω * u` has finite part `0`. -/
theorem finitePart_omega0_mul u :
    finitePart (Ordinal.omega0 * u) = 0 := by
  conv_lhs => rw [← limitPart_omega0_mul u]
  exact finitePart_limitPart _

/-- Adding a natural number is inflationary. -/
theorem self_le_add_nat {x : Ordinal₀} {i : ℕ} : x ≤ x + i := by simp_all

/-- A code with a smaller block index is below the larger block level: `ω·u + m < ω·v` for
`u < v`. -/
def code_add_lt_mul {u v : Ordinal₀} (h : u < v) (m : ℕ) :=
  calc Ordinal.omega0 * u + m
      < Ordinal.omega0 * u + Ordinal.omega0 :=
        add_lt_add_right (Ordinal.natCast_lt_omega0 m) _
    _ = Ordinal.omega0 * Order.succ u := (Ordinal.mul_succ _ _).symm
    _ ≤ Ordinal.omega0 * v :=
        (Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono.monotone
          (Order.succ_le_of_lt h)

/-- Within a block, order is finite-part order. -/
def finitePart_le_of_le {x y} (hlim : limitPart x = limitPart y)
    (hxy : x ≤ y) := by
  have h1 : limitPart y + (finitePart x) = x := by rw [← hlim]; exact decomposition x
  have h2  := decomposition y
  have h3 : limitPart y + (finitePart x) ≤ limitPart y + (finitePart y) := by
    rw [h1, h2]; exact hxy
  exact_mod_cast (add_le_add_iff_left (limitPart y)).mp h3

/-- An ordinal in the half-open block `[limitPart x, limitPart x + ω)` has limit part
`limitPart x`. -/
theorem limitPart_eq_of_mem_block {x q} (h1 : limitPart x ≤ q)
    (h2 : q < limitPart x + Ordinal.omega0) : limitPart q = limitPart x := by
  refine le_antisymm ?_ ?_
  · by_contra hlt
    rw [not_le] at hlt
    exact absurd ((limitPart_add_omega0_le hlt).trans (limitPart_le)) (not_le.mpr h2)
  · calc limitPart x = limitPart (limitPart x) := (limitPart_idem x).symm
      _ ≤ limitPart q := limitPart_mono h1

end Value

namespace Transform

/-! ### The canonical alphabet: items and ranks -/

/-- The **items** of the canonical alphabet `ν_{S,K}` (note §3), a finite set of ordinals in
increasing order: for each block meeting `S` at finite parts `≤ K`, an *interval item* at the
block start (the image of `limitPart`); for each `s ∈ S` with finite part `≥ K+1`, a
*singleton item* at `s`.  (The top label `⊤` is always tracked separately, by the extra block
`(items S K).card`; see `canonicalNormalizer`.) -/
noncomputable def items (S : Finset Ordinal₀) K :=
  (S.filter fun s => finitePart s ≤ K).image limitPart ∪
    S.filter fun s => K + 1 ≤ finitePart s

variable {S : Finset Ordinal₀} {K : ℕ}

local notation "items₀" => items S K

theorem limitPart_mem_items {s} (hs : s ∈ S) (hfp : finitePart s ≤ K) :
    limitPart s ∈ items₀ :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hs, hfp⟩))

theorem mem_items_of_high {s} (hs : s ∈ S) (hfp : K + 1 ≤ finitePart s) :
    s ∈ items₀ :=
  Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hs, hfp⟩)

/-- Items are block starts or high singletons. -/
theorem items_fp {p} (hp : p ∈ items₀) :
    finitePart p = 0 ∨ K + 1 ≤ finitePart p := by
  rcases Finset.mem_union.mp hp with h | h
  · aesop (add safe apply [finitePart_limitPart])
  · simp_all

/-- The item count is at most `S.card` (one interval item per touched block, one singleton
item per high element). -/
theorem items_card_le : (items₀).card ≤ S.card := by
  calc (items₀).card
      ≤ ((S.filter fun s => finitePart s ≤ K).image limitPart).card +
        (S.filter fun s => K + 1 ≤ finitePart s).card := Finset.card_union_le _ _
    _ ≤ (S.filter fun s => finitePart s ≤ K).card +
        (S.filter fun s => K + 1 ≤ finitePart s).card :=
        Nat.add_le_add_right Finset.card_image_le _
    _ = S.card := by
        have hcongr : (S.filter fun s => K + 1 ≤ finitePart s) =
            S.filter fun s => ¬ finitePart s ≤ K :=
          Finset.filter_congr fun s _ => by omega
        rw [hcongr]
        exact Finset.card_filter_add_card_filter_not _

/-- The **rank** of `x`: the number of items `≤ x`. -/
noncomputable def rank S K x :=
  ((items S K).filter fun p => p ≤ x).card

local notation "rank₀" => rank S K

theorem rank_mono {x y} (hxy : x ≤ y) : rank₀ x ≤ rank₀ y := by unfold rank; gcongr

theorem rank_le_card x : rank₀ x ≤ (items₀).card :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem rank_eq_zero_iff {x} :
    rank₀ x = 0 ↔ ∀ p ∈ items₀, ¬ p ≤ x := by
  rw [rank, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

theorem rank_pos_of_item {p x} (hp : p ∈ items₀) (hpx : p ≤ x) :
    1 ≤ rank₀ x :=
  Nat.one_le_iff_ne_zero.mpr fun h => (rank_eq_zero_iff.mp h) p hp hpx

/-- Ranks agree when no item separates `x` from `y`. -/
theorem rank_eq_of_forall {x y} (hxy : x ≤ y)
    (h : ∀ p ∈ items₀, p ≤ y → p ≤ x) : rank₀ x = rank₀ y := by
  refine le_antisymm (rank_mono hxy) (Finset.card_le_card fun q hq => ?_)
  rw [Finset.mem_filter] at hq ⊢
  exact ⟨hq.1, h q hq.1 hq.2⟩

/-- A new item strictly between `x` and `y` raises the rank. -/
theorem rank_lt_rank_of_item {x y p} (hxy : x ≤ y) (hp : p ∈ items₀)
    (hpx : x < p) (hpy : p ≤ y) : rank₀ x < rank₀ y := by
  apply Finset.card_lt_card
  refine ⟨fun q hq => Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hq).1, le_trans (Finset.mem_filter.mp hq).2 hxy⟩, fun hsub => ?_⟩
  have := hsub (Finset.mem_filter.mpr ⟨hp, hpy⟩)
  exact absurd (Finset.mem_filter.mp this).2 (not_le.mpr hpx)

/-- No item lies strictly inside the sub-`K` part of a block: an item `≤ limitPart x + i`
(`i ≤ K`) is already `≤ limitPart x`. -/
theorem item_le_block_of_le {x p} {i} (hp : p ∈ items₀) (hi : i ≤ K)
    (hpy : p ≤ limitPart x + i) : p ≤ limitPart x := by
  by_contra hpx
  rw [not_le] at hpx
  have hblock  :=
    limitPart_eq_of_mem_block hpx.le
      (hpy.trans_lt (add_lt_add_right (Ordinal.natCast_lt_omega0 i) _))
  rcases items_fp hp with h0 | hhigh
  · simp_all [eq_limitPart_of_finitePart_eq_zero]
  · have hpe : p = limitPart x + (finitePart p) := by
      grind [decomposition]
    have hlt : limitPart x + i < limitPart x + (finitePart p) :=
      add_lt_add_right (Nat.cast_lt.mpr (lt_of_le_of_lt hi (Nat.lt_of_succ_le hhigh))) _
    rw [← hpe] at hlt
    exact absurd hpy (not_le.mpr hlt)

/-! ### The canonical normalizer -/

/-- Self-visibility of coded values: `ω·u + m` is self-visible at every threshold `≤ m`. -/
theorem code_selfVis {u : Ordinal₀} {m k : ℕ} (h : k ≤ m) :
    extVisibilityReplace (ofOrd (Ordinal.omega0 * u + m)) k k
      = ofOrd (Ordinal.omega0 * u + m) := by grind [extVisibilityReplace_self_iff, finitePart_code]

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
noncomputable def canonicalNormalizer (S : Finset Ordinal₀) (K : ℕ) : LabelMap
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



theorem canonicalNormalizer_ofOrd x :
    canonicalNormalizer S K (ofOrd x) =
      if (∃ p ∈ items S K, limitPart p = limitPart x) ∧
          ∀ p ∈ items S K, limitPart p = limitPart x → x < p then
        ofOrd (Ordinal.omega0 * rank S K x + K)
      else if limitPart x ∈ items S K ∧ finitePart x ≤ K then
        ofOrd (Ordinal.omega0 * (rank S K x - 1 : ℕ) + finitePart x)
      else if rank S K x = 0 then ⊥
      else ofOrd (Ordinal.omega0 * (rank S K x - 1 : ℕ) + ((K + 1 : ℕ) : Ordinal)) := rfl

/-- The **`3b` branch** (below-first-item region of a block with items): constant
`ω·rank + K`. -/
theorem canonicalNormalizer_3b {x}
    (h1 : ∃ p ∈ items₀, limitPart p = limitPart x)
    (h2 : ∀ p ∈ items₀, limitPart p = limitPart x → x < p) :
    canonicalNormalizer S K (ofOrd x) = ofOrd (Ordinal.omega0 * rank₀ x + K) := by
  rw [canonicalNormalizer_ofOrd, ite_eq_left ⟨h1, h2⟩]

/-- The **affine branch**: on the sub-`K` part of an interval-item block, `ν` shifts the
block affinely to code block `rank − 1`. -/
theorem canonicalNormalizer_affine {x} (hmem : limitPart x ∈ items S K)
    (hfp : finitePart x ≤ K) :
    canonicalNormalizer S K (ofOrd x)
      = ofOrd (Ordinal.omega0 * (rank S K x - 1 : ℕ) + finitePart x) := by
  have hno3b : ¬ ((∃ p ∈ items S K, limitPart p = limitPart x) ∧
      ∀ p ∈ items S K, limitPart p = limitPart x → x < p) := by
    grind [limitPart_idem, limitPart_le]
  rw [canonicalNormalizer_ofOrd, ite_eq_right hno3b, ite_eq_left ⟨hmem, hfp⟩]

/-- The **plateau branch**: the code of the greatest item `≤ x`, at offset `K+1`. -/
theorem canonicalNormalizer_plateau {x}
    (h3b : ¬ ((∃ p ∈ items S K, limitPart p = limitPart x) ∧
        ∀ p ∈ items S K, limitPart p = limitPart x → x < p))
    (haff : ¬ (limitPart x ∈ items S K ∧ finitePart x ≤ K)) (h0 : rank S K x ≠ 0) :
    canonicalNormalizer S K (ofOrd x)
      = ofOrd (Ordinal.omega0 * (rank S K x - 1 : ℕ) + ((K + 1 : ℕ) : Ordinal)) := by
  rw [canonicalNormalizer_ofOrd, ite_eq_right h3b, ite_eq_right haff, ite_eq_right h0]

/-- The **`⊥` branch**: blocks entirely below every item. -/
theorem canonicalNormalizer_of_rank_zero {x}
    (hb : ¬ ∃ p ∈ items₀, limitPart p = limitPart x) (h0 : rank₀ x = 0) :
    canonicalNormalizer S K (ofOrd x) = ⊥ := by grind [limitPart_idem, canonicalNormalizer_ofOrd]

/-- **`⊥`-fiber characterization**: `ν` sends an ordinal to `⊥` exactly when no item is
`≤ x` and no item shares `x`'s block.  In particular the `⊥`-fiber is a downward-closed
union of whole blocks. -/
theorem canonicalNormalizer_eq_bot_iff {x} :
    canonicalNormalizer S K (ofOrd x) = ⊥ ↔
      rank₀ x = 0 ∧ ¬ ∃ p ∈ items₀, limitPart p = limitPart x := by
  constructor
  · intro h
    by_cases hb : ∃ p ∈ items₀, limitPart p = limitPart x
    · exfalso
      by_cases hall : ∀ p ∈ items₀, limitPart p = limitPart x → x < p
      · simp_all [canonicalNormalizer_3b]
      · simp   at hall
        obtain ⟨p, hp, hlim, hpx⟩ := hall
        have h0  := Nat.one_le_iff_ne_zero.mp (rank_pos_of_item hp hpx)
        by_cases haff : limitPart x ∈ items₀ ∧ finitePart x ≤ K
        · simp_all [canonicalNormalizer_affine]
        · rw [canonicalNormalizer_plateau
            (fun hc => absurd (hc.2 p hp hlim) (not_lt.mpr hpx)) haff h0] at h
          exact ofOrd_ne_bot _ h
    · by_cases h0 : rank₀ x = 0
      · exact ⟨h0, hb⟩
      · rw [canonicalNormalizer_plateau (fun hc => hb hc.1)
          (fun hc => hb ⟨limitPart x, hc.1, limitPart_idem x⟩) h0] at h
        exact absurd h (ofOrd_ne_bot _)
  · simp_all [canonicalNormalizer_of_rank_zero]

/-- **The block bound** (note §3): the block indices of `ν_{S,K}` form an initial segment of
length at most `(items S K).card + 1 ≤ S.card + 1`. -/
theorem canonicalNormalizer_blockIdx_le x :
    canonicalNormalizer S K x = ⊥ ∨ ∃ u m : ℕ, u ≤ (items₀).card ∧ m ≤ K + 1 ∧
      canonicalNormalizer S K x = ofOrd (Ordinal.omega0 * u + m) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨ξ, rfl⟩
  · exact Or.inl rfl
  · aesop
  · rw [canonicalNormalizer_ofOrd]
    split_ifs with h1 h2 h3
    · aesop (add safe apply [rank_le_card])
    · grind only [rank_le_card]
    · exact Or.inl rfl
    · grind only [rank_le_card]

/-- Every value of `ν_{S,K}` is at most the top code (the value of `⊤`). -/
theorem canonicalNormalizer_le_top x :
    canonicalNormalizer S K x ≤ canonicalNormalizer S K ⊤ := by
  
  rcases ExtOrd.cases x with rfl | rfl | ⟨ξ, rfl⟩
  · exact bot_le
  · exact le_rfl
  · rw [canonicalNormalizer_ofOrd]
    split_ifs with h1 h2 h3
    · have h : ((rank S K ξ : ℕ)) ≤ ((items S K).card : Ordinal) :=
        Nat.cast_le.mpr (rank_le_card ξ)
      exact ofOrd_le_ofOrd.mpr (code_le_code h (Nat.le_succ K))
    · have h : ((rank S K ξ - 1 : ℕ)) ≤ ((items S K).card : Ordinal) :=
        Nat.cast_le.mpr (le_trans (Nat.sub_le _ 1) (rank_le_card ξ))
      exact ofOrd_le_ofOrd.mpr (code_le_code h (le_trans h2.2 (Nat.le_succ K)))
    · exact bot_le
    · have h : ((rank S K ξ - 1 : ℕ)) ≤ ((items S K).card : Ordinal) :=
        Nat.cast_le.mpr (le_trans (Nat.sub_le _ 1) (rank_le_card ξ))
      exact ofOrd_le_ofOrd.mpr (code_le_code h le_rfl)

/-! ### Monotonicity of the canonical normalizer -/

/-- A member of an earlier block is below every later block level and its members. -/
private def item_le_of_block_lt {p x y} (hplim : limitPart p = limitPart x)
    (hlxy : limitPart x < limitPart y) :=
  le_of_lt (lt_of_lt_of_le (lt_of_lt_of_le (hplim ▸ lt_limitPart_add_omega0 p)
    (limitPart_add_omega0_le hlxy)) (limitPart_le))

/-- Lower bound: at positive rank, every value of `ν` is at least the base of code block
`rank − 1`. -/
private theorem le_canonicalNormalizer_ofOrd {y} (h0 : rank S K y ≠ 0) :
    ofOrd (Ordinal.omega0 * (rank S K y - 1 : ℕ)) ≤ canonicalNormalizer S K (ofOrd y) := by
  by_cases h1 : (∃ p ∈ items S K, limitPart p = limitPart y) ∧
      ∀ p ∈ items S K, limitPart p = limitPart y → y < p
  · rw [canonicalNormalizer_3b h1.1 h1.2]
    exact ofOrd_le_ofOrd.mpr (le_trans ((Ordinal.isNormal_mul_right
      Ordinal.omega0_pos).strictMono.monotone (Nat.cast_le.mpr (Nat.sub_le _ 1)))
      (self_le_add_nat))
  · by_cases h2 : limitPart y ∈ items S K ∧ finitePart y ≤ K
    · simp_all [canonicalNormalizer_affine]
    · rw [canonicalNormalizer_plateau h1 h2 h0]
      exact ofOrd_le_ofOrd.mpr (self_le_add_nat)

private theorem mono_3b {x y} (hxy : x ≤ y)
    (h1 : ∃ p ∈ items₀, limitPart p = limitPart x)
    (h2 : ∀ p ∈ items₀, limitPart p = limitPart x → x < p) :
    canonicalNormalizer S K (ofOrd x) ≤ canonicalNormalizer S K (ofOrd y) := by
  obtain ⟨p₀, hp₀, hp₀lim⟩ := h1
  rw [canonicalNormalizer_3b ⟨p₀, hp₀, hp₀lim⟩ h2]
  by_cases hsame : limitPart y = limitPart x
  · by_cases hall : ∀ p ∈ items₀, limitPart p = limitPart y → y < p
    · -- `y` is still below every item of the (shared) block: equal rank, equal value
      have hrank : rank₀ x = rank₀ y := by
        refine rank_eq_of_forall hxy fun p hp hpy => ?_
        by_cases hpl : limitPart p = limitPart x
        · grind
        · refine le_of_lt (lt_of_limitPart_lt ?_)
          exact lt_of_le_of_ne (hsame ▸ limitPart_mono hpy) hpl
      rw [canonicalNormalizer_3b ⟨p₀, hp₀, hp₀lim.trans hsame.symm⟩ hall, hrank]
    · -- some item of the shared block is `≤ y`: `y` is on the plateau, one rank up
      simp only [not_forall, not_lt] at hall
      obtain ⟨p₁, hp₁, hl₁, hp₁y⟩ := hall
      have hx₁  := h2 p₁ hp₁ (hl₁.trans hsame)
      have hry  := rank_lt_rank_of_item hxy hp₁ hx₁ hp₁y
      have h0y  := Nat.one_le_iff_ne_zero.mp (rank_pos_of_item hp₁ hp₁y)
      have haffy : ¬ (limitPart y ∈ items₀ ∧ finitePart y ≤ K) := by
        rintro ⟨hm, -⟩
        have hxl  := h2 (limitPart y) hm (by rw [limitPart_idem]; exact hsame)
        have hly : limitPart y ≤ x := by rw [hsame]; exact limitPart_le
        exact absurd (lt_of_lt_of_le hxl hly) (lt_irrefl x)
      have h3by : ¬ ((∃ p ∈ items₀, limitPart p = limitPart y) ∧
          ∀ p ∈ items₀, limitPart p = limitPart y → y < p) :=
        fun hc => absurd (hc.2 p₁ hp₁ hl₁) (not_lt.mpr hp₁y)
      rw [canonicalNormalizer_plateau h3by haffy h0y]
      exact ofOrd_le_ofOrd.mpr
        (code_le_code (Nat.cast_le.mpr (by omega)) (Nat.le_succ K))
  · -- `y` is in a later block; `p₀ ≤ y`, so the rank strictly increases
    have hlxy  :=
      lt_of_le_of_ne (limitPart_mono hxy) fun h => hsame h.symm
    have hp₀y  := item_le_of_block_lt hp₀lim hlxy
    have hry  :=
      rank_lt_rank_of_item hxy hp₀ (h2 p₀ hp₀ hp₀lim) hp₀y
    rcases Nat.lt_or_ge (rank₀ x + 1) (rank₀ y) with hgap | hgap
    · -- rank gap `≥ 2`: chain through the base of code block `rank y − 1`
      have h0y : rank₀ y ≠ 0 := by omega
      refine le_trans ?_ (le_canonicalNormalizer_ofOrd h0y)
      refine ofOrd_le_ofOrd.mpr (le_of_lt (code_add_lt_mul ?_ K))
      exact_mod_cast (by omega)
    · -- adjacent ranks: `y` cannot be affine (that would need two new items)
      have hryx : rank₀ y = rank₀ x + 1 := by omega
      by_cases hally : ∀ p ∈ items₀, limitPart p = limitPart y → y < p
      · by_cases hby : ∃ p ∈ items₀, limitPart p = limitPart y
        · simp_all [canonicalNormalizer_3b, code_le_code]
        · have h0y : rank₀ y ≠ 0 := Nat.one_le_iff_ne_zero.mp (rank_pos_of_item hp₀ hp₀y)
          rw [canonicalNormalizer_plateau (fun hc => hby hc.1)
            (fun hc => hby ⟨limitPart y, hc.1, limitPart_idem y⟩) h0y]
          exact ofOrd_le_ofOrd.mpr
            (code_le_code (Nat.cast_le.mpr (by omega)) (Nat.le_succ K))
      · simp only [not_forall, not_lt] at hally
        obtain ⟨p₁, hp₁, hl₁, hp₁y⟩ := hally
        have h0y  := Nat.one_le_iff_ne_zero.mp (rank_pos_of_item hp₁ hp₁y)
        have h3by : ¬ ((∃ p ∈ items₀, limitPart p = limitPart y) ∧
            ∀ p ∈ items₀, limitPart p = limitPart y → y < p) :=
          fun hc => absurd (hc.2 p₁ hp₁ hl₁) (not_lt.mpr hp₁y)
        by_cases haffy : limitPart y ∈ items₀ ∧ finitePart y ≤ K
        · exfalso
          have hx₀  := h2 p₀ hp₀ hp₀lim
          have hstep1  :=
            rank_lt_rank_of_item hx₀.le hp₀ hx₀ le_rfl
          have hp₀lt  :=
            lt_of_lt_of_le (hp₀lim ▸ lt_limitPart_add_omega0 p₀)
              (limitPart_add_omega0_le hlxy)
          have hstep2  :=
            rank_lt_rank_of_item hp₀y haffy.1 hp₀lt (limitPart_le)
          omega
        · rw [canonicalNormalizer_plateau h3by haffy h0y]
          exact ofOrd_le_ofOrd.mpr
            (code_le_code (Nat.cast_le.mpr (by omega)) (Nat.le_succ K))

private theorem mono_affine {x y} (hxy : x ≤ y)
    (hmem : limitPart x ∈ items S K) (hfp : finitePart x ≤ K) :
    canonicalNormalizer S K (ofOrd x) ≤ canonicalNormalizer S K (ofOrd y) := by
  rw [canonicalNormalizer_affine hmem hfp]
  have hrx0  :=
    Nat.one_le_iff_ne_zero.mp (rank_pos_of_item hmem (limitPart_le))
  by_cases hsame : limitPart y = limitPart x
  · have hfxy : finitePart x ≤ finitePart y := finitePart_le_of_le hsame.symm hxy
    by_cases hfpy : finitePart y ≤ K
    · -- `y` affine in the same block, same rank
      have hmemy : limitPart y ∈ items S K := by rwa [hsame]
      rw [canonicalNormalizer_affine hmemy hfpy]
      have hrank : rank S K x = rank S K y := by
        refine rank_eq_of_forall hxy fun p hp hpy => ?_
        have hp'  := item_le_block_of_le hp hfpy (by rwa [decomposition])
        rw [hsame] at hp'
        exact le_trans hp' (limitPart_le)
      rw [hrank]
      exact ofOrd_le_ofOrd.mpr (code_le_code le_rfl hfxy)
    · -- `y` above the affine part of the block: plateau
      rw [not_le] at hfpy
      have hmy : limitPart y ∈ items S K := by rwa [hsame]
      have h0y  :=
        Nat.one_le_iff_ne_zero.mp (rank_pos_of_item hmy (limitPart_le))
      have h3by : ¬ ((∃ p ∈ items S K, limitPart p = limitPart y) ∧
          ∀ p ∈ items S K, limitPart p = limitPart y → y < p) := by
        grind [limitPart_idem, limitPart_le]
      rw [canonicalNormalizer_plateau h3by (fun hc => absurd hc.2 (not_le.mpr hfpy)) h0y]
      exact ofOrd_le_ofOrd.mpr (code_le_code
        (Nat.cast_le.mpr (Nat.sub_le_sub_right (rank_mono hxy) 1))
        (hfp.trans (Nat.le_succ K)))
  · -- later block
    have hlxy  :=
      lt_of_le_of_ne (limitPart_mono hxy) fun h => hsame h.symm
    rcases Nat.lt_or_ge (rank S K x) (rank S K y) with hlt | hge
    · have h0y : rank S K y ≠ 0 := by omega
      refine le_trans ?_ (le_canonicalNormalizer_ofOrd h0y)
      have hstep : ((rank S K x - 1 : ℕ)) < ((rank S K x) : Ordinal) := by
        exact_mod_cast Nat.sub_lt (Nat.pos_of_ne_zero hrx0) one_pos
      have hmul : Ordinal.omega0 * ((rank S K x : ℕ)) ≤
          Ordinal.omega0 * ((rank S K y - 1 : ℕ)) :=
        (Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono.monotone
          (Nat.cast_le.mpr (by omega))
      exact ofOrd_le_ofOrd.mpr
        (le_of_lt (lt_of_lt_of_le (code_add_lt_mul hstep (finitePart x)) hmul))
    · have hreq : rank S K y = rank S K x := le_antisymm hge (rank_mono hxy)
      by_cases hally : ∀ p ∈ items S K, limitPart p = limitPart y → y < p
      · by_cases hby : ∃ p ∈ items S K, limitPart p = limitPart y
        · rw [canonicalNormalizer_3b hby hally]
          refine ofOrd_le_ofOrd.mpr (le_trans (le_of_lt
            (code_add_lt_mul ?_ (finitePart x))) (self_le_add_nat))
          exact_mod_cast (by omega)
        · have h0y : rank S K y ≠ 0 := by omega
          rw [canonicalNormalizer_plateau (fun hc => hby hc.1)
            (fun hc => hby ⟨limitPart y, hc.1, limitPart_idem y⟩) h0y]
          exact ofOrd_le_ofOrd.mpr (code_le_code (Nat.cast_le.mpr (by omega))
            (hfp.trans (Nat.le_succ K)))
      · simp only [not_forall, not_lt] at hally
        obtain ⟨p₁, hp₁, hl₁, hp₁y⟩ := hally
        have h0y  := Nat.one_le_iff_ne_zero.mp (rank_pos_of_item hp₁ hp₁y)
        have h3by : ¬ ((∃ p ∈ items S K, limitPart p = limitPart y) ∧
            ∀ p ∈ items S K, limitPart p = limitPart y → y < p) :=
          fun hc => absurd (hc.2 p₁ hp₁ hl₁) (not_lt.mpr hp₁y)
        by_cases haffy : limitPart y ∈ items S K ∧ finitePart y ≤ K
        · exfalso
          have hxly  :=
            lt_of_lt_of_le (lt_limitPart_add_omega0 x) (limitPart_add_omega0_le hlxy)
          have := rank_lt_rank_of_item hxy haffy.1 hxly (limitPart_le)
          omega
        · rw [canonicalNormalizer_plateau h3by haffy h0y]
          exact ofOrd_le_ofOrd.mpr (code_le_code (Nat.cast_le.mpr (by omega))
            (hfp.trans (Nat.le_succ K)))

private theorem mono_plateau {x y} (hxy : x ≤ y)
    (h3b : ¬ ((∃ p ∈ items S K, limitPart p = limitPart x) ∧
        ∀ p ∈ items S K, limitPart p = limitPart x → x < p))
    (haff : ¬ (limitPart x ∈ items S K ∧ finitePart x ≤ K)) (h0 : rank S K x ≠ 0) :
    canonicalNormalizer S K (ofOrd x) ≤ canonicalNormalizer S K (ofOrd y) := by
  rw [canonicalNormalizer_plateau h3b haff h0]
  rcases Nat.lt_or_ge (rank S K x) (rank S K y) with hlt | hge
  · have h0y : rank S K y ≠ 0 := by omega
    refine le_trans ?_ (le_canonicalNormalizer_ofOrd h0y)
    have hstep : ((rank S K x - 1 : ℕ)) < ((rank S K x) : Ordinal) := by
      exact_mod_cast Nat.sub_lt (Nat.pos_of_ne_zero h0) one_pos
    have hmul : Ordinal.omega0 * ((rank S K x : ℕ)) ≤
        Ordinal.omega0 * ((rank S K y - 1 : ℕ)) :=
      (Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono.monotone
        (Nat.cast_le.mpr (by omega))
    exact ofOrd_le_ofOrd.mpr
      (le_of_lt (lt_of_lt_of_le (code_add_lt_mul hstep (K + 1)) hmul))
  · have hreq : rank S K y = rank S K x := le_antisymm hge (rank_mono hxy)
    by_cases hally : ∀ p ∈ items S K, limitPart p = limitPart y → y < p
    · by_cases hby : ∃ p ∈ items S K, limitPart p = limitPart y
      · rw [canonicalNormalizer_3b hby hally]
        refine ofOrd_le_ofOrd.mpr (le_trans (le_of_lt
          (code_add_lt_mul ?_ (K + 1))) (self_le_add_nat))
        exact_mod_cast (by omega)
      · grind [canonicalNormalizer_plateau, limitPart_idem]
    · simp only [not_forall, not_lt] at hally
      obtain ⟨p₁, hp₁, hl₁, hp₁y⟩ := hally
      
      have h3by : ¬ ((∃ p ∈ items S K, limitPart p = limitPart y) ∧
          ∀ p ∈ items S K, limitPart p = limitPart y → y < p) :=
        fun hc => absurd (hc.2 p₁ hp₁ hl₁) (not_lt.mpr hp₁y)
      by_cases haffy : limitPart y ∈ items S K ∧ finitePart y ≤ K
      · exfalso
        by_cases hsame : limitPart y = limitPart x
        · have hf : finitePart x ≤ finitePart y := finitePart_le_of_le hsame.symm hxy
          exact haff ⟨by rw [← hsame]; exact haffy.1, le_trans hf haffy.2⟩
        · have hlxy : limitPart x < limitPart y :=
            lt_of_le_of_ne (limitPart_mono hxy) fun h => hsame h.symm
          have hxly  :=
            lt_of_lt_of_le (lt_limitPart_add_omega0 x) (limitPart_add_omega0_le hlxy)
          have := rank_lt_rank_of_item hxy haffy.1 hxly (limitPart_le)
          omega
      · grind [canonicalNormalizer_plateau]

/-- **The canonical normalizer is monotone** (clause 4 of Def. 2.3.9 for `ν_{S,K}`). -/
theorem canonicalNormalizer_mono : Monotone (canonicalNormalizer S K) := by
  intro a b hab
  rcases ExtOrd.cases a with rfl | rfl | ⟨x, rfl⟩
  · simp_all [canonicalNormalizer]
  · rw [top_le_iff.mp hab]
  · rcases ExtOrd.cases b with rfl | rfl | ⟨y, rfl⟩
    · simp_all
    · exact canonicalNormalizer_le_top _
    · have hxy : x ≤ y := ofOrd_le_ofOrd.mp hab
      by_cases h3b : (∃ p ∈ items₀, limitPart p = limitPart x) ∧
          ∀ p ∈ items₀, limitPart p = limitPart x → x < p
      · exact mono_3b hxy h3b.1 h3b.2
      · by_cases haff : limitPart x ∈ items₀ ∧ finitePart x ≤ K
        · simp_all [mono_affine]
        · by_cases h0 : rank₀ x = 0
          · have hb : ¬ ∃ p ∈ items₀, limitPart p = limitPart x := by
              grind [rank_pos_of_item]
            rw [canonicalNormalizer_of_rank_zero hb h0]
            exact bot_le
          · exact mono_plateau hxy h3b haff h0

/-! ### The canonical decoder: item enumeration -/

/-- The natural number represented by an ordinal `< ω` (junk above). -/
noncomputable def ordToNat (o : Ordinal₀) := Cardinal.toNat o.card

@[simp] theorem ordToNat_natCast (n : ℕ) : ordToNat (n : Ordinal₀) = n := by
  rw [ordToNat, Ordinal.card_nat, Cardinal.toNat_natCast]

theorem ordToNat_cast_eq {o} (h : o < Ordinal.omega0) :
    ((ordToNat o : ℕ) : Ordinal₀) = o := by
  obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp h
  rw [ordToNat_natCast]

/-- The index of an item: the number of items strictly below it. -/
noncomputable def idx S K p :=
  ((items S K).filter fun q => q < p).card

local notation "idx₀" => idx S

theorem idx_lt_card {p} (hp : p ∈ items₀) :
    idx₀ K p < (items₀).card :=
  Finset.card_lt_card ⟨Finset.filter_subset _ _, fun hsub =>
    absurd (Finset.mem_filter.mp (hsub hp)).2 (lt_irrefl p)⟩

theorem idx_lt_idx {p q} (hp : p ∈ items₀) (hpq : p < q) :
    idx₀ K p < idx₀ K q := by
  apply Finset.card_lt_card
  constructor
  · grind
  · intro hsub
    exact absurd (Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨hp, hpq⟩))).2
      (lt_irrefl p)

theorem item_eq_of_idx_eq {p q} (hp : p ∈ items₀) (hq : q ∈ items₀)
    (h : idx₀ K p = idx₀ K q) : p = q := by
  rcases lt_trichotomy p q with hlt | heq | hgt
  · simp_all [Nat.ne_of_lt, idx_lt_idx]
  · exact heq
  · exact absurd h.symm (Nat.ne_of_lt (idx_lt_idx hq hgt))

/-- The rank of an item is its index plus one. -/
theorem rank_item {p} (hp : p ∈ items₀) :
    rank₀ p = idx₀ K p + 1 := by
  rw [rank, ]
  have hins : ((items₀).filter fun q => q ≤ p) =
      insert p ((items₀).filter fun q => q < p) := by
    grind
  rw [hins]
  exact Finset.card_insert_of_notMem fun hmem =>
    absurd (Finset.mem_filter.mp hmem).2 (lt_irrefl p)

/-- The `u`-th item in increasing order (junk `0` beyond the item count). -/
noncomputable def itemOfIdx S K u :=
  if h : u < (items S K).card then (items S K).orderEmbOfFin rfl ⟨u, h⟩ else 0

theorem itemOfIdx_mem {u} (h : u < (items₀).card) : itemOfIdx S K u ∈ items₀ := by
  rw [itemOfIdx, dite_eq_left h]
  exact Finset.orderEmbOfFin_mem _ _ _

/-- The enumeration inverts the index: the `u`-th item has index `u`. -/
theorem idx_itemOfIdx {u} (h : u < (items₀).card) :
    idx₀ K (itemOfIdx S K u) = u := by
  rw [itemOfIdx, dite_eq_left h]
  set e := (items₀).orderEmbOfFin rfl with he
  have himg : ((items₀).filter fun q => q < e ⟨u, h⟩) =
      (Finset.Iio (⟨u, h⟩)).image e := by
    ext q
    constructor
    · intro hq'
      rw [Finset.mem_filter] at hq'
      obtain ⟨hq, hlt⟩ := hq'
      have hqr : q ∈ Set.range e := by
        simp_all
      obtain ⟨j, rfl⟩ := hqr
      exact Finset.mem_image.mpr
        ⟨j, Finset.mem_Iio.mpr (e.strictMono.lt_iff_lt.mp hlt), rfl⟩
    · aesop
  rw [idx, himg, Finset.card_image_of_injective _ e.injective, Fin.card_Iio]

/-- The index inverts the enumeration on items. -/
theorem itemOfIdx_idx {p} (hp : p ∈ items₀) :
    itemOfIdx S K (idx₀ K p) = p := by grind [item_eq_of_idx_eq, itemOfIdx_mem, idx_lt_card, idx_itemOfIdx]

/-! ### The canonical decoder -/

/-- The sub-`K+1` value of a singleton code block: just below the item and above every
earlier item — `max (limitPart p + K) (the greatest item < p)`. -/
noncomputable def decoderLow (S : Finset Ordinal₀) (K : ℕ) (p : Ordinal₀) :=
  max (limitPart p + K) (((items S K).filter fun q => q < p).sup id)

theorem le_decoderLow_left p :
    limitPart p + (K : Ordinal) ≤ decoderLow S K p := le_max_left _ _

local notation "decoderLow₀" => decoderLow S K

theorem item_le_decoderLow {q p} (hq : q ∈ items₀) (hqp : q < p) :
    q ≤ decoderLow₀ p := by
  refine le_trans ?_ (le_max_right _ _)
  have hmem : q ∈ (items₀).filter fun r => r < p := by
    simp_all
  exact Finset.le_sup (f := id) hmem

theorem decoderLow_lt {p} (hp : K + 1 ≤ finitePart p) :
    decoderLow₀ p < p := by
  have hp0 : 0 < p := by
    have h0  := by
      have := finitePart_natCast 0
      rwa [Nat.cast_zero] at this
    refine lt_of_le_of_ne (by simp_all) fun h => ?_
    rw [← h, ] at hp
    omega
  rw [decoderLow, max_lt_iff]
  constructor
  · conv_rhs => rw [← decomposition p]
    exact add_lt_add_right (Nat.cast_lt.mpr (Nat.lt_of_succ_le hp)) _
  · simp_all

theorem le_finitePart_decoderLow p :
    K ≤ finitePart (decoderLow₀ p) := by
  rw [decoderLow]
  rcases max_cases (limitPart p + (K))
    (((items₀).filter fun q => q < p).sup id) with ⟨hm, -⟩ | ⟨hm, hlt⟩
  · rw [hm, finitePart_limitPart_add_nat]
  · rw [hm]
    have hne : ((items₀).filter fun q => q < p).Nonempty := by
      rcases Finset.eq_empty_or_nonempty ((items₀).filter fun q => q < p) with he | hne
      · simp_all only <;> aesop
      · exact hne
    obtain ⟨q, hqmem, hsup⟩ := Finset.exists_mem_eq_sup _ hne id
    rw [Finset.mem_filter] at hqmem
    rw [hsup, id_eq]
    have hqgt : limitPart p + (K) < q := by
      simp_all
    have hqlim  :=
      limitPart_eq_of_mem_block
        (le_trans (self_le_add_nat) (le_of_lt hqgt))
        (lt_trans hqmem.2 (lt_limitPart_add_omega0 p))
    rcases items_fp hqmem.1 with h0 | hhigh
    · simp_all only [eq_limitPart_of_finitePart_eq_zero] <;> aesop
    · omega

/-- The item owning the code block of `y`. -/
noncomputable def blockItem S K y :=
  itemOfIdx S K (ordToNat (y / Ordinal.omega0))

/-- The **canonical decoder** `τ_{S,K}` (note §3), the mirror map on the code side: on the
code block of an item `p` — every block below `ω·(items S K).card` is one — it is affine back
onto `[p, p+K]` when `p` is an interval item (constant `p + K` on the plateau), and for a
singleton item it sends offset `≥ K+1` to `p` and the sub-`K+1` part to the constant
`decoderLow p`; everything at or beyond the top block decodes to `⊤`. -/
noncomputable def canonicalDecoder (S : Finset Ordinal₀) (K : ℕ) : LabelMap
  | ⊥ => ⊥
  | some ⊤ => ⊤
  | some (some y) =>
    if y < Ordinal.omega0 * (items S K).card then
      if finitePart (blockItem S K y) = 0 then
        ofOrd (blockItem S K y + min (finitePart y) K)
      else if finitePart y ≤ K then ofOrd (decoderLow S K (blockItem S K y))
      else ofOrd (blockItem S K y)
    else ⊤

local notation "canonicalDecoder₀" => canonicalDecoder S K

@[simp] theorem canonicalDecoder_bot : canonicalDecoder₀ ⊥ = ⊥ := rfl

local notation "blockItem₀" => blockItem S K

theorem canonicalDecoder_ofOrd y :
    canonicalDecoder₀ (ofOrd y) =
      if y < Ordinal.omega0 * (items₀).card then
        if finitePart (blockItem₀ y) = 0 then
          ofOrd (blockItem₀ y + min (finitePart y) K)
        else if finitePart y ≤ K then ofOrd (decoderLow₀ (blockItem₀ y))
        else ofOrd (blockItem₀ y)
      else ⊤ := rfl

theorem canonicalDecoder_topRegion {y}
    (hy : ¬ y < Ordinal.omega0 * (items₀).card) :
    canonicalDecoder₀ (ofOrd y) = ⊤ := by
  rw [canonicalDecoder_ofOrd, ite_eq_right hy]

theorem canonicalDecoder_interval {y}
    (hy : y < Ordinal.omega0 * (items₀).card) (h0 : finitePart (blockItem₀ y) = 0) :
    canonicalDecoder₀ (ofOrd y) = ofOrd (blockItem₀ y + min (finitePart y) K) := by
  rw [canonicalDecoder_ofOrd, ite_eq_left hy, ite_eq_left h0]

theorem canonicalDecoder_singLow {y}
    (hy : y < Ordinal.omega0 * (items₀).card) (h0 : ¬ finitePart (blockItem₀ y) = 0)
    (hfp : finitePart y ≤ K) :
    canonicalDecoder₀ (ofOrd y) = ofOrd (decoderLow₀ (blockItem₀ y)) := by
  rw [canonicalDecoder_ofOrd, ite_eq_left hy, ite_eq_right h0, ite_eq_left hfp]

theorem canonicalDecoder_singHigh {y}
    (hy : y < Ordinal.omega0 * (items₀).card) (h0 : ¬ finitePart (blockItem₀ y) = 0)
    (hfp : ¬ finitePart y ≤ K) :
    canonicalDecoder₀ (ofOrd y) = ofOrd (blockItem₀ y) := by
  rw [canonicalDecoder_ofOrd, ite_eq_left hy, ite_eq_right h0, ite_eq_right hfp]

/-- The code division computation: `(ω·u + m) / ω = u`. -/
theorem code_div_omega0 (u : Ordinal₀) (m : ℕ) :
    (Ordinal.omega0 * u + m) / Ordinal.omega0 = u := by
  rw [Ordinal.mul_add_div _ Ordinal.omega0_ne_zero,
    Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 m), add_zero]

@[simp] theorem blockItem_code (u m : ℕ) :
    blockItem₀ (Ordinal.omega0 * u + m) = itemOfIdx S K u := by
  rw [blockItem, code_div_omega0, ordToNat_natCast]

/-- In the decoding region the block index is a genuine item index, and the block level of
`y` is the corresponding code block. -/
theorem blockIdx_lt {y} (hy : y < Ordinal.omega0 * (items₀).card) :
    ordToNat (y / Ordinal.omega0) < (items₀).card ∧
      limitPart y = Ordinal.omega0 * (ordToNat (y / Ordinal.omega0) : ℕ) := by
  have hdiv  :=
    (Ordinal.lt_mul_iff_div_lt Ordinal.omega0_ne_zero).mp hy
  have hcast  :=
    ordToNat_cast_eq (lt_trans hdiv (Ordinal.natCast_lt_omega0 _))
  constructor
  · rw [← hcast] at hdiv
    exact_mod_cast hdiv
  · rw [hcast]
    rfl

/-! ### The canonical normalizer is a step shifter -/

local notation "rank₀₀" => rank S

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
    · 
      exact code_selfVis (hk.trans (Nat.le_succ K))
    · have hfp : k ≤ finitePart ξ := by
        rcases (extVisibilityReplace_self_iff _ _).mp hx with h | h | ⟨α, hα, hα_fp⟩
        · exact absurd h (ofOrd_ne_bot ξ)
        · exact absurd h (ofOrd_ne_top ξ)
        · rw [ofOrd_inj.mp hα]
          exact hα_fp
      rw [canonicalNormalizer_ofOrd]
      split_ifs with h1 h2 h3
      · exact code_selfVis hk
      · exact code_selfVis hfp
      · rfl
      · exact code_selfVis (hk.trans (Nat.le_succ K))
  blockwise := by
    intro ξ
    by_cases hmem : limitPart ξ ∈ items S K
    · -- interval-item block: affine onto code block `rank − 1`
      left
      refine ⟨Ordinal.omega0 * (rank₀₀ K (limitPart ξ) - 1 : ℕ),
        finitePart_omega0_mul _, ?_⟩
      intro i hi
      have hlim : limitPart (limitPart ξ + (i)) = limitPart ξ :=
        limitPart_limitPart_add_nat ξ i
      have hfpi : finitePart (limitPart ξ + (i)) = i := finitePart_limitPart_add_nat ξ i
      have hmem' : limitPart (limitPart ξ + (i)) ∈ items S K := by
        rw [hlim]
        exact hmem
      rw [canonicalNormalizer_affine hmem' (by rw [hfpi]; exact hi)]
      have hrk : rank₀₀ K (limitPart ξ) = rank₀₀ K (limitPart ξ + (i)) :=
        rank_eq_of_forall (self_le_add_nat) fun q hq hqy => item_le_block_of_le hq hi hqy
      rw [← hrk, hfpi]
    · by_cases hblock : ∃ p ∈ items S K, limitPart p = limitPart ξ
      · -- singleton-only block: constant `ω·rank + K` below its first item
        right
        refine ⟨ofOrd (Ordinal.omega0 * rank₀₀ K (limitPart ξ) + K), code_selfVis le_rfl, ?_⟩
        intro i hi
        obtain ⟨p, hp, hplim⟩ := hblock
        have hlim : limitPart (limitPart ξ + (i)) = limitPart ξ :=
          limitPart_limitPart_add_nat ξ i
        have h2 : ∀ q ∈ items S K, limitPart q = limitPart (limitPart ξ + (i)) →
            limitPart ξ + (i) < q := by
          intro q hq hql
          rw [hlim] at hql
          rcases items_fp hq with h0 | hhigh
          · exfalso
            apply hmem
            have hq_eq : q = limitPart ξ := by
              rw [← hql]
              exact (eq_limitPart_of_finitePart_eq_zero h0).symm
            rw [← hq_eq]
            exact hq
          · have hq_eq : q = limitPart ξ + (finitePart q) := by
              conv_lhs => rw [← decomposition q]
              rw [hql]
            rw [hq_eq]
            exact add_lt_add_right (Nat.cast_lt.mpr (by omega)) _
        rw [canonicalNormalizer_3b ⟨p, hp, by rw [hlim]; exact hplim⟩ h2]
        have hrk : rank₀₀ K (limitPart ξ) = rank₀₀ K (limitPart ξ + (i)) :=
          rank_eq_of_forall (self_le_add_nat) fun q hq hqy => item_le_block_of_le hq hi hqy
        rw [← hrk]
      · by_cases h0 : rank₀₀ K (limitPart ξ) = 0
        · -- block entirely below every item: constant `⊥`
          right
          refine ⟨⊥, extVisibilityReplace_bot K K, ?_⟩
          intro i hi
          have hlim : limitPart (limitPart ξ + (i)) = limitPart ξ :=
            limitPart_limitPart_add_nat ξ i
          have hrk : rank₀₀ K (limitPart ξ) = rank₀₀ K (limitPart ξ + (i)) :=
            rank_eq_of_forall (self_le_add_nat) fun q hq hqy =>
              item_le_block_of_le hq hi hqy
          refine canonicalNormalizer_of_rank_zero ?_ (by rw [← hrk]; exact h0)
          rintro ⟨q, hq, hql⟩
          exact hblock ⟨q, hq, hql.trans hlim⟩
        · -- item-free block above some item: constant plateau
          right
          refine ⟨ofOrd (Ordinal.omega0 * (rank₀₀ K (limitPart ξ) - 1 : ℕ) +
            ((K + 1 : ℕ))), code_selfVis (Nat.le_succ K), ?_⟩
          intro i hi
          have hlim : limitPart (limitPart ξ + (i)) = limitPart ξ :=
            limitPart_limitPart_add_nat ξ i
          have hrk : rank₀₀ K (limitPart ξ) = rank₀₀ K (limitPart ξ + (i)) :=
            rank_eq_of_forall (self_le_add_nat) fun q hq hqy =>
              item_le_block_of_le hq hi hqy
          rw [canonicalNormalizer_plateau ?_ ?_ ?_, ← hrk]
          · rintro ⟨⟨q, hq, hql⟩, -⟩
            exact hblock ⟨q, hq, hql.trans hlim⟩
          · rintro ⟨hm, -⟩
            rw [hlim] at hm
            exact hmem hm
          · rw [← hrk]
            exact h0
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

/-! ### The canonical decoder is a step shifter -/

theorem itemOfIdx_lt {u v} (hv : v < (items₀).card) (huv : u < v) :
    itemOfIdx S K u < itemOfIdx S K v := by
  rw [itemOfIdx, itemOfIdx, dite_eq_left (lt_trans huv hv), dite_eq_left hv]
  exact ((items₀).orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr huv)

theorem div_omega0_eq_of_limitPart_eq {x y} (h : limitPart x = limitPart y) :
    x / Ordinal.omega0 = y / Ordinal.omega0 := by
  unfold limitPart at h
  exact (Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono.injective h

/-- **The canonical decoder is monotone** (clause 4 of Def. 2.3.9 for `τ_{S,K}`). -/
theorem canonicalDecoder_mono : Monotone (canonicalDecoder₀) := by
  intro a b hab
  rcases ExtOrd.cases a with rfl | rfl | ⟨y, rfl⟩
  · simp_all
  · rw [top_le_iff.mp hab]
  · rcases ExtOrd.cases b with rfl | rfl | ⟨y', rfl⟩
    · simp_all
    · simp [canonicalDecoder]
    · have hyy : y ≤ y' := ofOrd_le_ofOrd.mp hab
      by_cases hy' : y' < Ordinal.omega0 * (items₀).card
      case neg =>
        simp_all [canonicalDecoder_topRegion]
      have hy  := lt_of_le_of_lt hyy hy'
      obtain ⟨hu, hlimy⟩ := blockIdx_lt hy
      obtain ⟨hu', hlimy'⟩ := blockIdx_lt hy'
      have hpmem  := itemOfIdx_mem hu
      have hp'mem  := itemOfIdx_mem hu'
      have hfp_high := (items_fp hpmem).resolve_left
      have hfp'_high := (items_fp hp'mem).resolve_left
      have huu  := by
        have hmul : Ordinal.omega0 * ((ordToNat (y / Ordinal.omega0) : ℕ)) ≤
            Ordinal.omega0 * ((ordToNat (y' / Ordinal.omega0) : ℕ)) := by
          rw [← hlimy, ← hlimy']
          exact limitPart_mono hyy
        exact Nat.cast_le.mp
          ((Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono.le_iff_le.mp hmul)
      rcases Nat.lt_or_ge (ordToNat (y / Ordinal.omega0)) (ordToNat (y' / Ordinal.omega0))
        with hlt | hge
      · -- distinct code blocks: chain through `hi(p) ≤ lo(p')`
        have hpp'  := itemOfIdx_lt hu' hlt
        have hhi : canonicalDecoder₀ (ofOrd y) ≤
            ofOrd (if finitePart (blockItem₀ y) = 0
              then blockItem₀ y + (K) else blockItem₀ y) := by
          by_cases h0 : finitePart (blockItem₀ y) = 0
          · simp_all [canonicalDecoder_interval]
          · rw [ite_eq_right h0]
            by_cases hfp : finitePart y ≤ K
            · rw [canonicalDecoder_singLow hy h0 hfp]
              exact ofOrd_le_ofOrd.mpr (le_of_lt (decoderLow_lt (hfp_high h0)))
            · simp_all [canonicalDecoder_singHigh]
        have hlo : ofOrd (if finitePart (blockItem₀ y') = 0 then blockItem₀ y'
            else decoderLow₀ (blockItem₀ y')) ≤ canonicalDecoder₀ (ofOrd y') := by
          by_cases h0' : finitePart (blockItem₀ y') = 0
          · simp_all [canonicalDecoder_interval]
          · rw [ite_eq_right h0']
            by_cases hfp' : finitePart y' ≤ K
            · simp_all [canonicalDecoder_singLow]
            · rw [canonicalDecoder_singHigh hy' h0' hfp']
              exact ofOrd_le_ofOrd.mpr (le_of_lt (decoderLow_lt (hfp'_high h0')))
        refine le_trans hhi (le_trans (ofOrd_le_ofOrd.mpr ?_) hlo)
        by_cases h0 : finitePart (blockItem₀ y) = 0
        · rw [ite_eq_left h0]
          have hplim  :=
            eq_limitPart_of_finitePart_eq_zero h0
          by_cases h0' : finitePart (blockItem₀ y') = 0
          · rw [ite_eq_left h0']
            have hplim'  :=
              eq_limitPart_of_finitePart_eq_zero h0'
            have hll : limitPart (blockItem₀ y) < limitPart (blockItem₀ y') := by
              simp_all [blockItem]
            have hstep := limitPart_add_omega0_le hll
            rw [hplim, hplim'] at hstep
            exact le_of_lt (lt_of_lt_of_le
              (add_lt_add_right (Ordinal.natCast_lt_omega0 K) _) hstep)
          · rw [ite_eq_right h0']
            refine le_trans ?_ (le_decoderLow_left _)
            have hlp : blockItem₀ y ≤ limitPart (blockItem₀ y') := by
              rw [← hplim]
              exact limitPart_mono hpp'.le
            exact add_le_add hlp le_rfl
        · grind [blockItem, item_le_decoderLow]
      · -- the same code block
        have hueq  :=
          le_antisymm huu hge
        have hpe : blockItem₀ y = blockItem₀ y' := by
          rw [blockItem, blockItem, hueq]
        have hlimeq : limitPart y = limitPart y' := by
          rw [hlimy, hlimy', hueq]
        have hfyy  := finitePart_le_of_le hlimeq hyy
        by_cases h0 : finitePart (blockItem₀ y) = 0
        · simp_all [canonicalDecoder_interval]
        · by_cases hfp : finitePart y ≤ K
          · by_cases hfp' : finitePart y' ≤ K
            · simp_all [canonicalDecoder_singLow]
            · rw [canonicalDecoder_singLow hy h0 hfp,
                canonicalDecoder_singHigh hy' (by rw [← hpe]; exact h0) hfp', ← hpe]
              exact ofOrd_le_ofOrd.mpr (le_of_lt (decoderLow_lt (hfp_high h0)))
          · grind [canonicalDecoder_singHigh]

/-- **`τ_{S,K}` is a `K`-step shifter** (note §3): the code side has the same block geometry
with exactly one item per block, so the same case split applies. -/
theorem isStepShifter_canonicalDecoder :
    IsStepShifter K (canonicalDecoder₀) where
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
        · rw [ofOrd_inj.mp hα]
          exact hα_fp
      by_cases hy : y < Ordinal.omega0 * (items₀).card
      case neg =>
        rw [canonicalDecoder_topRegion hy]
        rfl
      obtain ⟨hu, -⟩ := blockIdx_lt hy
      have hpmem : blockItem₀ y ∈ items₀ := itemOfIdx_mem hu
      by_cases h0 : finitePart (blockItem₀ y) = 0
      · rw [canonicalDecoder_interval hy h0]
        refine (extVisibilityReplace_self_iff _ _).mpr (Or.inr (Or.inr ⟨_, rfl, ?_⟩))
        have hplim : limitPart (blockItem₀ y) = blockItem₀ y :=
          eq_limitPart_of_finitePart_eq_zero h0
        rw [show blockItem₀ y + ((min (finitePart y) K)) =
            limitPart (blockItem₀ y) + ((min (finitePart y) K)) by
          rw [hplim], finitePart_limitPart_add_nat]
        exact le_min hfp hk
      · by_cases hfpy : finitePart y ≤ K
        · rw [canonicalDecoder_singLow hy h0 hfpy]
          refine (extVisibilityReplace_self_iff _ _).mpr (Or.inr (Or.inr ⟨_, rfl, ?_⟩))
          exact le_trans hk (le_finitePart_decoderLow _)
        · rw [canonicalDecoder_singHigh hy h0 hfpy]
          refine (extVisibilityReplace_self_iff _ _).mpr (Or.inr (Or.inr ⟨_, rfl, ?_⟩))
          rcases items_fp hpmem with hz | hh
          · exact absurd hz h0
          · omega
  blockwise := by
    intro ξ
    by_cases hy : limitPart ξ < Ordinal.omega0 * (items₀).card
    case neg =>
      right
      refine ⟨⊤, extVisibilityReplace_top, ?_⟩
      intro i _hi
      refine canonicalDecoder_topRegion ?_
      rw [not_lt] at hy ⊢
      exact le_trans hy (self_le_add_nat)
    · obtain ⟨hu, -⟩ := blockIdx_lt hy
      have hyi : ∀ i : ℕ, limitPart ξ + i < Ordinal.omega0 * (items₀).card := by
        intro i
        refine lt_of_lt_of_le (add_lt_add_right (Ordinal.natCast_lt_omega0 i) _) ?_
        have h1 : limitPart (limitPart ξ) <
            limitPart (Ordinal.omega0 * ((items₀).card)) := by
          rw [limitPart_idem, limitPart_omega0_mul]
          exact hy
        have h2 := limitPart_add_omega0_le h1
        rw [limitPart_idem, limitPart_omega0_mul] at h2
        exact h2
      have hblockItem : ∀ i : ℕ,
          blockItem₀ (limitPart ξ + i) = blockItem₀ (limitPart ξ) := by
        intro i
        rw [blockItem, blockItem, div_omega0_eq_of_limitPart_eq
          ((limitPart_limitPart_add_nat ξ i).trans (limitPart_idem ξ).symm)]
      by_cases h0 : finitePart (blockItem₀ (limitPart ξ)) = 0
      · left
        refine ⟨blockItem₀ (limitPart ξ), h0, ?_⟩
        intro i hi
        have hfpi : finitePart (limitPart ξ + i) = i := finitePart_limitPart_add_nat ξ i
        rw [canonicalDecoder_interval (hyi i) (by rw [hblockItem i]; exact h0),
          hblockItem i, hfpi, min_eq_left hi]
      · right
        refine ⟨ofOrd (decoderLow₀ (blockItem₀ (limitPart ξ))), ?_, ?_⟩
        · exact (extVisibilityReplace_self_iff _ _).mpr
            (Or.inr (Or.inr ⟨_, rfl, le_finitePart_decoderLow _⟩))
        · intro i hi
          have hfpi : finitePart (limitPart ξ + i) = i := finitePart_limitPart_add_nat ξ i
          rw [canonicalDecoder_singLow (hyi i) (by rw [hblockItem i]; exact h0)
            (by rw [hfpi]; exact hi), hblockItem i]
  bot_blocks := by
    intro ξ ζ _hlim hbot
    exfalso
    by_cases hy : ξ < Ordinal.omega0 * (items₀).card
    · by_cases h0 : finitePart (blockItem₀ ξ) = 0
      · rw [canonicalDecoder_interval hy h0] at hbot
        exact ofOrd_ne_bot _ hbot
      · by_cases hfp : finitePart ξ ≤ K
        · rw [canonicalDecoder_singLow hy h0 hfp] at hbot
          exact ofOrd_ne_bot _ hbot
        · rw [canonicalDecoder_singHigh hy h0 hfp] at hbot
          exact ofOrd_ne_bot _ hbot
    · rw [canonicalDecoder_topRegion hy] at hbot
      exact top_ne_bot hbot

/-! ### The retraction: decoding inverts encoding on tracked labels -/

/-- `τ_{S,K} ∘ ν_{S,K}` is the identity on `⊥`, `⊤`, and the tracked ordinals `S`. -/
theorem canonicalDecoder_canonicalNormalizer {x}
    (hx : x = ⊥ ∨ x = ⊤ ∨ ∃ s ∈ S, x = ofOrd s) :
    canonicalDecoder S K (canonicalNormalizer S K x) = x := by
  rcases hx with rfl | rfl | ⟨s, hs, rfl⟩
  · rfl
  · simp_all [canonicalDecoder_topRegion, canonicalNormalizer]
  · by_cases hfp : finitePart s ≤ K
    · -- interval-item block: the affine code decodes affinely
      have hmem  := limitPart_mem_items hs hfp
      have hrk : rank₀₀ K s = idx₀ K (limitPart s) + 1 := by
        have h1 : rank₀₀ K (limitPart s) = rank₀₀ K s :=
          rank_eq_of_forall (limitPart_le) fun p hp hpy =>
            item_le_block_of_le hp hfp (by rwa [decomposition])
        rw [← h1, rank_item hmem]
      rw [canonicalNormalizer_affine hmem hfp]
      have hidx : rank₀₀ K s - 1 = idx₀ K (limitPart s) := by omega
      rw [hidx]
      have hylt : Ordinal.omega0 * (idx₀ K (limitPart s)) + (finitePart s)
          < Ordinal.omega0 * ((items S K).card) :=
        code_add_lt_mul (Nat.cast_lt.mpr (idx_lt_card hmem)) _
      have hbi : blockItem S K
          (Ordinal.omega0 * (idx₀ K (limitPart s)) + (finitePart s))
          = limitPart s := by
        simp_all [itemOfIdx_idx]
      rw [canonicalDecoder_interval hylt (by simp_all [finitePart_limitPart]), hbi,
        finitePart_code, min_eq_left hfp, decomposition]
    · -- singleton item: the plateau code decodes to the item itself
      
      have hmem : s ∈ items S K := mem_items_of_high hs (by omega)
      have h3b : ¬ ((∃ p ∈ items S K, limitPart p = limitPart s) ∧
          ∀ p ∈ items S K, limitPart p = limitPart s → s < p) := by
        aesop
      have haff : ¬ (limitPart s ∈ items S K ∧ finitePart s ≤ K) := by
        rintro ⟨-, h⟩
        omega
      have h0  := Nat.one_le_iff_ne_zero.mp (rank_pos_of_item hmem le_rfl)
      rw [canonicalNormalizer_plateau h3b haff h0]
      have hidx : rank₀₀ K s - 1 = idx₀ K s := by
        rw [rank_item hmem]
        omega
      rw [hidx]
      have hylt : Ordinal.omega0 * (idx₀ K s) + ((K + 1 : ℕ))
          < Ordinal.omega0 * ((items S K).card) :=
        code_add_lt_mul (Nat.cast_lt.mpr (idx_lt_card hmem)) _
      have hbi : blockItem S K
          (Ordinal.omega0 * (idx₀ K s) + ((K + 1 : ℕ))) = s := by
        grind [blockItem_code, itemOfIdx_idx]
      have h0' : ¬ finitePart (blockItem S K
          (Ordinal.omega0 * (idx₀ K s) + ((K + 1 : ℕ)))) = 0 := by
        rw [hbi]
        omega
      have hfp' : ¬ finitePart
          (Ordinal.omega0 * (idx₀ K s) + ((K + 1 : ℕ))) ≤ K := by
        rw [finitePart_code]
        omega
      rw [canonicalDecoder_singHigh hylt h0' hfp', hbi]

/-! ### The NF Lemma (note §3, Lemma 3.A; faithful Lemmas 2.3.3/2.3.15) -/

end Transform

/-! ### The finite coded inventory, combinatorial level (note §4) -/

namespace ExtOrd

/-- The **coded alphabet** at block bound `t` and grade bound `K` (note §§3–4): `⊥` together
with the codes `ω·u + m`, `u ≤ t`, `m ≤ K+1` — a `Finset`. -/
noncomputable def codedAlphabet t K :=
  insert ⊥ ((Finset.range (t + 1) ×ˢ Finset.range (K + 2)).image
    fun um => ofOrd (Ordinal.omega0 * um.1 + um.2))

theorem mem_codedAlphabet_iff {t K} {x} :
    x ∈ codedAlphabet t K ↔
      x = ⊥ ∨ ∃ u m : ℕ, u ≤ t ∧ m ≤ K + 1 ∧ x = ofOrd (Ordinal.omega0 * u + m) := by
  simp only [codedAlphabet, Finset.mem_insert, Finset.mem_image, Finset.mem_product,
    Finset.mem_range]
  constructor
  · grind
  · rintro (h | ⟨u, m, hu, hm, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨⟨u, m⟩, ⟨by omega, by omega⟩, rfl⟩

/-- **The finite inventory at the combinatorial level** (note §4; the counting content of
Lemmas 4.3.4/4.3.9/4.3.11): over a finite family, the labellings with values in the coded
alphabet form a finite set. -/
theorem codedLabellings_finite (D : Type*) [Finite D] (t K : ℕ) :
    {F : D → ExtOrd | ∀ d, F d ∈ codedAlphabet t K}.Finite := by
  have h : {F : D → ExtOrd | ∀ d, F d ∈ codedAlphabet t K} =
      Set.pi Set.univ fun _ : D => (codedAlphabet t K) := by
    ext F
    simp 
  rw [h]
  exact Set.Finite.pi fun _ => (codedAlphabet t K).finite_toSet

end ExtOrd

namespace Transform

variable {S : Finset Ordinal₀} {K : ℕ}

/-- Canonical forms take values in the coded alphabet at block bound `≥ S.card` (note §4):
the inventory of canonical forms is finite. -/
theorem canonicalNormalizer_mem_codedAlphabet {t} (ht : S.card ≤ t) x :
    canonicalNormalizer S K x ∈ ExtOrd.codedAlphabet t K := by grind [ExtOrd.mem_codedAlphabet_iff, canonicalNormalizer_blockIdx_le, items_card_le]



