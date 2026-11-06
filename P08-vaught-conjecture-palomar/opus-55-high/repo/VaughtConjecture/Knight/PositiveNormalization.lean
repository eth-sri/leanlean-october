/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.SetTheory.Cardinal.Finite
public import VaughtConjecture.Knight.WitnessAlgebra
public import VaughtConjecture.Knight.NormalForm

/-! # Positive normalization: finite coded respecting representatives without closure

After the reassessment note's `PositiveNormalizationDraft.lean`
(`vc-notes/reassessment/gap-work`, 2026-09-08; compiled here with two one-token fixes).

**The mechanism.**  Normalize each actual controller witness to a bounded exact witness with the
step suppressor `g_m` (`exists_bounded_exact_capped_witness`, `Knight/WitnessAlgebra.lean`), then
postcompose with a normalized witness at a larger grade bound `K` that **reflects bottom**.  The
composite is again a witness with suppressor `g_m` (`Witness.comp_of_bottom_reflecting`): at
thresholds `≤ m` both commute unguardedly, and above `m` the composite's guard, through bottom
reflection, restores the inner witness's guard.  This is not transformation transitivity and
not closure of all normalized witnesses under composition.

**Bottom reflection from ordinal zero.**  The canonical normalizer `ν_{S,K}` sends an ordinal to
`⊥` exactly when its item-rank is zero (`canonicalNormalizer_eq_bot_iff`); with `0 ∈ S` zero is
an item below every ordinal, so `ν_{S,K}` reflects bottom
(`canonicalNormalizer_reflects_bottom_of_zero_mem`).  Hence, with the semantic rows unchanged,
respect is closed under `ν_{insert 0 S, K}` (`RespectsSemanticsBelow.canonical_insert_zero`).

**The finite cover** (`RespectsSemanticsBelow.exists_coded_representative`): on a fixed finite
lower domain with `m` cells and grades at most `K`, every respecting labelling has a respecting
representative taking values in the one finite coded alphabet `codedAlphabet (m + 1) K`, with the
canonical decoder recovering the original labelling exactly on every cell.  Tracking the
labelling's ordinal values plus zero costs at most `m + 1` inventory items
(`items_card_le`); the existing alphabet and decoder theorems supply the rest.

**Boundaries.**  This is the existential finite normal form: it does not prove the universally
quantified `NormalizationClosure` (#128, stated only), it is not a relative normalizer preserving
prescribed codes below a cut, the decoder depends on the labelling (one decoder per labelling,
not one for all), inherited labels are not preserved literally, and normalizing two profiles
separately says nothing about their compatibility or a common extension.  It removes a coding
obstacle, not the mixed-grade amalgamation problem.  Also recorded: faithful transformation
cannot reverse two same-grade sources (`TransformsTo.same_grade_order`), a same-grade form of the
fixed-row order law of `Knight/CoupledGradeTwoRequest.lean`.

**Decoder transport** (after the reviewer's decoder-closure scout,
`vc-decoder-normalization/DecoderNormalizationScout.lean`, 2026-09-08; ported with attribution).
The canonical decoder reflects bottom for *every* inventory (`canonicalDecoder_reflects_bottom`:
every nonbottom branch returns an ordinal or `⊤`), so the same composition argument gives
closure of respect under every bottom-reflecting `K`-step shifter
(`RespectsSemanticsBelow.map_bottom_reflecting`), in particular under decoding
(`RespectsSemanticsBelow.decoded`), with the semantic rows unchanged.  With zero in the inventory
and the labelling's ordinal values tracked, respect of a labelling is *equivalent* to respect of
its canonical encoding (`respects_canonical_iff`), and a respecting lift of jointly encoded
inputs decodes to a respecting lift with literal protected labels and the original capped
agreement (`decode_relative_lift`).  This upgrades one-way compression to transport of solutions
over one shared codebook; it builds no section, controller family, or extension domain, and
faces encoded with unrelated codebooks are not covered. -/
@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-- A normalized witness may be followed by a normalized, bottom-reflecting
witness at a larger grade. Bottom reflection is used only above the inner grade. -/
theorem Witness.comp_of_bottom_reflecting
    {m K : ℕ} {τ ν : ExtOrd → ExtOrd}
    (hτ : Witness (gTop m) τ) (hν : Witness (gTop K) ν)
    (hmK : m ≤ K) (hbot : ∀ x, ν x = ⊥ → x = ⊥) :
    Witness (gTop m) (ν ∘ τ) where
  anti := hτ.anti
  vis := hτ.vis
  bot := by simp only [Function.comp_apply, hτ.bot, hν.bot]
  mono := hν.mono.comp hτ.mono
  clause5 := by
    intro x k hact i hi
    change ν (τ (extVisibilityReplace x k i)) =
      extVisibilityReplace (ν (τ x)) k i
    by_cases hk : k ≤ m
    · rw [hτ.clause5 x k (by rw [gTop_of_le hk]; exact le_top) i hi,
        hν.clause5 (τ x) k (by rw [gTop_of_le (hk.trans hmK)]; exact le_top) i hi]
    · have hz : ν (τ x) = ⊥ := by
        apply le_bot_iff.mp
        simpa only [Function.comp_apply, gTop_of_gt (not_le.mp hk)] using hact
      have ht : τ x = ⊥ := hbot _ hz
      rw [hτ.clause5 x k (by grind) i hi,
        ht, extVisibilityReplace_bot, hν.bot, extVisibilityReplace_bot]

/-- The two existing names for the normalized suppressor have the same definition. -/
theorem Transform.IsStepShifter.normalizedWitness {K : ℕ} {ν : ExtOrd → ExtOrd}
    (hν : IsStepShifter K ν) : Witness (gTop K) ν where
  anti := (witness_id K).anti
  vis := (witness_id K).vis
  bot := hν.map_bot
  mono := hν.mono
  clause5 := by
    intro x k hact i hi
    exact hν.clause5 x k hact i hi

/-- Adding ordinal zero to the finite inventory removes every nonbottom point
from the canonical normalizer's bottom fibre. -/
theorem canonicalNormalizer_reflects_bottom_of_zero_mem
    {S} {K} (h0 : (0 : Ordinal.{0}) ∈ S)
    x (hx : canonicalNormalizer S K x = ⊥) : x = ⊥ := by
  classical
  rcases ExtOrd.cases x with rfl | rfl | ⟨ξ, rfl⟩
  · rfl
  · rw [canonicalNormalizer_top] at hx
    exact False.elim (ofOrd_ne_bot _ hx)
  · have hfp : finitePart (0 : Ordinal.{0}) = 0 := by
      simpa only [Nat.cast_zero] using finitePart_natCast 0
    have hlim : limitPart (0 : Ordinal.{0}) = 0 := by
      simpa only [Nat.cast_zero] using limitPart_natCast 0
    have hitem := by
      simpa only [hlim] using
        (limitPart_mem_items (K := K) h0 (by rw [hfp]; exact Nat.zero_le K))
    have hpos : 0 < rank S K ξ := rank_pos_of_item hitem (zero_le (a := ξ))
    have hzero : rank S K ξ = 0 := (canonicalNormalizer_eq_bot_iff.mp hx).1
    exact False.elim ((Nat.ne_of_gt hpos) hzero)

/-- Transport one actual controller locality, after normalizing its witness.
The semantic source row is unchanged. -/
theorem map_capped_locality_of_bottom_reflecting
    {X} {grade} {E p : X → ExtOrd} {c}
    {K} {ν}
    (hmax : ∀ d, grade d ≤ grade c) (hcK : grade c ≤ K)
    (hvis : SelfVis (grade c) (p c))
    (hloc : TransformsTo grade E (fun d => min (p d) (p c)))
    (hν : Witness (gTop K) ν) (hbot : ∀ x, ν x = ⊥ → x = ⊥) :
    TransformsTo grade E (fun d => min (ν (p d)) (ν (p c))) := by
  obtain ⟨τ, hτ, _, hread⟩ := exists_bounded_exact_capped_witness hmax hvis hloc
  apply (hτ.comp_of_bottom_reflecting hν hcK hbot).transformsTo
  intro d
  simp only [Function.comp_apply, gTop_of_le (hmax d), min_top_right]
  rw [hread d, hν.mono.map_min]

section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D} {BJ : Finset ι × ℕ} {r : D.below BJ → ExtOrd} {K : ℕ}

/-- **Respect is closed under every bottom-reflecting `K`-step shifter**, with the semantic rows
unchanged (after the reviewer's decoder scout). -/
theorem RespectsSemanticsBelow.map_bottom_reflecting
    {ν : ExtOrd → ExtOrd}
    (hr : RespectsSemanticsBelow sem BJ r)
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    (hν : IsStepShifter K ν) (hbot : ∀ x, ν x = ⊥ → x = ⊥) :
    RespectsSemanticsBelow sem BJ (fun d => ν (r d)) where
  orderly d := (hν.selfVis (r d) (D.grade d.1) (hK d) (hr.orderly d).symm).symm
  locality Sig := by
    let c : D.below (D.cell Sig.1) := ⟨Sig.1, GradedLe.refl _⟩
    let p : D.below (D.cell Sig.1) → ExtOrd :=
      fun d => r (CellScheme.below.incl Sig d)
    have hmax : ∀ d : D.below (D.cell Sig.1), D.grade d.1 ≤ D.grade c.1 :=
      fun d => d.2.2
    have hcvis : SelfVis (D.grade c.1) (p c) := (hr.orderly Sig).symm
    have hloc : TransformsTo (fun d : D.below (D.cell Sig.1) => D.grade d.1)
        (sem.E Sig.1) (fun d => min (p d) (p c)) := hr.locality Sig
    exact map_capped_locality_of_bottom_reflecting hmax (hK Sig) hcvis hloc
      hν.normalizedWitness hbot
  availability Sig Xi₀ hscope hgrade := by
    obtain ⟨Xi, hcell, hle⟩ := hr.availability Sig Xi₀ hscope hgrade
    exact ⟨Xi, hcell, hν.mono hle⟩

/-- Respecting labellings are closed under the existing canonical normalizer
when zero is included in its inventory. This is a restricted NC theorem, not
an assertion of the repository's universally quantified NormalizationClosure. -/
theorem RespectsSemanticsBelow.canonical_of_zero_mem
    {S}
    (hr : RespectsSemanticsBelow sem BJ r)
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    (h0 : (0 : Ordinal.{0}) ∈ S) :
    RespectsSemanticsBelow sem BJ (fun d => canonicalNormalizer S K (r d)) :=
  hr.map_bottom_reflecting hK isStepShifter_canonicalNormalizer
    (canonicalNormalizer_reflects_bottom_of_zero_mem h0)

/-- The existential normalization needed for a finite inventory costs at most
one extra ordinal item. Existing coding and decoder results apply unchanged. -/
theorem RespectsSemanticsBelow.canonical_insert_zero
    S
    (hr : RespectsSemanticsBelow sem BJ r)
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K) :
    RespectsSemanticsBelow sem BJ (fun d => canonicalNormalizer (insert 0 S) K (r d)) := by
  exact hr.canonical_of_zero_mem hK (Finset.mem_insert_self _ _)

end

/-! ## The finite cover of a fixed finite lower domain -/

section FiniteCover

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

open Classical in
/-- The ordinal carried by a label (`0` at the endpoints). -/
noncomputable def ordOf (x : ExtOrd) : Ordinal.{0} :=
  if h : ∃ s : Ordinal.{0}, x = ofOrd s then h.choose else 0

theorem ordOf_ofOrd s : ordOf (ofOrd s) = s := by
  have h : ∃ t, ofOrd s = ofOrd t := ⟨s, rfl⟩
  unfold ordOf
  simp_all

/-- **Every respecting labelling of a finite lower domain has a respecting representative in one
uniformly bounded finite coded inventory, decoding exactly to it.**  With at most `m` cells and
grades at most `K`, the inventory is `codedAlphabet (m + 1) K`: the labelling's ordinal values
plus zero cost at most `m + 1` items. -/
theorem RespectsSemanticsBelow.exists_coded_representative {sem}
    {BJ} {r} {K m}
    (hr : RespectsSemanticsBelow sem BJ r) (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    (hm : Nat.card (D.below BJ) ≤ m) :
    ∃ (S : Finset Ordinal.{0}) (r' : D.below BJ → ExtOrd),
      RespectsSemanticsBelow sem BJ r' ∧ S.card ≤ m + 1 ∧
      (∀ d, r' d ∈ ExtOrd.codedAlphabet (m + 1) K) ∧
      (∀ d, canonicalDecoder S K (r' d) = r d) := by
  have hfin : Fintype (D.below BJ) := Fintype.ofFinite _
  obtain ⟨S₀, hS₀⟩ : ∃ S₀,
      S₀ = (Finset.univ : Finset (D.below BJ)).image fun d => ordOf (r d) := ⟨_, rfl⟩
  have hS₀card : S₀.card ≤ m := by
    refine le_trans ?_ hm
    simp_all
    exact Finset.card_image_le
  have hcard : (insert (0 : Ordinal.{0}) S₀).card ≤ m + 1 :=
    (Finset.card_insert_le _ _).trans (Nat.succ_le_succ hS₀card)
  refine ⟨insert 0 S₀, fun d => canonicalNormalizer (insert 0 S₀) K (r d),
    hr.canonical_insert_zero S₀ hK, hcard, fun d => canonicalNormalizer_mem_codedAlphabet hcard _,
    fun d => ?_⟩
  refine canonicalDecoder_canonicalNormalizer ?_
  rcases ExtOrd.cases (r d) with h | h | ⟨s, hs⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨s, Finset.mem_insert_of_mem ?_, hs⟩)
    rw [hS₀, Finset.mem_image]
    exact ⟨d, Finset.mem_univ _, by rw [hs, ordOf_ofOrd]⟩

end FiniteCover

/-! ## Decoder transport (after the reviewer's decoder scout) -/

section DecoderTransport

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

/-- The canonical decoder reflects bottom for every inventory: each nonbottom branch returns an
ordinal or `⊤`. -/
theorem canonicalDecoder_reflects_bottom
    {S} {K} x
    (hx : canonicalDecoder S K x = ⊥) : x = ⊥ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨ξ, rfl⟩
  · rfl
  · simp_all
  · exfalso
    by_cases hy : ξ < Ordinal.omega0 * (items S K).card
    · by_cases h0 : finitePart (blockItem S K ξ) = 0
      · rw [canonicalDecoder_interval hy h0] at hx
        exact ofOrd_ne_bot _ hx
      · by_cases hfp : finitePart ξ ≤ K
        · rw [canonicalDecoder_singLow hy h0 hfp] at hx
          exact ofOrd_ne_bot _ hx
        · rw [canonicalDecoder_singHigh hy h0 hfp] at hx
          exact ofOrd_ne_bot _ hx
    · rw [canonicalDecoder_topRegion hy] at hx
      exact top_ne_bot hx

/-- **Decoding preserves respect**, for every inventory, with the semantic rows unchanged. -/
theorem RespectsSemanticsBelow.decoded
    {sem} {BJ} {r : D.below BJ → ExtOrd}
    {K} S
    (hr : RespectsSemanticsBelow sem BJ r)
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K) :
    RespectsSemanticsBelow sem BJ (fun d => canonicalDecoder S K (r d)) :=
  hr.map_bottom_reflecting hK isStepShifter_canonicalDecoder canonicalDecoder_reflects_bottom

end DecoderTransport

end VaughtConjecture.Knight
