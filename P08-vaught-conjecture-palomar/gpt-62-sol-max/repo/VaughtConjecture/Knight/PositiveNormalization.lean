/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.SetTheory.Cardinal.Finite
public import VaughtConjecture.Knight.WitnessAlgebra
public import VaughtConjecture.Knight.NormalForm

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
  bot := by simp [hτ.bot, hν.bot]
  mono := hν.mono.comp hτ.mono
  clause5 x k hact i hi := by
    change ν (τ (extVisibilityReplace x k i)) = extVisibilityReplace (ν (τ x)) k i
    rcases le_or_gt k m with hk | hk
    · rw [hτ.comm x hk hi, hν.comm (τ x) (hk.trans hmK) hi]
    · rw [gTop_of_gt hk, le_bot_iff] at hact
      change ν (τ x) = ⊥ at hact
      rw [hτ.zero_repl x (hbot _ hact) k hi, hν.bot, hact, extVisibilityReplace_bot]

/-- Adding ordinal zero to the finite inventory removes every nonbottom point
from the canonical normalizer's bottom fibre. -/
theorem canonicalNormalizer_reflects_bottom_of_zero_mem
    {S : Finset Ordinal.{0}} {K : ℕ} (h0 : (0 : Ordinal.{0}) ∈ S)
    (x : ExtOrd) (hx : canonicalNormalizer S K x = ⊥) : x = ⊥ := by
  classical
  rcases ExtOrd.cases x with rfl | rfl | ⟨ξ, rfl⟩
  · rfl
  · trivial
  · have hfp : finitePart (0 : Ordinal.{0}) = 0 := by
      simpa [Nat.cast_zero] using finitePart_natCast 0
    have hlim : limitPart (0 : Ordinal.{0}) = 0 := by
      simpa [Nat.cast_zero] using limitPart_natCast 0
    have hitem : (0 : Ordinal.{0}) ∈ items S K := by
      simpa [hlim] using
        (limitPart_mem_items (K := K) h0 (by omega))
    have hpos : 0 < rank S K ξ := rank_pos_of_item hitem (zero_le (a := ξ))
    have hzero : rank S K ξ = 0 := (canonicalNormalizer_eq_bot_iff.mp hx).1
    omega

/-- Transport one actual controller locality, after normalizing its witness.
The semantic source row is unchanged. -/
theorem map_capped_locality_of_bottom_reflecting
    {X : Type*} {grade : X → ℕ} {E p : X → ExtOrd} {c : X}
    {K : ℕ} {ν : ExtOrd → ExtOrd}
    (hmax : ∀ d, grade d ≤ grade c) (hcK : grade c ≤ K)
    (hvis : SelfVis (grade c) (p c))
    (hloc : TransformsTo grade E (fun d => min (p d) (p c)))
    (hν : Witness (gTop K) ν) (hbot : ∀ x, ν x = ⊥ → x = ⊥) :
    TransformsTo grade E (fun d => min (ν (p d)) (ν (p c))) := by
  obtain ⟨τ, hτ, _, hread⟩ := exists_bounded_exact_capped_witness hmax hvis hloc
  exact (hτ.comp_of_bottom_reflecting hν hcK hbot).transformsTo_top hmax
    (fun d => by rw [Function.comp_apply, hread d, hν.mono.map_min])

namespace RespectsSemanticsBelow

section Map

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ : Finset ι × ℕ} {r : D.below BJ → ExtOrd}
  {K : ℕ} {ν : ExtOrd → ExtOrd}

abbrev LocalityAt (sem : Semantics D) (r : D.below BJ → ExtOrd) (c : D.below BJ) : Prop :=
  TransformsTo (fun d : D.below (D.cell c.1) => D.grade d.1) (sem.E c.1)
    (fun d => min (r (CellScheme.below.incl c d)) (r c))

/-- Only the owner locality must be checked again under a witness. -/
theorem map_of_locality (hr : RespectsSemanticsBelow sem BJ r)
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K) (hν : Witness (gTop K) ν)
    (hl : ∀ c, LocalityAt sem (ν ∘ r) c) : RespectsSemanticsBelow sem BJ (ν ∘ r) where
  orderly d := by
    have h := hν.comm (r d) (hK d) le_rfl
    rwa [← hr.orderly d] at h
  locality := hl
  availability d c hs hg := by
    obtain ⟨e, he, hde⟩ := hr.availability d c hs hg
    exact ⟨e, he, hν.mono hde⟩

/-- A bottom-reflecting step witness preserves lawfulness on any lower set. -/
theorem map_bottom_reflecting (hr : RespectsSemanticsBelow sem BJ r)
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    (hν : Witness (gTop K) ν) (hbot : ∀ x, ν x = ⊥ → x = ⊥) :
    RespectsSemanticsBelow sem BJ (ν ∘ r) :=
  hr.map_of_locality hK hν fun c => map_capped_locality_of_bottom_reflecting
    (c := (⟨c.1, GradedLe.refl _⟩ : D.below (D.cell c.1)))
    (p := fun d => r (CellScheme.below.incl c d))
    (fun d => d.2.2) (hK c) (hr.orderly c).symm (hr.locality c) hν hbot

end Map

end RespectsSemanticsBelow

/-- Respecting labellings are closed under the existing canonical normalizer
when zero is included in its inventory. This is a restricted NC theorem, not
an assertion of the repository's universally quantified NormalizationClosure. -/
theorem RespectsSemanticsBelow.canonical_of_zero_mem
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {BJ : Finset ι × ℕ} {r : D.below BJ → ExtOrd}
    {K : ℕ} {S : Finset Ordinal.{0}}
    (hr : RespectsSemanticsBelow sem BJ r)
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    (h0 : (0 : Ordinal.{0}) ∈ S) :
    RespectsSemanticsBelow sem BJ (fun d => canonicalNormalizer S K (r d)) :=
  hr.map_bottom_reflecting hK isStepShifter_canonicalNormalizer.normalizedWitness
    (canonicalNormalizer_reflects_bottom_of_zero_mem h0)

/-- The existential normalization needed for a finite inventory costs at most
one extra ordinal item. Existing coding and decoder results apply unchanged. -/
theorem RespectsSemanticsBelow.canonical_insert_zero
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {BJ : Finset ι × ℕ} {r : D.below BJ → ExtOrd}
    {K : ℕ} (S : Finset Ordinal.{0})
    (hr : RespectsSemanticsBelow sem BJ r)
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K) :
    RespectsSemanticsBelow sem BJ (fun d => canonicalNormalizer (insert 0 S) K (r d)) := by
  classical
  exact hr.canonical_of_zero_mem hK (Finset.mem_insert_self _ _)

section FiniteCover

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

open Classical in
/-- The ordinal carried by a label (`0` at the endpoints). -/
noncomputable def ordOf (x : ExtOrd) : Ordinal.{0} :=
  if h : ∃ s : Ordinal.{0}, x = ofOrd s then h.choose else 0

theorem ordOf_ofOrd (s : Ordinal.{0}) : ordOf (ofOrd s) = s := by
  unfold ordOf
  simp

/-- **Every respecting labelling of a finite lower domain has a respecting representative in one
uniformly bounded finite coded inventory, decoding exactly to it.**  With at most `m` cells and
grades at most `K`, the inventory is `codedAlphabet (m + 1) K`: the labelling's ordinal values
plus zero cost at most `m + 1` items. -/
theorem RespectsSemanticsBelow.exists_coded_representative {sem : Semantics D}
    {BJ : Finset ι × ℕ} {r : D.below BJ → ExtOrd} {K m : ℕ}
    (hr : RespectsSemanticsBelow sem BJ r) (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    (hm : Nat.card (D.below BJ) ≤ m) :
    ∃ (S : Finset Ordinal.{0}) (r' : D.below BJ → ExtOrd),
      RespectsSemanticsBelow sem BJ r' ∧ S.card ≤ m + 1 ∧
      (∀ d, r' d ∈ ExtOrd.codedAlphabet (m + 1) K) ∧
      (∀ d, canonicalDecoder S K (r' d) = r d) := by
  have hfin : Fintype (D.below BJ) := Fintype.ofFinite _
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Finset Ordinal.{0},
      S₀ = (Finset.univ : Finset (D.below BJ)).image fun d => ordOf (r d) := ⟨_, rfl⟩
  have hS₀card : S₀.card ≤ m := by
    refine le_trans ?_ hm
    rw [hS₀, Nat.card_eq_fintype_card, ← Finset.card_univ]
    grind
  have hcard : (insert (0 : Ordinal.{0}) S₀).card ≤ m + 1 :=
    by grind
  refine ⟨insert 0 S₀, fun d => canonicalNormalizer (insert 0 S₀) K (r d),
    hr.canonical_insert_zero S₀ hK, hcard, fun d => canonicalNormalizer_mem_codedAlphabet hcard _,
    fun d => ?_⟩
  refine canonicalDecoder_canonicalNormalizer ?_
  rcases ExtOrd.cases (r d) with h | h | ⟨s, hs⟩
  · tauto
  · tauto
  · refine Or.inr (Or.inr ⟨s, Finset.mem_insert_of_mem ?_, hs⟩)
    rw [hS₀, Finset.mem_image]
    exact ⟨d, Finset.mem_univ _, by rw [hs, ordOf_ofOrd]⟩

end FiniteCover

section DecoderTransport

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

/-- **Decoding preserves respect**, for every inventory, with the semantic rows unchanged. -/
theorem RespectsSemanticsBelow.decoded
    {sem : Semantics D} {BJ : Finset ι × ℕ} {r : D.below BJ → ExtOrd}
    {K : ℕ} (S : Finset Ordinal.{0})
    (hr : RespectsSemanticsBelow sem BJ r)
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K) :
    RespectsSemanticsBelow sem BJ (fun d => canonicalDecoder S K (r d)) :=
  hr.map_bottom_reflecting hK isStepShifter_canonicalDecoder.normalizedWitness canonicalDecoder_reflects_bottom

end DecoderTransport

end VaughtConjecture.Knight
