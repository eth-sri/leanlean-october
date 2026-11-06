
import VaughtConjecture.Knight.PointwiseLabels
import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.AlignedCutJoin

/-! # Encoding above a source cut without inverting the ambient witness

The low codes come from the old lawful source labelling, not from an inverse of
its shifter. Only prescribed outputs above the external cap get new tail codes.
The aligned paste is lawful and decodes literally. The source cut and the output
cap may differ; the latter need not belong to the source alphabet. Existence of
an aligned cut and room in a fixed alphabet remain explicit hypotheses.
-/

namespace VaughtConjecture.Knight.AlignedCutEncoding

open Transform  ExtOrd SharpWitnessComposition AlignedCutJoin

private theorem tail_witness S K b :
    Witness (gTop K) (PaddedSourceDecoder.encode S K b) := by
  induction b with
  | zero => exact (isStepShifter_canonicalNormalizer  ).normalizedWitness
  | succ b ih =>
    exact ih.comp_of_bottom_reflecting (SourceBlockPadding.pad_step K).normalizedWitness
      le_rfl SourceBlockPadding.pad_reflects_bottom

section

variable {X : Type*} [Fintype X]

/-- Old low sources are retained; new high outputs receive separate codes. -/
noncomputable def encode (s p : X → ExtOrd) (K b : ℕ) (a γ : ExtOrd) :=
  AlignedCutJoin.paste s p a
    (above γ (PaddedSourceDecoder.encode (RelativePrefixEncoding.inventory p γ) K b))

theorem encode_of_le {s p : X → ExtOrd} {K b : ℕ} {a γ : ExtOrd}
    {d : X} (hd : p d ≤ γ) : encode s p K b a γ d = min (s d) a :=
  paste_of_le (fun _ h => above_of_le h) d hd

private theorem high_gap (p : X → ExtOrd) {K b : ℕ} {a γ : ExtOrd}
    (hroom : a < ofOrd (Ordinal.omega0 * b)) (d : X) (hd : γ < p d) :
    a < above γ (PaddedSourceDecoder.encode (RelativePrefixEncoding.inventory p γ) K b)
      (p d) := by
  rw [above_of_gt hd]
  exact hroom.trans_le (PaddedSourceDecoder.encode_ge_floor _
    (RelativePrefixEncoding.tracked_high p γ d hd) (ne_of_gt (bot_le.trans_lt hd)))

theorem encode_of_gt (s p : X → ExtOrd) {K b : ℕ} {a γ : ExtOrd}
    (hroom : a < ofOrd (Ordinal.omega0 * b)) (d : X) (hd : γ < p d) :
    encode s p K b a γ d =
      PaddedSourceDecoder.encode (RelativePrefixEncoding.inventory p γ) K b (p d) := by
  rw [encode, paste_of_gt (high_gap p hroom) d hd, above_of_gt hd]

/-- Capped source agreement is derived from the alignment of raised outputs. -/
theorem encode_cap {s p : X → ExtOrd} {K b : ℕ} {a γ : ExtOrd}
    (hroom : a < ofOrd (Ordinal.omega0 * b))
    (halign : ∀ d, γ < p d → a ≤ s d) {d : X} :
    min (encode s p K b a γ d) a = min (s d) a :=
  AlignedCutJoin.paste_cap (fun _ h => above_of_le h) (high_gap p hroom) halign d

/-- Literal readback uses no inverse or identity-prefix hypothesis on `σ`.
Only the new high outputs are inserted into the decoder's finite inventory. -/
theorem decode_encode {s p : X → ExtOrd} {K b : ℕ} {a γ : ExtOrd}
    {σ : LabelMap} (hσ : Monotone σ)
    (hroom : a < ofOrd (Ordinal.omega0 * b)) (hactive : γ ≤ σ a)
    (hread : ∀ d, min (σ (s d)) γ = min (p d) γ) (d : X) :
    PaddedSourceDecoder.extend (RelativePrefixEncoding.inventory p γ) K b σ γ
      (encode s p K b a γ d) = p d := by
  by_cases hd : p d ≤ γ
  · rw [encode_of_le hd,
      PaddedSourceDecoder.extend_before _ ((min_le_right _ _).trans_lt hroom),
      hσ.map_min, min_assoc, min_eq_right hactive, hread d, min_eq_left hd]
  · rw [encode_of_gt s p hroom d (not_le.mp hd)]
    exact PaddedSourceDecoder.extend_encode _
      (RelativePrefixEncoding.tracked_high p γ d (not_le.mp hd)) (not_le.mp hd).le

end

/-- The new codes form a lawful face on the original rows, not just a scalar
solution of the prescribed equations. Source block repair supplies locality. -/
theorem encode_respects
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {BJ : GradedIndex ι} [Fintype (D.below BJ)]
    {s p : BelowLabels D BJ} {K b : ℕ} {a γ : ExtOrd}
    (hs : RespectsSemanticsBelow sem BJ s) (hp : RespectsSemanticsBelow sem BJ p)
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    (ha : SelfVis K a) (hab : a ≠ ⊥) (hγ : SelfVis K γ)
    (hroom : a < ofOrd (Ordinal.omega0 * b))
    (halign : ∀ d, γ < p d → a ≤ s d) :
    RespectsSemanticsBelow sem BJ (encode s p K b a γ) :=
  paste_respects hs hp hK ha hab
    (above_bounded (boundedMap_of_witness (tail_witness _ K b)) hγ)
    (fun _ h => above_of_le h) (high_gap p hroom) halign

/-- Decode an independently constructed coded lift. Agreement at the source
cut preserves every ambient output cap, and positive-cap transport proves
respect of the output without assuming faithful transformations compose. -/
theorem decode_lift
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {BJ : GradedIndex ι} {X : Type*} [Fintype X]
    (s : BelowLabels D BJ) (p : X → ExtOrd) (incl : X → D.below BJ)
    {r q : BelowLabels D BJ} {K b : ℕ} {a γ : ExtOrd} {σ : LabelMap}
    (hr : RespectsSemanticsBelow sem BJ r) (hq : RespectsSemanticsBelow sem BJ q)
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    (hσ : Witness (gTop K) σ) (hγ : SelfVis K γ) (hγb : γ ≠ ⊥)
    (hroom : a < ofOrd (Ordinal.omega0 * b)) (hactive : γ ≤ σ a)
    (hsource : CappedEq r s a)
    (hambient : CappedEq (σ ∘ s) q γ)
    (hface : CappedEq p (q ∘ incl) γ)
    (hlit : ∀ d, r (incl d) = encode (s ∘ incl) p K b a γ d) :
    ∃ q' , RespectsSemanticsBelow sem BJ q' ∧
      (PointwiseEq (q' ∘ incl) p) ∧ CappedEq q' q γ := by
  let S := RelativePrefixEncoding.inventory p γ
  let τ := PaddedSourceDecoder.extend S K b σ γ
  have hτ : Witness (gTop K) τ := PaddedSourceDecoder.extend_witness S hσ hγ
  have hag d : min (τ (r d)) γ = min (q d) γ :=
    (PaddedSourceDecoder.extend_cap_agreement S hσ hγ hroom hactive (hsource d)).trans
      (hambient d)
  refine ⟨fun d => τ (r d),
    map_respects_of_positive_cap_agreement hr hq hK (boundedMap_of_witness hτ) hγb hag,
    ?_, hag⟩
  intro d
  change PaddedSourceDecoder.extend S K b σ γ (r (incl d)) = p d
  rw [hlit d]
  exact decode_encode hσ.mono hroom hactive
    (fun e => (hambient (incl e)).trans (hface e).symm) d

