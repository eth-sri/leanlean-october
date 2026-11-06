/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.AlignedCutJoin

/-! # Encoding above a source cut without inverting the ambient witness

The low codes come from the old lawful source labelling, not from an inverse of
its shifter. Only prescribed outputs above the external cap get new tail codes.
The aligned paste is lawful and decodes literally. The source cut and the output
cap may differ; the latter need not belong to the source alphabet. Existence of
an aligned cut and room in a fixed alphabet remain explicit hypotheses.
-/

@[expose] public section

namespace VaughtConjecture.Knight.AlignedCutEncoding

open Transform Value ExtOrd SharpWitnessComposition AlignedCutJoin

private theorem tail_witness S K b :
    Witness (gTop K) (PaddedSourceDecoder.encode S K b) := by
  induction b with
  | zero => exact (isStepShifter_canonicalNormalizer (S := S) (K := K)).normalizedWitness
  | succ b ih =>
    exact ih.comp_of_bottom_reflecting (SourceBlockPadding.pad_step K).normalizedWitness
      le_rfl SourceBlockPadding.pad_reflects_bottom

section Finite

variable {X : Type*} [Fintype X]

section
variable (s p : X → ExtOrd) (K b : ℕ) (a γ : ExtOrd)

/-- Old low sources are retained; new high outputs receive separate codes. -/
noncomputable def encode  : X → ExtOrd :=
  AlignedCutJoin.paste s p a
    (above γ (PaddedSourceDecoder.encode (RelativePrefixEncoding.inventory p γ) K b))

theorem encode_of_le d (hd : p d ≤ γ) : encode s p K b a γ d = min (s d) a :=
  paste_of_le (fun _ h => above_of_le h) d hd

end

private theorem high_gap p {K b : ℕ} {a γ}
    (hroom : a < ofOrd (Ordinal.omega0 * b)) (d : X) (hd : γ < p d) :
    a < above γ (PaddedSourceDecoder.encode (RelativePrefixEncoding.inventory p γ) K b)
      (p d) := by
  rw [above_of_gt hd]
  exact hroom.trans_le (PaddedSourceDecoder.encode_ge_floor _
    (RelativePrefixEncoding.tracked_high p γ d hd) (ne_of_gt (bot_le.trans_lt hd)))

section
variable (s p : X → ExtOrd) {K b : ℕ} {a γ : ExtOrd}

theorem encode_of_gt (hroom : a < ofOrd (Ordinal.omega0 * b)) (d : X) (hd : γ < p d) :
    encode s p K b a γ d =
      PaddedSourceDecoder.encode (RelativePrefixEncoding.inventory p γ) K b (p d) := by
  rw [encode, paste_of_gt (high_gap p hroom) d hd, above_of_gt hd]

/-- Capped source agreement is derived from the alignment of raised outputs. -/
theorem encode_cap (hroom : a < ofOrd (Ordinal.omega0 * b))
    (halign : ∀ d, γ < p d → a ≤ s d) (d : X) :
    min (encode s p K b a γ d) a = min (s d) a :=
  AlignedCutJoin.paste_cap (fun _ h => above_of_le h) (high_gap p hroom) halign d

/-- Literal readback uses no inverse or identity-prefix hypothesis on `σ`.
Only the new high outputs are inserted into the decoder's finite inventory. -/
theorem decode_encode {σ} (hσ : Monotone σ)
    (hroom : a < ofOrd (Ordinal.omega0 * b)) (hactive : γ ≤ σ a)
    (hread : ∀ d, min (σ (s d)) γ = min (p d) γ) d :
    PaddedSourceDecoder.extend (RelativePrefixEncoding.inventory p γ) K b σ γ
      (encode s p K b a γ d) = p d := by
  by_cases hd : p d ≤ γ
  · rw [encode_of_le s p K b a γ d hd,
      PaddedSourceDecoder.extend_before _ ((min_le_right _ _).trans_lt hroom),
      hσ.map_min, min_assoc, min_eq_right hactive, hread d, min_eq_left hd]
  · rw [encode_of_gt s p hroom d (not_le.mp hd)]
    exact PaddedSourceDecoder.extend_encode _
      (RelativePrefixEncoding.tracked_high p γ d (not_le.mp hd)) (not_le.mp hd).le

end

end Finite

section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D} {BJ : Finset ι × ℕ}

/-- The new codes form a lawful face on the original rows, not just a scalar
solution of the prescribed equations. Source block repair supplies locality. -/
theorem encode_respects
    [Fintype (D.below BJ)]
    {s p} {K b : ℕ} {a γ}
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
    {X} [Fintype X]
    s p (incl : X → D.below BJ)
    {r q} {K b : ℕ} {a γ} {σ}
    (hr : RespectsSemanticsBelow sem BJ r) (hq : RespectsSemanticsBelow sem BJ q)
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    (hσ : Witness (gTop K) σ) (hγ : SelfVis K γ) (hγb : γ ≠ ⊥)
    (hroom : a < ofOrd (Ordinal.omega0 * b)) (hactive : γ ≤ σ a)
    (hsource : ∀ d, min (r d) a = min (s d) a)
    (hambient : ∀ d, min (σ (s d)) γ = min (q d) γ)
    (hface : ∀ d, min (p d) γ = min (q (incl d)) γ)
    (hlit : ∀ d, r (incl d) = encode (s ∘ incl) p K b a γ d) :
    ∃ q' : D.below BJ → ExtOrd, RespectsSemanticsBelow sem BJ q' ∧
      (∀ d, q' (incl d) = p d) ∧ ∀ d, min (q' d) γ = min (q d) γ := by
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
  exact decode_encode (s ∘ incl) p hσ.mono hroom hactive
    (fun e => (hambient (incl e)).trans (hface e).symm) d

end

end VaughtConjecture.Knight.AlignedCutEncoding
