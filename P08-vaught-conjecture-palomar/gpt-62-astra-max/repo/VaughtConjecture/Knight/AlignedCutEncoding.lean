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

open Transform Value ExtOrd SharpWitnessComposition AlignedCutJoin PaddedSourceDecoder

private theorem tail_witness K b :
    Witness (gTop K) (reserve b) := by
  induction b with
  | zero => exact witness_id K
  | succ b ih =>
    exact ih.comp_of_bottom_reflecting (SourceBlockPadding.pad_step K).normalizedWitness
      le_rfl SourceBlockPadding.pad_reflects_bottom

section Finite

variable {X : Type*}

/-- Old low sources are retained; new high outputs receive separate codes. -/
noncomputable def encode (s p : X → ExtOrd) (b : ℕ) (a γ : ExtOrd) : X → ExtOrd :=
  AlignedCutJoin.paste s p a
    (above γ (reserve b))

theorem encode_of_le s p (b : ℕ) a γ
    (d : X) (hd : p d ≤ γ) : encode s p b a γ d = min (s d) a :=
  paste_of_le (fun _ h => above_of_le h) d hd

private theorem high_gap (p : X → ExtOrd) {b : ℕ} {a γ : ExtOrd}
    (hroom : a < ofOrd (Ordinal.omega0 * b)) (d : X) (hd : γ < p d) :
    a < above γ (reserve b)
      (p d) := by
  rw [above_of_gt hd]
  exact hroom.trans_le (floor_le_reserve (ne_of_gt (bot_le.trans_lt hd)))

theorem encode_of_gt s p {b : ℕ} {a γ}
    (hroom : a < ofOrd (Ordinal.omega0 * b)) (d : X) (hd : γ < p d) :
    encode s p b a γ d =
      reserve b (p d) := by
  rw [encode, paste_of_gt (high_gap p hroom) d hd, above_of_gt hd]

/-- Capped source agreement is derived from the alignment of raised outputs. -/
theorem encode_cap s p {b : ℕ} {a γ}
    (hroom : a < ofOrd (Ordinal.omega0 * b))
    (halign : ∀ d, γ < p d → a ≤ s d) (d : X) :
    min (encode s p b a γ d) a = min (s d) a :=
  AlignedCutJoin.paste_cap (fun _ h => above_of_le h) (high_gap p hroom) halign d

/-- Literal readback uses no inverse or identity-prefix hypothesis on `σ`.
Only the new high outputs are inserted into the decoder's finite inventory. -/
theorem decode_encode s p {b : ℕ} {a γ}
    {σ} (hσ : Monotone σ)
    (hroom : a < ofOrd (Ordinal.omega0 * b)) (hactive : γ ≤ σ a)
    (hread : ∀ d, min (σ (s d)) γ = min (p d) γ) (d : X) :
    extend b σ γ
      (encode s p b a γ d) = p d := by
  by_cases hd : p d ≤ γ
  · rw [encode_of_le s p b a γ d hd,
      extend_before ((min_le_right _ _).trans_lt hroom),
      hσ.map_min, min_assoc, min_eq_right hactive, hread d, min_eq_left hd]
  · rw [encode_of_gt s p hroom d (not_le.mp hd)]
    exact extend_reserve (not_le.mp hd).le

end Finite

/-- The new codes form a lawful face on the original rows, not just a scalar
solution of the prescribed equations. Source block repair supplies locality. -/
theorem encode_respects
    {ι : Type*} [DecidableEq ι] {A} {D : CellScheme A}
    {sem} {BJ : Finset ι × ℕ}
    {s p : D.SectionAt BJ} {K b : ℕ} {a γ}
    (hs : RespectsSemanticsBelow sem BJ s) (hp : RespectsSemanticsBelow sem BJ p)
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    (ha : SelfVis K a) (hab : a ≠ ⊥) (hγ : SelfVis K γ)
    (hroom : a < ofOrd (Ordinal.omega0 * b))
    (halign : ∀ d, γ < p d → a ≤ s d) :
    RespectsSemanticsBelow sem BJ (encode s p b a γ) :=
  paste_respects hs hp hK ha hab
    (above_bounded (boundedMap_of_witness (tail_witness K b)) hγ)
    (fun _ h => above_of_le h) (high_gap p hroom) halign

end VaughtConjecture.Knight.AlignedCutEncoding
