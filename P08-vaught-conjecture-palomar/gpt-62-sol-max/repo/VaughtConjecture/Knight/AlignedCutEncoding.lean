/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.AlignedCutJoin

@[expose] public section

namespace VaughtConjecture.Knight.AlignedCutEncoding

open Transform Value ExtOrd SharpWitnessComposition AlignedCutJoin

private theorem tail_witness (S : Finset Ordinal.{0}) (K b : ℕ) :
    Witness (gTop K) (PaddedSourceDecoder.encode S K b) := by
  induction b with
  | zero => exact (isStepShifter_canonicalNormalizer (S := S) (K := K)).normalizedWitness
  | succ b ih =>
    exact ih.comp_of_bottom_reflecting (SourceBlockPadding.pad_step K).normalizedWitness
      le_rfl SourceBlockPadding.pad_reflects_bottom

section Finite

variable {X : Type*} [Fintype X]

/-- Old low sources are retained; new high outputs receive separate codes. -/
noncomputable def encode (s p : X → ExtOrd) (K b : ℕ) (a γ : ExtOrd) : X → ExtOrd :=
  AlignedCutJoin.paste s p a
    (above γ (PaddedSourceDecoder.encode (RelativePrefixEncoding.inventory p γ) K b))

theorem encode_of_le (s p : X → ExtOrd) (K b : ℕ) (a γ : ExtOrd)
    (d : X) (hd : p d ≤ γ) : encode s p K b a γ d = min (s d) a :=
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

theorem encode_ne_top {s p : X → ExtOrd} {K b : ℕ} {a γ : ExtOrd}
    (hroom : a < ofOrd (Ordinal.omega0 * b)) (d : X) : encode s p K b a γ d ≠ ⊤ := by
  by_cases hd : p d ≤ γ
  · rw [encode_of_le _ _ _ _ _ _ d hd]
    exact ne_of_lt ((min_le_right _ _).trans_lt (hroom.trans (ofOrd_lt_top _)))
  · rw [encode_of_gt _ _ hroom d (not_le.mp hd)]
    rcases mem_codedAlphabet_iff.mp (PaddedSourceDecoder.encode_mem _ K b (p d)) with h | ⟨_, _, _, _, h⟩
    · exact h.trans_ne bot_ne_top
    · exact h.trans_ne (ofOrd_ne_top _)

/-- Capped source agreement is derived from the alignment of raised outputs. -/
theorem encode_cap (s p : X → ExtOrd) {K b : ℕ} {a γ : ExtOrd}
    (hroom : a < ofOrd (Ordinal.omega0 * b))
    (halign : ∀ d, γ < p d → a ≤ s d) (d : X) :
    min (encode s p K b a γ d) a = min (s d) a :=
  AlignedCutJoin.paste_cap (fun _ h => above_of_le h) (high_gap p hroom) halign d

/-- Literal readback uses no inverse or identity-prefix hypothesis on `σ`.
Only the new high outputs are inserted into the decoder's finite inventory. -/
theorem decode_encode (s p : X → ExtOrd) {K b : ℕ} {a γ : ExtOrd}
    {σ : ExtOrd → ExtOrd} (hσ : Monotone σ)
    (hroom : a < ofOrd (Ordinal.omega0 * b)) (hactive : γ ≤ σ a)
    (hread : ∀ d, min (σ (s d)) γ = min (p d) γ) (d : X) :
    PaddedSourceDecoder.extend (RelativePrefixEncoding.inventory p γ) K b σ γ
      (encode s p K b a γ d) = p d := by
  by_cases hd : p d ≤ γ
  · rw [encode_of_le s p K b a γ d hd,
      PaddedSourceDecoder.extend_before _ ((min_le_right _ _).trans_lt hroom),
      hσ.map_min, min_assoc, min_eq_right hactive, hread d, min_eq_left hd]
  · rw [encode_of_gt s p hroom d (not_le.mp hd)]
    exact PaddedSourceDecoder.extend_encode _
      (RelativePrefixEncoding.tracked_high p γ d (not_le.mp hd)) (not_le.mp hd).le

end Finite

/-- The new codes form a lawful face on the original rows, not just a scalar
solution of the prescribed equations. Source block repair supplies locality. -/
theorem encode_respects
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {BJ : Finset ι × ℕ} [Fintype (D.below BJ)]
    {s p : D.below BJ → ExtOrd} {K b : ℕ} {a γ : ExtOrd}
    (hs : RespectsSemanticsBelow sem BJ s) (hp : RespectsSemanticsBelow sem BJ p)
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    (ha : SelfVis K a) (hab : a ≠ ⊥) (hγ : SelfVis K γ)
    (hroom : a < ofOrd (Ordinal.omega0 * b))
    (halign : ∀ d, γ < p d → a ≤ s d) :
    RespectsSemanticsBelow sem BJ (encode s p K b a γ) :=
  paste_respects hs hp hK ha hab
    (above_bounded ((tail_witness _ K b).bounded) hγ)
    (fun _ h => above_of_le h) (high_gap p hroom) halign

/-- Decode at the retuned face cut, then check lawfulness at the protected ambient cap. -/
theorem decode_lift
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {BJ : Finset ι × ℕ} {X : Type*} [Fintype X]
    (s : D.below BJ → ExtOrd) (p : X → ExtOrd) (incl : X → D.below BJ)
    {r q : D.below BJ → ExtOrd} {K b : ℕ} {a γ δ : ExtOrd} {σ : ExtOrd → ExtOrd}
    (hr : RespectsSemanticsBelow sem BJ r) (hq : RespectsSemanticsBelow sem BJ q)
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    (hσ : Witness (gTop K) σ) (hδ : SelfVis K δ) (hγb : γ ≠ ⊥) (hγδ : γ ≤ δ)
    (hroom : a < ofOrd (Ordinal.omega0 * b)) (hactive : δ ≤ σ a)
    (hsource : ∀ d, min (r d) a = min (s d) a)
    (hambient : ∀ d, min (σ (s d)) γ = min (q d) γ)
    (hface : ∀ d, min (p d) δ = min (σ (s (incl d))) δ)
    (hlit : ∀ d, r (incl d) = encode (s ∘ incl) p K b a δ d) :
    ∃ q' : D.below BJ → ExtOrd, RespectsSemanticsBelow sem BJ q' ∧
      (∀ d, q' (incl d) = p d) ∧ ∀ d, min (q' d) γ = min (q d) γ := by
  let S := RelativePrefixEncoding.inventory p δ
  let τ := PaddedSourceDecoder.extend S K b σ δ
  have hτ := PaddedSourceDecoder.extend_witness S (b := b) hσ hδ
  have hag d : min (τ (r d)) γ = min (q d) γ := by
    have he := PaddedSourceDecoder.extend_cap_agreement S hσ hδ hroom hactive (hsource d)
    exact (show min (τ (r d)) γ = min (σ (s d)) γ by
      simpa only [min_assoc, min_eq_right hγδ] using congrArg (min · γ) he).trans (hambient d)
  refine ⟨fun d => τ (r d),
    map_respects_of_positive_cap_agreement hr hq hK (hτ.bounded) hγb hag,
    ?_, hag⟩
  intro d
  change PaddedSourceDecoder.extend S K b σ δ (r (incl d)) = p d
  rw [hlit d]
  exact decode_encode (s ∘ incl) p hσ.mono hroom hactive
    (fun e => (hface e).symm) d

end VaughtConjecture.Knight.AlignedCutEncoding
