/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CapFirstScalar
public import VaughtConjecture.Knight.SourceBlockPadding

@[expose] public section

namespace VaughtConjecture.Knight.PaddedSourceDecoder

open Transform Value ExtOrd SharpWitnessComposition SourceBlockPadding

/-- Move nonbottom sources by `b` whole blocks. -/
noncomputable def reserve : ℕ → ExtOrd → ExtOrd
  | 0, x => x
  | b + 1, x => pad (reserve b x)

/-- Erase the reserved blocks; every erased block is killed in its entirety. -/
noncomputable def release : ℕ → ExtOrd → ExtOrd
  | 0, x => x
  | b + 1, x => release b (unpad x)

@[simp] theorem reserve_bot (b : ℕ) : reserve b ⊥ = ⊥ := by
  induction b with
  | zero => rfl
  | succ b ih => simp only [reserve, ih, pad_bot]

/-- The inverse is literal at every padded source, including bottom and top. -/
theorem release_reserve (b : ℕ) (x : ExtOrd) : release b (reserve b x) = x := by
  induction b with
  | zero => rfl
  | succ b ih => simpa [reserve, release, unpad_pad] using ih

/-- Repeated source padding preserves the finite part exactly. -/
theorem reserve_code (b u j : ℕ) : reserve b (ofOrd (Ordinal.omega0 * u + j)) =
    ofOrd (Ordinal.omega0 * (u + b : ℕ) + j) := by
  induction b with
  | zero => rfl
  | succ b ih => rw [reserve, ih, pad_code, Nat.add_assoc]

/-- Precomposition is justified by exact replacement commutation, not transitivity. -/
theorem witness_release {g : ℕ → ExtOrd} {τ : ExtOrd → ExtOrd}
    (hτ : Witness g τ) (b : ℕ) : Witness g (fun x => τ (release b x)) := by
  induction b with
  | zero => exact hτ
  | succ b ih => exact witness_precompose_unpad ih

private theorem unpad_lt_floor {b : ℕ} {x : ExtOrd}
    (hx : x < ofOrd (Ordinal.omega0 * (b + 1 : ℕ))) :
    unpad x < ofOrd (Ordinal.omega0 * b) := by
  classical
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · simp
  · trivial
  · by_cases hα : Ordinal.omega0 ≤ α
    · have he : pad (unpad (ofOrd α)) = ofOrd α := by
        rw [unpad_ofOrd, ite_eq_left hα, pad_ofOrd, Ordinal.add_sub_cancel_of_le hα]
      have hp : pad (ofOrd (Ordinal.omega0 * b)) =
          ofOrd (Ordinal.omega0 * (b + 1 : ℕ)) := by
        simpa [Nat.cast_zero, add_zero] using pad_code b 0
      by_contra hn
      have hle := pad_mono (not_lt.mp hn)
      grind
    · rw [unpad_ofOrd, ite_eq_right hα]
      exact bot_lt_ofOrd _

/-- The decoder sees bottom on the entire reserved prefix, not just listed sources. -/
theorem release_eq_bot_of_lt {b : ℕ} {x : ExtOrd}
    (hx : x < ofOrd (Ordinal.omega0 * b)) : release b x = ⊥ := by
  induction b generalizing x with
  | zero =>
    change x = ⊥
    rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
    all_goals simp_all
  | succ b ih => exact ih (unpad_lt_floor hx)

/-- An alphabet of block bound `t` moves to block bound `t + b`. -/
theorem reserve_mem_codedAlphabet {t K : ℕ} {x : ExtOrd}
    (hx : x ∈ ExtOrd.codedAlphabet t K) (b : ℕ) :
    reserve b x ∈ ExtOrd.codedAlphabet (t + b) K := by
  rcases mem_codedAlphabet_iff.mp hx with rfl | ⟨u, j, hu, hj, rfl⟩
  · exact mem_codedAlphabet_iff.mpr (Or.inl (reserve_bot b))
  · exact mem_codedAlphabet_iff.mpr
      (Or.inr ⟨u + b, j, Nat.add_le_add_right hu b, hj, reserve_code b u j⟩)

/-- The actual finite tail code. Original literal top is represented by a proper code. -/
noncomputable def encode (S : Finset Ordinal.{0}) (K b : ℕ) (y : ExtOrd) : ExtOrd :=
  reserve b (canonicalNormalizer S K y)

/-- Exact alphabet accounting: no availability of this much room in a tower is assumed. -/
theorem encode_mem (S : Finset Ordinal.{0}) (K b : ℕ) (y : ExtOrd) :
    encode S K b y ∈ ExtOrd.codedAlphabet (S.card + b) K :=
  reserve_mem_codedAlphabet (canonicalNormalizer_mem_codedAlphabet le_rfl y) b

/-- Exact readback before taking any maximum with the old witness. -/
theorem decode_encode (S : Finset Ordinal.{0}) {K b : ℕ} {y : ExtOrd}
    (hy : y = ⊥ ∨ y = ⊤ ∨ ∃ α ∈ S, y = ofOrd α) :
    canonicalDecoder S K (release b (encode S K b y)) = y := by
  rw [encode, release_reserve, canonicalDecoder_canonicalNormalizer hy]

/-- Every nonbottom tracked target really is placed beyond the reserved blocks. -/
theorem encode_ge_floor (S : Finset Ordinal.{0}) {K b : ℕ} {y : ExtOrd}
    (hy : y = ⊥ ∨ y = ⊤ ∨ ∃ α ∈ S, y = ofOrd α) (hyb : y ≠ ⊥) :
    ofOrd (Ordinal.omega0 * b) ≤ encode S K b y := by
  by_contra hn
  have he := decode_encode (K := K) (b := b) S hy
  simp_all [release_eq_bot_of_lt]

/-- Join a clipped old witness to the new decoder. The join uses existing normalized
witness closure; its decoder is precomposed only with the exact source inverse. -/
noncomputable def extend (S : Finset Ordinal.{0}) (K b : ℕ)
    (σ : ExtOrd → ExtOrd) (γ : ExtOrd) (x : ExtOrd) : ExtOrd :=
  max (min (σ x) γ) (canonicalDecoder S K (release b x))

/-- The extension is globally faithful, including the higher-threshold bottom clauses. -/
theorem extend_witness (S : Finset Ordinal.{0}) {K b : ℕ}
    {σ : ExtOrd → ExtOrd} {γ : ExtOrd}
    (hσ : Witness (gTop K) σ) (hγ : SelfVis K γ) :
    Witness (gTop K) (extend S K b σ γ) :=
  (FreeDiagonal.clip_witness hσ hγ).max
    (witness_release (isStepShifter_canonicalDecoder (S := S) (K := K)).normalizedWitness b)

/-- Every value before the tail remains exactly the old value capped at `γ`. -/
theorem extend_before (S : Finset Ordinal.{0}) {K b : ℕ}
    {σ : ExtOrd → ExtOrd} {γ x : ExtOrd} (hx : x < ofOrd (Ordinal.omega0 * b)) :
    extend S K b σ γ x = min (σ x) γ := by
  rw [extend, release_eq_bot_of_lt hx, canonicalDecoder_bot, max_bot_right]

/-- New high targets are read literally, with no restriction on their finite part.
Bottom is allowed when the cap is bottom; top is handled by its proper code. -/
theorem extend_encode (S : Finset Ordinal.{0}) {K b : ℕ}
    {σ : ExtOrd → ExtOrd} {γ y : ExtOrd}
    (hy : y = ⊥ ∨ y = ⊤ ∨ ∃ α ∈ S, y = ofOrd α) (hγy : γ ≤ y) :
    extend S K b σ γ (encode S K b y) = y := by simp_all [extend, encode, release_reserve, canonicalDecoder_canonicalNormalizer hy]

/-- The proposed new source map preserves output caps on every pair of sources
agreeing below an interior source cut. Nothing requires the old map to attain `γ`. -/
theorem extend_cap_agreement (S : Finset Ordinal.{0}) {K b : ℕ}
    {σ : ExtOrd → ExtOrd} {γ a x y : ExtOrd}
    (hσ : Witness (gTop K) σ) (hγ : SelfVis K γ)
    (ha : a < ofOrd (Ordinal.omega0 * b)) (hactive : γ ≤ σ a)
    (hxy : min x a = min y a) :
    min (extend S K b σ γ x) γ = min (σ y) γ :=
  CapFirstScalar.map_cap_agreement_of_clipped_prefix hσ.mono
    (extend_witness S hσ hγ).mono
    (fun _ hz => extend_before S (hz.trans_lt ha)) hxy hactive

end VaughtConjecture.Knight.PaddedSourceDecoder
