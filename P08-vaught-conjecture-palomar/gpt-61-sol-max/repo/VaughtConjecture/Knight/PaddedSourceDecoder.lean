import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CapFirstScalar
import VaughtConjecture.Knight.SourceBlockPadding

/-! # A finite decoder tail above a preserved capped prefix

Reserve finitely many source blocks, decode a new finite inventory beyond them,
and take the maximum with the old shifter clipped at the output cap. The result
is an actual faithful witness, literal on the clipped prefix and exact on all
tracked new targets above the output cap, including literal top. The source
alphabet bound is explicit. This constructs a scalar map and codes, not a lawful
replacement member, available controller, or uniform source enlargement.
-/

namespace VaughtConjecture.Knight.PaddedSourceDecoder

open Transform  ExtOrd  SourceBlockPadding

/-- Move nonbottom sources by `b` whole blocks. -/
noncomputable def reserve : ℕ → LabelMap
  | 0, x => x
  | b + 1, x => pad (reserve b x)

/-- Erase the reserved blocks; every erased block is killed in its entirety. -/
noncomputable def release : ℕ → LabelMap
  | 0, x => x
  | b + 1, x => release b (unpad x)

@[simp] theorem reserve_bot b : reserve b ⊥ = ⊥ := by
  induction b <;> simp_all [reserve, pad]

/-- The inverse is literal at every padded source, including bottom and top. -/
theorem release_reserve b x : release b (reserve b x) = x := by (
  induction b <;> simp_all [reserve, release, unpad_pad])

/-- Repeated source padding preserves the finite part exactly. -/
theorem reserve_code (b u j : ℕ) : reserve b (ofOrd (Ordinal.omega0 * u + j)) =
    ofOrd (Ordinal.omega0 * (u + b : ℕ) + j) := by
  induction b with
  | zero => simp  [reserve, ]
  | succ b ih => rw [reserve, ih, pad_code, Nat.add_assoc]

/-- Precomposition is justified by exact replacement commutation, not transitivity. -/
theorem witness_release {g} {τ}
    (hτ : Witness g τ) b : Witness g (fun x => τ (release b x)) := by
  induction b with
  | zero => exact hτ
  | succ b ih => exact witness_precompose_unpad ih

private theorem unpad_lt_floor {b} {x}
    (hx : x < ofOrd (Ordinal.omega0 * (b + 1 : ℕ))) :
    unpad x < ofOrd (Ordinal.omega0 * b) := by
  
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · simp_all
  · simp_all
  · by_cases hα : Ordinal.omega0 ≤ α
    · have he : pad (unpad (ofOrd α)) = ofOrd α := by
        simp_all [unpad_ofOrd, Ordinal.add_sub_cancel_of_le]
      have hp  := by
        simpa only [Nat.cast_zero, add_zero] using pad_code b 0
      by_contra hn
      have hle := pad_mono (not_lt.mp hn)
      rw [he, hp] at hle
      exact not_lt_of_ge hle hx
    · simp_all [unpad_ofOrd, ite_eq_right]

/-- The decoder sees bottom on the entire reserved prefix, not just listed sources. -/
theorem release_eq_bot_of_lt {b : ℕ} {x : ExtOrd}
    (hx : x < ofOrd (Ordinal.omega0 * b)) : release b x = ⊥ := by
  induction b generalizing x with
  | zero =>
    
    rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
    · rfl
    · simp_all
    · simp_all
  | succ b ih => exact ih (unpad_lt_floor hx)

/-- An alphabet of block bound `t` moves to block bound `t + b`. -/
theorem reserve_mem_codedAlphabet {t K} {x}
    (hx : x ∈ ExtOrd.codedAlphabet t K) b :
    reserve b x ∈ ExtOrd.codedAlphabet (t + b) K := by
  rcases mem_codedAlphabet_iff.mp hx with rfl | ⟨u, j, hu, hj, rfl⟩
  · simp_all [VaughtConjecture.Knight.ExtOrd.codedAlphabet]
  · exact mem_codedAlphabet_iff.mpr
      (Or.inr ⟨u + b, j, Nat.add_le_add_right hu b, hj, reserve_code b u j⟩)

/-- The actual finite tail code. Original literal top is represented by a proper code. -/
noncomputable def encode S K b y :=
  reserve b (canonicalNormalizer S K y)

/-- Exact alphabet accounting: no availability of this much room in a tower is assumed. -/
theorem encode_mem S K b y :
    encode S K b y ∈ ExtOrd.codedAlphabet (S.card + b) K :=
  reserve_mem_codedAlphabet (canonicalNormalizer_mem_codedAlphabet le_rfl y) b

/-- Exact readback before taking any maximum with the old witness. -/
theorem decode_encode S {K b} {y}
    (hy : y = ⊥ ∨ y = ⊤ ∨ ∃ α ∈ S, y = ofOrd α) :
    canonicalDecoder S K (release b (encode S K b y)) = y := by
  rw [encode, release_reserve, canonicalDecoder_canonicalNormalizer hy]

/-- Every nonbottom tracked target really is placed beyond the reserved blocks. -/
theorem encode_ge_floor (S : Finset Ordinal₀) {K b : ℕ} {y : ExtOrd}
    (hy : y = ⊥ ∨ y = ⊤ ∨ ∃ α ∈ S, y = ofOrd α) (hyb : y ≠ ⊥) :
    ofOrd (Ordinal.omega0 * b) ≤ encode S K b y := by
  by_contra hn
  have he := decode_encode (K := K) (b := b) S hy
  rw [release_eq_bot_of_lt (not_le.mp hn), ] at he
  exact hyb he.symm

/-- Join a clipped old witness to the new decoder. The join uses existing normalized
witness closure; its decoder is precomposed only with the exact source inverse. -/
noncomputable def extend (S : Finset Ordinal₀) (K b : ℕ)
    (σ : LabelMap) (γ x : ExtOrd) :=
  max (min (σ x) γ) (canonicalDecoder S K (release b x))

/-- The extension is globally faithful, including the higher-threshold bottom clauses. -/
theorem extend_witness S {K b}
    {σ} {γ}
    (hσ : Witness (gTop K) σ) (hγ : SelfVis K γ) :
    Witness (gTop K) (extend S K b σ γ) :=
  (FreeDiagonal.clip_witness hσ hγ).max
    (witness_release (isStepShifter_canonicalDecoder  ).normalizedWitness b)

/-- Every value before the tail remains exactly the old value capped at `γ`. -/
theorem extend_before (S : Finset Ordinal₀) {K b : ℕ}
    {σ : LabelMap} {γ x : ExtOrd} (hx : x < ofOrd (Ordinal.omega0 * b)) :
    extend S K b σ γ x = min (σ x) γ := by
  rw [extend, release_eq_bot_of_lt hx, canonicalDecoder_bot, max_bot_right]

/-- New high targets are read literally, with no restriction on their finite part.
Bottom is allowed when the cap is bottom; top is handled by its proper code. -/
theorem extend_encode S {K b}
    {σ} {γ y}
    (hy : y = ⊥ ∨ y = ⊤ ∨ ∃ α ∈ S, y = ofOrd α) (hγy : γ ≤ y) :
    extend S K b σ γ (encode S K b y) = y := by
  rw [extend, encode, release_reserve, canonicalDecoder_canonicalNormalizer hy]
  exact max_eq_right ((min_le_right _ _).trans hγy)

/-- The proposed new source map preserves output caps on every pair of sources
agreeing below an interior source cut. Nothing requires the old map to attain `γ`. -/
def extend_cap_agreement (S : Finset Ordinal₀) {K b : ℕ}
    {σ : LabelMap} {γ a x y : ExtOrd}
    (hσ : Witness (gTop K) σ) (hγ : SelfVis K γ)
    (ha : a < ofOrd (Ordinal.omega0 * b)) (hactive : γ ≤ σ a)
    (hxy : min x a = min y a) :=
  CapFirstScalar.map_cap_agreement_of_clipped_prefix hσ.mono
    (extend_witness S hσ hγ).mono
    (fun _ hz => extend_before S (hz.trans_lt ha)) hxy hactive

