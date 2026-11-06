/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CapFirstScalar
public import VaughtConjecture.Knight.SourceBlockPadding

/-! # A finite decoder tail above a preserved capped prefix

Reserve finitely many source blocks, decode a new finite inventory beyond them,
and take the maximum with the old shifter clipped at the output cap. The result
is an actual faithful witness, literal on the clipped prefix and exact on all
tracked new targets above the output cap, including literal top. The source
alphabet bound is explicit. This constructs a scalar map and codes, not a lawful
replacement member, available controller, or uniform source enlargement.
-/

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

section
variable (b : ℕ)

@[simp] theorem reserve_bot  : reserve b ⊥ = ⊥ := by
  induction b with
  | zero => rfl
  | succ b ih => simp only [reserve, ih, pad_bot]

/-- The inverse is literal at every padded source, including bottom and top. -/
theorem release_reserve x : release b (reserve b x) = x := by
  induction b with
  | zero => rfl
  | succ b ih => simpa only [reserve, release, unpad_pad] using ih

end

/-- Repeated source padding preserves the finite part exactly. -/
theorem reserve_code (b u j : ℕ) : reserve b (ofOrd (Ordinal.omega0 * u + j)) =
    ofOrd (Ordinal.omega0 * (u + b : ℕ) + j) := by
  induction b with
  | zero => simp only [reserve, Nat.add_zero]
  | succ b ih => rw [reserve, ih, pad_code, Nat.add_assoc]

/-- Precomposition is justified by exact replacement commutation, not transitivity. -/
theorem witness_release {g} {τ}
    (hτ : Witness g τ) b : Witness g (fun x => τ (release b x)) := by
  induction b with
  | zero => exact hτ
  | succ b ih => exact witness_precompose_unpad ih

section
variable {b : ℕ} {x : ExtOrd}

private theorem unpad_lt_floor (hx : x < ofOrd (Ordinal.omega0 * (b + 1 : ℕ))) :
    unpad x < ofOrd (Ordinal.omega0 * b) := by
  classical
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · rw [unpad_bot]; exact bot_lt_ofOrd _
  · exact False.elim (not_lt_of_ge le_top hx)
  · by_cases hα : Ordinal.omega0 ≤ α
    · have he : pad (unpad (ofOrd α)) = ofOrd α := by
        rw [unpad_ofOrd, ite_eq_left hα, pad_ofOrd, Ordinal.add_sub_cancel_of_le hα]
      have hp := by
        simpa only [Nat.cast_zero, add_zero] using pad_code b 0
      by_contra hn
      have hle := pad_mono (not_lt.mp hn)
      rw [he, hp] at hle
      exact not_lt_of_ge hle hx
    · rw [unpad_ofOrd, ite_eq_right hα]
      exact bot_lt_ofOrd _

/-- The decoder sees bottom on the entire reserved prefix, not just listed sources. -/
theorem release_eq_bot_of_lt (hx : x < ofOrd (Ordinal.omega0 * b)) : release b x = ⊥ := by
  induction b generalizing x with
  | zero =>
    rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
    · rfl
    · simp_all
    · simp_all
  | succ b ih => exact ih (unpad_lt_floor hx)

end

/-- An alphabet of block bound `t` moves to block bound `t + b`. -/
theorem reserve_mem_codedAlphabet {t K} {x}
    (hx : x ∈ ExtOrd.codedAlphabet t K) b :
    reserve b x ∈ ExtOrd.codedAlphabet (t + b) K := by
  rcases mem_codedAlphabet_iff.mp hx with rfl | ⟨u, j, hu, hj, rfl⟩
  · exact mem_codedAlphabet_iff.mpr (Or.inl (reserve_bot b))
  · exact mem_codedAlphabet_iff.mpr
      (Or.inr ⟨u + b, j, Nat.add_le_add_right hu b, hj, reserve_code b u j⟩)

/-- The actual finite tail code. Original literal top is represented by a proper code. -/
noncomputable def encode (S : Finset Ordinal.{0}) (K b : ℕ) (y : ExtOrd) : ExtOrd :=
  reserve b (canonicalNormalizer S K y)

section
variable (S : Finset Ordinal.{0})

/-- Exact alphabet accounting: no availability of this much room in a tower is assumed. -/
theorem encode_mem K b y :
    encode S K b y ∈ ExtOrd.codedAlphabet (S.card + b) K :=
  reserve_mem_codedAlphabet (canonicalNormalizer_mem_codedAlphabet le_rfl y) b

section
variable {K b : ℕ} {y : ExtOrd}

/-- Exact readback before taking any maximum with the old witness. -/
theorem decode_encode (hy : y = ⊥ ∨ y = ⊤ ∨ ∃ α ∈ S, y = ofOrd α) :
    canonicalDecoder S K (release b (encode S K b y)) = y := by
  rw [encode, release_reserve, canonicalDecoder_canonicalNormalizer hy]

/-- Every nonbottom tracked target really is placed beyond the reserved blocks. -/
theorem encode_ge_floor (hy : y = ⊥ ∨ y = ⊤ ∨ ∃ α ∈ S, y = ofOrd α) (hyb : y ≠ ⊥) :
    ofOrd (Ordinal.omega0 * b) ≤ encode S K b y := by
  by_contra hn
  have he := decode_encode (K := K) (b := b) S hy
  rw [release_eq_bot_of_lt (not_le.mp hn), canonicalDecoder_bot] at he
  exact hyb he.symm

end

end

/-- Join a clipped old witness to the new decoder. The join uses existing normalized
witness closure; its decoder is precomposed only with the exact source inverse. -/
noncomputable def extend (S : Finset Ordinal.{0}) (K b : ℕ)
    (σ : ExtOrd → ExtOrd) (γ : ExtOrd) (x : ExtOrd) : ExtOrd :=
  max (min (σ x) γ) (canonicalDecoder S K (release b x))

section
variable (S : Finset Ordinal.{0}) {K b : ℕ} {σ : ExtOrd → ExtOrd}

/-- The extension is globally faithful, including the higher-threshold bottom clauses. -/
theorem extend_witness {γ : ExtOrd}
    (hσ : Witness (gTop K) σ) (hγ : SelfVis K γ) :
    Witness (gTop K) (extend S K b σ γ) :=
  (FreeDiagonal.clip_witness hσ hγ).max
    (witness_release (isStepShifter_canonicalDecoder (S := S) (K := K)).normalizedWitness b)

/-- Every value before the tail remains exactly the old value capped at `γ`. -/
theorem extend_before {γ x : ExtOrd} (hx : x < ofOrd (Ordinal.omega0 * b)) :
    extend S K b σ γ x = min (σ x) γ := by
  rw [extend, release_eq_bot_of_lt hx, canonicalDecoder_bot, max_bot_right]

/-- New high targets are read literally, with no restriction on their finite part.
Bottom is allowed when the cap is bottom; top is handled by its proper code. -/
theorem extend_encode {γ y : ExtOrd}
    (hy : y = ⊥ ∨ y = ⊤ ∨ ∃ α ∈ S, y = ofOrd α) (hγy : γ ≤ y) :
    extend S K b σ γ (encode S K b y) = y := by
  rw [extend, encode, release_reserve, canonicalDecoder_canonicalNormalizer hy]
  exact max_eq_right ((min_le_right _ _).trans hγy)

/-- The proposed new source map preserves output caps on every pair of sources
agreeing below an interior source cut. Nothing requires the old map to attain `γ`. -/
theorem extend_cap_agreement {γ a x y : ExtOrd}
    (hσ : Witness (gTop K) σ) (hγ : SelfVis K γ)
    (ha : a < ofOrd (Ordinal.omega0 * b)) (hactive : γ ≤ σ a)
    (hxy : min x a = min y a) :
    min (extend S K b σ γ x) γ = min (σ y) γ :=
  CapFirstScalar.map_cap_agreement_of_clipped_prefix hσ.mono
    (extend_witness S hσ hγ).mono
    (fun _ hz => extend_before S (hz.trans_lt ha)) hxy hactive

end

end VaughtConjecture.Knight.PaddedSourceDecoder
