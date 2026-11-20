/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CapFirstScalar
public import VaughtConjecture.Knight.SourceBlockPadding

/-! # Reserving a prefix of ordinal blocks

Shift the new tail as a whole; no compression or enumeration of its labels is necessary.
Releasing the reserved blocks reads every shifted value, including literal top.
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

/-- The inverse is literal at every padded source, including bottom and top. -/
theorem release_reserve b x : release b (reserve b x) = x := by
  induction b with
  | zero => rfl
  | succ b ih => simpa only [reserve, release, unpad_pad] using ih

/-- Precomposition is justified by exact replacement commutation, not transitivity. -/
theorem witness_release {g} {τ}
    (hτ : Witness g τ) b : Witness g (fun x => τ (release b x)) := by
  induction b with
  | zero => exact hτ
  | succ b ih => exact witness_precompose_unpad ih

private theorem unpad_lt_floor {b} {x}
    (hx : x < ofOrd (Ordinal.omega0 * (b + 1 : ℕ))) :
    unpad x < ofOrd (Ordinal.omega0 * b) := by
  classical
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · rw [unpad_bot]; exact bot_lt_ofOrd _
  · exact False.elim (not_lt_of_ge le_top hx)
  · by_cases hα : Ordinal.omega0 ≤ α
    · have he : pad (unpad (ofOrd α)) = ofOrd α := by
        rw [unpad_ofOrd, ite_eq_left hα, pad_ofOrd, Ordinal.add_sub_cancel_of_le hα]
      have hp : pad (ofOrd (Ordinal.omega0 * b)) =
          ofOrd (Ordinal.omega0 * (b + 1 : ℕ)) := by
        simpa only [Nat.cast_zero, add_zero] using pad_code b 0
      by_contra hn
      have hle := pad_mono (not_lt.mp hn)
      rw [he, hp] at hle
      exact not_lt_of_ge hle hx
    · rw [unpad_ofOrd, ite_eq_right hα]
      exact bot_lt_ofOrd _

/-- The decoder sees bottom on the entire reserved prefix, not just listed sources. -/
theorem release_eq_bot_of_lt {b : ℕ} {x}
    (hx : x < ofOrd (Ordinal.omega0 * b)) : release b x = ⊥ := by
  induction b generalizing x with
  | zero =>
    change x = ⊥
    rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
    · rfl
    · exact False.elim (not_lt_of_ge le_top hx)
    · have hα := ofOrd_lt_ofOrd.mp hx
      simp only [Nat.cast_zero, mul_zero, not_lt_zero] at hα
  | succ b ih => exact ih (unpad_lt_floor hx)

/-- Every nonbottom target is shifted beyond the reserved prefix. -/
theorem floor_le_reserve {b : ℕ} {y : ExtOrd} (hy : y ≠ ⊥) :
    ofOrd (Ordinal.omega0 * b) ≤ reserve b y := by
  by_contra hn
  exact hy ((release_reserve b y).symm.trans (release_eq_bot_of_lt (not_le.mp hn)))

noncomputable def extend (b : ℕ) (σ : ExtOrd → ExtOrd) (γ x : ExtOrd) :=
  max (min (σ x) γ) (release b x)

theorem extend_witness {K b : ℕ} {σ : ExtOrd → ExtOrd} {γ : ExtOrd}
    (hσ : Witness (gTop K) σ) (hγ : SelfVis K γ) : Witness (gTop K) (extend b σ γ) :=
  (FreeDiagonal.clip_witness hσ hγ).max (witness_release (witness_id K) b)

theorem extend_before {b : ℕ} {σ : ExtOrd → ExtOrd} {γ x : ExtOrd}
    (hx : x < ofOrd (Ordinal.omega0 * b)) : extend b σ γ x = min (σ x) γ := by
  rw [extend, release_eq_bot_of_lt hx, max_bot_right]

theorem extend_reserve {b : ℕ} {σ : ExtOrd → ExtOrd} {γ y : ExtOrd} (h : γ ≤ y) :
    extend b σ γ (reserve b y) = y := by
  rw [extend, release_reserve, max_eq_right ((min_le_right _ _).trans h)]

theorem extend_cap_agreement {K b : ℕ} {σ} {γ a x y}
    (hσ : Witness (gTop K) σ) (hγ : SelfVis K γ)
    (ha : a < ofOrd (Ordinal.omega0 * b)) (hactive : γ ≤ σ a)
    (hxy : min x a = min y a) : min (extend b σ γ x) γ = min (σ y) γ :=
  CapFirstScalar.map_cap_agreement_of_clipped_prefix hσ.mono (extend_witness hσ hγ).mono
    (fun _ hz => extend_before (hz.trans_lt ha)) hxy hactive

end VaughtConjecture.Knight.PaddedSourceDecoder
