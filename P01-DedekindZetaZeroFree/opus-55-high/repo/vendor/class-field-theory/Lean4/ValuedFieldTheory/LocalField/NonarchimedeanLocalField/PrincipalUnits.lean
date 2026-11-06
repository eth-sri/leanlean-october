module

public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-!
# Principal units

Defines the filtration `U^n = 1 + 𝓂^n`, proves its basic order properties, and
constructs the quotient of valuation-ring units by the first filtration step.
-/


namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- The actual principal-unit filtration `U^n = {u ∈ 𝒪[K]ˣ | u - 1 ∈ 𝓂[K]^n}`. -/
def principalUnits (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    Subgroup 𝒪[K]ˣ where
  carrier := {u | ((u : 𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal 𝒪[K])}
  one_mem' := by
    simp
  mul_mem' := by
    intro a b ha hb
    change ((a : 𝒪[K]) * (b : 𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal 𝒪[K])
    rw [show ((a : 𝒪[K]) * (b : 𝒪[K]) - 1) =
        ((a : 𝒪[K]) - 1) * (b : 𝒪[K]) + ((b : 𝒪[K]) - 1) by
      ring]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) hb
  inv_mem' := by
    intro a ha
    change (((a⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal 𝒪[K])
    rw [show (((a⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) - 1) =
        -(((a⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * ((a : 𝒪[K]) - 1)) by
      calc
        (((a⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) - 1)
            = ((a⁻¹ : 𝒪[K]ˣ) : 𝒪[K])
              - (((a⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * (a : 𝒪[K])) := by
                simp
        _ = -(((a⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * ((a : 𝒪[K]) - 1)) := by
          ring]
    simp_all

/-- A valuation-ring unit lies in the `n`-th principal-unit group exactly when it is congruent to
one modulo the `n`-th maximal-ideal power. -/
theorem mem_principalUnits_iff (K : Type u) [Field K] [ValuativeRel K]
    (u : 𝒪[K]ˣ) (n : Nat) :
    u ∈ principalUnits K n ↔ ((u : 𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) :=
  Iff.rfl

/-- An automorphism of the valuation integer ring preserves the principal-unit
filtration whenever it preserves the corresponding maximal-ideal power. -/
theorem principalUnits_integerRingEquiv_mem (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (σ𝒪 : 𝒪[K] ≃+* 𝒪[K])
    (hpow : ∀ x : 𝒪[K],
      x ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) → σ𝒪 x ∈ (𝓂[K] ^ n : Ideal 𝒪[K]))
    (u : 𝒪[K]ˣ) (hu : u ∈ principalUnits K n) :
    Units.mapEquiv σ𝒪.toMulEquiv u ∈ principalUnits K n := by
  rw [mem_principalUnits_iff] at hu ⊢
  have hmem : σ𝒪 ((u : 𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) :=
    hpow ((u : 𝒪[K]) - 1) hu
  simpa using hmem

/-- The zeroth principal-unit group is the full unit group of the valuation ring. -/
@[simp] theorem principalUnits_zero (K : Type u) [Field K] [ValuativeRel K] :
    principalUnits K 0 = ⊤ := by
  ext u
  simp [principalUnits]

/-- Principal-unit groups decrease as the filtration index increases. -/
theorem principalUnits_antitone (K : Type u) [Field K] [ValuativeRel K]
    {m n : Nat} (h : m ≤ n) :
    principalUnits K n ≤ principalUnits K m := by
  intro u hu
  exact Ideal.pow_le_pow_right h hu

/-- Algebra identity used to prove multiplicative closure of principal units. -/
lemma unit_mul_sub_one_eq (K : Type u) [Field K] [ValuativeRel K] (a b : 𝒪[K]ˣ) :
    ((a * b : 𝒪[K]ˣ) : 𝒪[K]) - 1 =
      ((a : 𝒪[K]) - 1) * ((b : 𝒪[K]) - 1) +
        ((a : 𝒪[K]) - 1) + ((b : 𝒪[K]) - 1) := by
  simp only [Units.val_mul]
  ring
