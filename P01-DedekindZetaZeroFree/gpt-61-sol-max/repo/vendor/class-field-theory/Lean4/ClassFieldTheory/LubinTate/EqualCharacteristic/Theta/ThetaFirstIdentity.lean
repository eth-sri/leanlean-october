module

public import Mathlib

public import Mathlib.SetTheory.Cardinal.Finite
public import ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaUniqueness

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# The Lubin–Tate endomorphism commutation law: the first theta identity in equal characteristic

For the normalization `pi = T` and `bar_pi = u⁻¹ T`, this file constructs
the Lubin--Tate endomorphism `[u]` over the base integer ring `k[[T]]` and
proves the first identity of Corollary the Lubin–Tate endomorphism commutation law,

`theta^phi = theta o [u]`.

The endomorphism `[u]` is constructed independently from `theta`: its
linear coefficient is `u`, and its higher additive coefficients are the
unique contracting solutions forced by commutation with
`Y^q + bar_pi Y`.
-/

noncomputable section

open scoped PowerSeries


universe u v

namespace LubinTate
namespace EqualCharacteristic

variable {k : Type u} [Field k] [Finite k]
























/-- The numerator on the right of the coefficient equation for `[u]`. -/
noncomputable def equalCharacteristicSourceBracketNumerator
    (a : k⟦X⟧)  :=
  a - a ^ Nat.card k

/-- The source bracket numerator has zero constant coefficient. -/
theorem equalCharacteristicSourceBracketNumerator_constantCoeff
    (a : k⟦X⟧) :
    PowerSeries.coeff 0 (equalCharacteristicSourceBracketNumerator a) = 0 := by
  let  := Fintype.ofFinite k
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
    equalCharacteristicSourceBracketNumerator,
    map_sub, map_pow, Nat.card_eq_fintype_card,
    FiniteField.pow_card, sub_self]













































































































































































































/-- Frobenius fixes every coefficient coming from the base integer ring. -/
theorem equalCharacteristicPowerSeriesFrobenius_map_algebraMap
    (a : k⟦X⟧) :
    equalCharacteristicPowerSeriesFrobenius k
        (PowerSeries.map (algebraMap k (AlgebraicClosure k)) a) =
      PowerSeries.map (algebraMap k (AlgebraicClosure k)) a := by
  let  := Fintype.ofFinite k
  apply PowerSeries.ext
  intro n
  rw [equalCharacteristicPowerSeriesFrobenius_coeff,
    PowerSeries.coeff_map]
  calc
    (algebraMap k (AlgebraicClosure k) (PowerSeries.coeff n a)) ^
          Nat.card k =
        algebraMap k (AlgebraicClosure k)
          ((PowerSeries.coeff n a) ^ Nat.card k) := by
            rw [map_pow]
    _ = _ := by
      rw [Nat.card_eq_fintype_card,
        FiniteField.pow_card]





























































section QAdditiveComposition

variable {R : Type v} [CommRing R] [Nontrivial R] [Algebra k R]

/-- A `q^i`-th power shifts additive exponents by `i`; the coefficient at
`q^n` is zero for `n<i` and otherwise is the `q^i`-th power of the
coefficient at `q^(n-i)`. -/
theorem equalCharacteristicQAdditiveSeries_pow_card_pow
    (a : ℕ → R) (i : ℕ) :
    equalCharacteristicQAdditiveSeries k a ^ (Nat.card k ^ i) =
      equalCharacteristicQAdditiveSeries k (fun n ↦
        if i ≤ n then a (n - i) ^ (Nat.card k ^ i) else 0) := by
  induction i with
  | zero =>
      simp
  | succ i ih =>
      rw [pow_succ, pow_mul, ih,
        equalCharacteristicQAdditiveSeries_pow_card]
      congr 1
      funext n
      cases n with
      | zero =>
          simp [equalCharacteristicQAdditiveShift]
      | succ n =>
          by_cases hin : i ≤ n
          · have hisucc : i + 1 ≤ n + 1 := Nat.succ_le_succ hin
            simp [equalCharacteristicQAdditiveShift, hin, hisucc,
              pow_mul]
          · have hisucc : ¬ i + 1 ≤ n + 1 := by omega
            simp [equalCharacteristicQAdditiveShift, hin, hisucc,
              Nat.card_pos.ne']

/-- Coefficient form of the preceding shift formula. -/
theorem equalCharacteristicQAdditiveSeries_pow_card_pow_coeff
    (a : ℕ → R) (i n : ℕ) :
    PowerSeries.coeff (Nat.card k ^ n)
        (equalCharacteristicQAdditiveSeries k a ^ (Nat.card k ^ i)) =
      if i ≤ n then a (n - i) ^ (Nat.card k ^ i) else 0 := by
  rw [equalCharacteristicQAdditiveSeries_pow_card_pow,
    equalCharacteristicQAdditiveSeries_coeff_pow]

/-- The finite convolution of coefficients occurring in the composition
of two `q`-additive series. -/
def equalCharacteristicQAdditiveCompositionCoefficient
    (b a : ℕ → R) (n : ℕ)  :=
  ∑ i ∈ Finset.range (n + 1),
    b i * a (n - i) ^ (Nat.card k ^ i)

/-- Composition of two `q`-additive series is again `q`-additive, with the
usual finite Frobenius convolution of coefficients. -/
theorem equalCharacteristicQAdditiveSeries_subst_qAdditiveSeries
    (b a : ℕ → R) :
    PowerSeries.subst (equalCharacteristicQAdditiveSeries k a)
        (equalCharacteristicQAdditiveSeries k b) =
      equalCharacteristicQAdditiveSeries k
        (equalCharacteristicQAdditiveCompositionCoefficient (k := k) b a) := by
  let A := equalCharacteristicQAdditiveSeries k a
  let B := equalCharacteristicQAdditiveSeries k b
  have hA : PowerSeries.HasSubst A :=
    PowerSeries.HasSubst.of_constantCoeff_zero'
      (equalCharacteristicQAdditiveSeries_constantCoeff k a)
  apply PowerSeries.ext
  intro n
  by_cases hn : IsEqualCharacteristicAdditiveExponent k n
  · obtain ⟨r, rfl⟩ := hn
    rw [equalCharacteristicQAdditiveSeries_coeff_pow,
      PowerSeries.coeff_subst' hA]
    let F  := fun d ↦
      PowerSeries.coeff d B •
        PowerSeries.coeff (Nat.card k ^ r) (A ^ d)
    change ∑ᶠ d : ℕ, F d = _
    have hsupport : Function.support F ⊆
        (((Finset.range (r + 1)).image (fun i ↦ Nat.card k ^ i)) : Set ℕ) := by
      intro d hd
      change F d ≠ 0 at hd
      by_cases hde : IsEqualCharacteristicAdditiveExponent k d
      · obtain ⟨i, rfl⟩ := hde
        by_cases hir : i ≤ r
        · exact Finset.mem_coe.mpr (Finset.mem_image.mpr
            ⟨i, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hir), rfl⟩)
        · have hzero :=
            equalCharacteristicQAdditiveSeries_pow_card_pow_coeff
              (k := k) a i r
          rw [ite_eq_right hir] at hzero
          simp [F, A, hzero] at hd
      · have hzero :=
          equalCharacteristicQAdditiveSeries_coeff_eq_zero k b d hde
        simp [F, B, hzero] at hd
    rw [finsum_eq_sum_of_support_subset F hsupport,
      Finset.sum_image]
    · simp only [F, A, B,
        equalCharacteristicQAdditiveSeries_coeff_pow,
        equalCharacteristicQAdditiveSeries_pow_card_pow_coeff,
        equalCharacteristicQAdditiveCompositionCoefficient]
      apply Finset.sum_congr rfl
      intro i hi
      have hir  := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      simp [hir, smul_eq_mul]
    · intro i hi j hj hij
      exact (natCard_pow_injective k hij)
  · rw [equalCharacteristicQAdditiveSeries_coeff_eq_zero k _ n hn,
      PowerSeries.coeff_subst' hA,
      finsum_eq_zero_of_forall_eq_zero]
    intro d
    by_cases hde : IsEqualCharacteristicAdditiveExponent k d
    · obtain ⟨i, rfl⟩ := hde
      rw [equalCharacteristicQAdditiveSeries_pow_card_pow]
      have hzero := equalCharacteristicQAdditiveSeries_coeff_eq_zero
        k (fun m ↦ if i ≤ m then a (m - i) ^ (Nat.card k ^ i) else 0)
        n hn
      simp [hzero]
    · rw [equalCharacteristicQAdditiveSeries_coeff_eq_zero k b d hde]
      simp

end QAdditiveComposition



























































































































































































































































































end EqualCharacteristic
end LubinTate

end
