module

public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.RamificationInvariants
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Canonical exponential valuation attached to an absolute value

The localization arguments of the ramification-localization construction are naturally multiplicative, whereas the
unramified predicates of the unramified-extension construction use additive exponential valuations.  This file
supplies the canonical conversion `v(x) = -log |x|`.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

variable {K : Type*} [Field K]

/-- The additive exponential valuation `- log |x|`, with value `∞` at zero. -/
def absoluteValueExponentialValuation
    (abv : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue abv) :
    LubinTate.Valuations.ExponentialValuation K := by
  classical
  refine
    { toFun := fun x ↦
        if x = 0 then ⊤ else ((-Real.log (abv x) : ℝ) : WithTop ℝ)
      eq_top_iff := ?_
      map_mul := ?_
      add_le_min := ?_ }
  · intro x
    simp
  · intro x y
    by_cases hx : x = 0
    · subst x
      simp
    by_cases hy : y = 0
    · subst y
      simp
    have hxy : x * y ≠ 0 := mul_ne_zero hx hy
    simp only [hx, hy, hxy, ite_false, map_mul]
    rw [Real.log_mul (abv.ne_zero hx) (abv.ne_zero hy)]
    simp only [neg_add, WithTop.coe_add]
  · intro x y
    by_cases hx : x = 0
    · subst x
      simp
    by_cases hy : y = 0
    · subst y
      simp
    by_cases hxy : x + y = 0
    · simp [hxy]
    simp only [hx, hy, hxy, ite_false]
    apply WithTop.coe_le_coe.mpr
    by_cases hle : abv x ≤ abv y
    · have hlogxy : Real.log (abv x) ≤ Real.log (abv y) :=
        Real.strictMonoOn_log.monotoneOn (abv.pos hx) (abv.pos hy) hle
      rw [min_eq_right (neg_le_neg hlogxy)]
      apply neg_le_neg
      exact Real.strictMonoOn_log.monotoneOn (abv.pos hxy) (abv.pos hy)
        (((LubinTate.Valuations.strong_triangle_of_nonarchimedean abv hnonarch)
          x y).trans (max_eq_right hle).le)
    · have hyx : abv y ≤ abv x := le_of_not_ge hle
      have hlogyx : Real.log (abv y) ≤ Real.log (abv x) :=
        Real.strictMonoOn_log.monotoneOn (abv.pos hy) (abv.pos hx) hyx
      rw [min_eq_left (neg_le_neg hlogyx)]
      apply neg_le_neg
      exact Real.strictMonoOn_log.monotoneOn (abv.pos hxy) (abv.pos hx)
        (((LubinTate.Valuations.strong_triangle_of_nonarchimedean abv hnonarch)
          x y).trans (max_eq_left hyx).le)

@[simp] theorem absoluteValueExponentialValuation_apply_ne_zero
    (abv : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue abv)
    {x : K} (hx : x ≠ 0) :
    absoluteValueExponentialValuation abv hnonarch x =
      ((-Real.log (abv x) : ℝ) : WithTop ℝ) := by
  simp [absoluteValueExponentialValuation, hx]

/-- The original absolute value is associated to its canonical exponential
valuation, with base `e`. -/
theorem absoluteValueExponentialValuation_associated
    (abv : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue abv) :
    LubinTate.Valuations.AssociatedAbsoluteValue
      (absoluteValueExponentialValuation abv hnonarch)
      (Real.exp 1) abv := by
  refine ⟨Real.one_lt_exp_iff.mpr zero_lt_one, ?_⟩
  intro x hx
  refine ⟨-Real.log (abv x), ?_, ?_⟩
  · simp [absoluteValueExponentialValuation, hx]
  · simp only [neg_neg]
    exact (Real.exp_log (abv.pos hx)).symm.trans
      (Real.exp_one_rpow (Real.log (abv x))).symm

/-- Exact extension of nonarchimedean absolute values gives exact extension
of their canonical exponential valuations. -/
theorem absoluteValueExponentialValuation_extends
    {L : Type*} [Field L] [Algebra K L]
    (av : AbsoluteValue K ℝ) (aw : AbsoluteValue L ℝ)
    (hav : LubinTate.Valuations.NonarchimedeanAbsoluteValue av)
    (haw : LubinTate.Valuations.NonarchimedeanAbsoluteValue aw)
    (hExt : ∀ x : K, aw (algebraMap K L x) = av x) :
    ∀ x : K,
      absoluteValueExponentialValuation aw haw (algebraMap K L x) =
        absoluteValueExponentialValuation av hav x := by
  intro x
  by_cases hx : x = 0
  · subst x
    simp [absoluteValueExponentialValuation]
  simp_all
