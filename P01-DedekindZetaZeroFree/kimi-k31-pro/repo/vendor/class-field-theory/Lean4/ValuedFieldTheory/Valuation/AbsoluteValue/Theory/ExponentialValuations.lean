module

public import ValuedFieldTheory.Valuation.AbsoluteValue.Theory.AbsoluteValues
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/








set_option autoImplicit false

/-! Provides the public declarations in the `ValuationTheory.AbsoluteValue.Theory.ExponentialValuations` Lean module. -/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace LubinTate
namespace Valuations

/-- The additive exponential valuation with value `∞` at zero. -/
structure ExponentialValuation (K : Type*) [Field K] where
  /-- The value map into `ℝ ∪ {∞}`. -/
  toFun : K → WithTop ℝ
  /-- Exactly zero has value `∞`. -/
  eq_top_iff : ∀ x, toFun x = ⊤ ↔ x = 0
  /-- Multiplication becomes addition of values. -/
  map_mul : ∀ x y, toFun (x * y) = toFun x + toFun y
  /-- The nonarchimedean inequality in additive form. -/
  add_le_min : ∀ x y, min (toFun x) (toFun y) ≤ toFun (x + y)

/-- Coerce an exponential valuation to its function. -/
instance exponentialValuationCoeFun {K : Type*} [Field K] :
    CoeFun (ExponentialValuation K) (fun _ => K → WithTop ℝ) where
  coe v := v.toFun





/-- A multiplicative absolute value associated to an exponential valuation by `|x| = q^{-v(x)}`. -/
def AssociatedAbsoluteValue {K : Type*} [Field K]
    (v : ExponentialValuation K) (q : ℝ) (abv : AbsoluteValue K ℝ) : Prop :=
  1 < q ∧ ∀ x : K, x ≠ 0 → ∃ r : ℝ,
    v x = (r : WithTop ℝ) ∧ abv x = Real.rpow q (-r)

/-- The valuation ring `{x | v(x) ≥ 0}` attached to an exponential valuation. -/
def exponentialValuationRing {K : Type*} [Field K]
    (v : ExponentialValuation K) : Set K :=
  {x | (0 : WithTop ℝ) ≤ v x}

/-- Nonzero elements have finite value for a exponential valuation. -/
theorem exponentialValuation_ne_top_of_ne_zero {K : Type*} [Field K]
    (v : ExponentialValuation K) {x : K} (hx : x ≠ 0) :
    v x ≠ ⊤ := by
  intro htop
  exact hx ((v.eq_top_iff x).mp htop)

/-- A nonzero element has a real-valued exponential valuation. -/
theorem exponentialValuation_exists_real_of_ne_zero {K : Type*} [Field K]
    (v : ExponentialValuation K) {x : K} (hx : x ≠ 0) :
    ∃ r : ℝ, v x = (r : WithTop ℝ) := by
  rcases WithTop.ne_top_iff_exists.mp
      (exponentialValuation_ne_top_of_ne_zero v hx) with ⟨r, hr⟩
  exact ⟨r, hr.symm⟩

/-- The value of `1` is `0` for a exponential valuation. -/
@[simp]
theorem exponentialValuation_one {K : Type*} [Field K]
    (v : ExponentialValuation K) :
    v (1 : K) = 0 := by
  obtain ⟨r, hr⟩ :=
    exponentialValuation_exists_real_of_ne_zero v (one_ne_zero : (1 : K) ≠ 0)
  have hmul := v.map_mul (1 : K) (1 : K)
  rw [one_mul, hr] at hmul
  have hmul_real : r = r + r :=
    WithTop.coe_eq_coe.mp (by simpa [WithTop.coe_add] using hmul)
  have hr0 : r = 0 := by linarith
  simp [hr, hr0]

/-- The value of `-1` is `0` for a exponential valuation. -/
@[simp]
theorem exponentialValuation_neg_one {K : Type*} [Field K]
    (v : ExponentialValuation K) :
    v (-1 : K) = 0 := by
  obtain ⟨r, hr⟩ :=
    exponentialValuation_exists_real_of_ne_zero v
      (neg_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0))
  have hmul := v.map_mul (-1 : K) (-1 : K)
  have hsq : (-1 : K) * (-1 : K) = 1 := by ring
  rw [hsq, exponentialValuation_one v, hr] at hmul
  have hmul_real : (0 : ℝ) = r + r :=
    WithTop.coe_eq_coe.mp (by simpa [WithTop.coe_add] using hmul)
  have hr0 : r = 0 := by linarith
  simp [hr, hr0]

/-- Negation does not change a exponential valuation. -/
@[simp]
theorem exponentialValuation_neg {K : Type*} [Field K]
    (v : ExponentialValuation K) (x : K) :
    v (-x) = v x := by
  rw [← neg_one_mul, v.map_mul, exponentialValuation_neg_one, zero_add]

/-- An element of value zero is nonzero. -/
theorem exponentialValuation_ne_zero_of_value_eq_zero {K : Type*} [Field K]
    (v : ExponentialValuation K) {x : K} (hx : v x = 0) :
    x ≠ 0 := by
  intro hzero
  have htop : v x = ⊤ := (v.eq_top_iff x).mpr hzero
  rw [hx] at htop
  simp at htop

/-- The inverse of a value-zero element again has value zero. -/
theorem exponentialValuation_inv_of_value_eq_zero {K : Type*} [Field K]
    (v : ExponentialValuation K) {x : K} (hx : v x = 0) :
    v x⁻¹ = 0 := by
  have hx0 : x ≠ 0 := exponentialValuation_ne_zero_of_value_eq_zero v hx
  have hmul := v.map_mul x x⁻¹
  rw [mul_inv_cancel₀ hx0, exponentialValuation_one v, hx] at hmul
  simpa using hmul.symm

/-- Finite inverse-value formula for a exponential valuation. -/
theorem exponentialValuation_inv_value {K : Type*} [Field K]
    (v : ExponentialValuation K) {x : K} (hx : x ≠ 0) {r : ℝ}
    (hval : v x = (r : WithTop ℝ)) :
    v x⁻¹ = ((-r : ℝ) : WithTop ℝ) := by
  obtain ⟨s, hs⟩ :=
    exponentialValuation_exists_real_of_ne_zero v (inv_ne_zero hx)
  have hmul := v.map_mul x x⁻¹
  rw [mul_inv_cancel₀ hx, exponentialValuation_one v, hval, hs] at hmul
  have hmul_real : (0 : ℝ) = r + s :=
    WithTop.coe_eq_coe.mp (by simpa [WithTop.coe_add] using hmul)
  have hs_eq : s = -r := by
    linarith
  simp [hs, hs_eq]

/-- The set `{x | 0 ≤ v x}` is a subring. -/
def exponentialValuationSubring {K : Type*} [Field K]
    (v : ExponentialValuation K) : Subring K where
  carrier := exponentialValuationRing v
  zero_mem' := by
    change (0 : WithTop ℝ) ≤ v (0 : K)
    rw [(v.eq_top_iff 0).mpr rfl]
    simp
  one_mem' := by
    change (0 : WithTop ℝ) ≤ v (1 : K)
    simp
  add_mem' := by
    intro x y hx hy
    change (0 : WithTop ℝ) ≤ v (x + y)
    exact (le_min hx hy).trans (v.add_le_min x y)
  neg_mem' := by
    intro x hx
    change (0 : WithTop ℝ) ≤ v x at hx
    change (0 : WithTop ℝ) ≤ v (-x)
    simpa using hx
  mul_mem' := by
    intro x y hx hy
    change (0 : WithTop ℝ) ≤ v (x * y)
    rw [v.map_mul]
    exact add_nonneg hx hy

/-- Membership in the exponential-valuation subring is exactly the defining
condition `0 ≤ v x`. -/
theorem mem_exponentialValuationSubring_iff {K : Type*} [Field K]
    (v : ExponentialValuation K) (x : K) :
    x ∈ exponentialValuationSubring v ↔ (0 : WithTop ℝ) ≤ v x :=
  Iff.rfl

/-- Every element of the field or its inverse lies in the exponential-valuation ring. -/
theorem exponentialValuationRing_mem_or_inv_mem {K : Type*} [Field K]
    (v : ExponentialValuation K) (x : K) :
    x ∈ exponentialValuationRing v ∨ x⁻¹ ∈ exponentialValuationRing v := by
  by_cases hx : x = 0
  · left
    subst x
    change (0 : WithTop ℝ) ≤ v (0 : K)
    rw [(v.eq_top_iff 0).mpr rfl]
    simp
  · obtain ⟨r, hr⟩ := exponentialValuation_exists_real_of_ne_zero v hx
    by_cases hr_nonneg : 0 ≤ r
    · left
      change (0 : WithTop ℝ) ≤ v x
      rw [hr]
      exact WithTop.coe_le_coe.mpr hr_nonneg
    · right
      have hneg_nonneg : 0 ≤ -r := by
        linarith
      change (0 : WithTop ℝ) ≤ v x⁻¹
      rw [exponentialValuation_inv_value v hx hr]
      exact WithTop.coe_le_coe.mpr hneg_nonneg

/-- The absolute values subring satisfies mathlib's valuation-subring
membership alternative. -/
theorem exponentialValuationSubring_mem_or_inv_mem {K : Type*} [Field K]
    (v : ExponentialValuation K) (x : K) :
    x ∈ exponentialValuationSubring v ∨
      x⁻¹ ∈ exponentialValuationSubring v := by
  simpa [exponentialValuationSubring] using
    exponentialValuationRing_mem_or_inv_mem v x

/-- The exponential-valuation ring, bundled as mathlib's `ValuationSubring`. -/
def exponentialValuationSubringAsValuationSubring
    {K : Type*} [Field K] (v : ExponentialValuation K) :
    ValuationSubring K :=
  ValuationSubring.ofSubring (exponentialValuationSubring v)
    (exponentialValuationSubring_mem_or_inv_mem v)

/-- Membership in the bundled mathlib valuation subring is the defining condition
`0 ≤ v x`. -/
theorem mem_exponentialValuationSubringAsValuationSubring_iff
    {K : Type*} [Field K] (v : ExponentialValuation K) (x : K) :
    x ∈ exponentialValuationSubringAsValuationSubring v ↔
      (0 : WithTop ℝ) ≤ v x :=
  Iff.rfl





















/-- For an associated multiplicative absolute value, `|x| ≤ 1` is the same as
the exponential value being nonnegative. -/
theorem associatedAbsoluteValue_le_one_iff
    {K : Type*} [Field K] {v : ExponentialValuation K}
    {q : ℝ} {abv : AbsoluteValue K ℝ}
    (hassoc : AssociatedAbsoluteValue v q abv) {x : K} (hx : x ≠ 0) :
    abv x ≤ 1 ↔ (0 : WithTop ℝ) ≤ v x := by
  rcases hassoc.2 x hx with ⟨r, hval, habv⟩
  have hq : 1 < q := hassoc.1
  have hq_pos : 0 < q := zero_lt_one.trans hq
  have hq_not_le_one : ¬ q ≤ 1 := not_le.mpr hq
  constructor
  · intro habv_le
    have hpow : q ^ (-r) ≤ 1 := by
      simpa [habv] using habv_le
    have hneg_nonpos : -r ≤ 0 := by
      rcases (Real.rpow_le_one_iff_of_pos hq_pos).mp hpow with hcase | hcase
      · exact hcase.2
      · exact (hq_not_le_one hcase.1).elim
    have hr_nonneg : 0 ≤ r := by linarith
    have hwt : ((0 : ℝ) : WithTop ℝ) ≤ (r : WithTop ℝ) :=
      WithTop.coe_le_coe.mpr hr_nonneg
    simpa [hval] using hwt
  · intro hval_nonneg
    have hr_nonneg : 0 ≤ r := by
      have hwt : ((0 : ℝ) : WithTop ℝ) ≤ (r : WithTop ℝ) := by
        simpa [hval] using hval_nonneg
      exact WithTop.coe_le_coe.mp hwt
    have hneg_nonpos : -r ≤ 0 := by linarith
    have hpow : q ^ (-r) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt hq) hneg_nonpos
    simpa [habv] using hpow

/-- For an associated multiplicative absolute value, `|x| < 1` is the same as
the exponential value being positive. -/
theorem associatedAbsoluteValue_lt_one_iff
    {K : Type*} [Field K] {v : ExponentialValuation K}
    {q : ℝ} {abv : AbsoluteValue K ℝ}
    (hassoc : AssociatedAbsoluteValue v q abv) {x : K} (hx : x ≠ 0) :
    abv x < 1 ↔ (0 : WithTop ℝ) < v x := by
  rcases hassoc.2 x hx with ⟨r, hval, habv⟩
  have hq : 1 < q := hassoc.1
  have hq_pos : 0 < q := zero_lt_one.trans hq
  have hq_not_lt_one : ¬ q < 1 := not_lt.mpr (le_of_lt hq)
  constructor
  · intro habv_lt
    have hpow : q ^ (-r) < 1 := by
      simpa [habv] using habv_lt
    have hneg_neg : -r < 0 := by
      rcases (Real.rpow_lt_one_iff_of_pos hq_pos).mp hpow with hcase | hcase
      · exact hcase.2
      · exact (hq_not_lt_one hcase.1).elim
    have hr_pos : 0 < r := by linarith
    have hwt : ((0 : ℝ) : WithTop ℝ) < (r : WithTop ℝ) :=
      WithTop.coe_lt_coe.mpr hr_pos
    simpa [hval] using hwt
  · intro hval_pos
    have hr_pos : 0 < r := by
      have hwt : ((0 : ℝ) : WithTop ℝ) < (r : WithTop ℝ) := by
        simpa [hval] using hval_pos
      exact WithTop.coe_lt_coe.mp hwt
    have hneg_neg : -r < 0 := by linarith
    have hpow : q ^ (-r) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hq hneg_neg
    simpa [habv] using hpow

/-- For an associated multiplicative absolute value, `|x| = 1` is the same as
the exponential value being zero. -/
theorem associatedAbsoluteValue_eq_one_iff
    {K : Type*} [Field K] {v : ExponentialValuation K}
    {q : ℝ} {abv : AbsoluteValue K ℝ}
    (hassoc : AssociatedAbsoluteValue v q abv) {x : K} (hx : x ≠ 0) :
    abv x = 1 ↔ v x = 0 := by
  constructor
  · intro habv_one
    have hle : (0 : WithTop ℝ) ≤ v x :=
      (associatedAbsoluteValue_le_one_iff
        (v := v) (q := q) (abv := abv) hassoc hx).mp
        (le_of_eq habv_one)
    have hnlt : ¬ (0 : WithTop ℝ) < v x := by
      intro hvpos
      have habv_lt :
          abv x < 1 :=
        (associatedAbsoluteValue_lt_one_iff
          (v := v) (q := q) (abv := abv) hassoc hx).mpr hvpos
      exact (not_lt_of_ge (le_of_eq habv_one.symm)) habv_lt
    exact le_antisymm (le_of_not_gt hnlt) hle
  · intro hvzero
    have hle : abv x ≤ 1 :=
      (associatedAbsoluteValue_le_one_iff
        (v := v) (q := q) (abv := abv) hassoc hx).mpr
        (by simp [hvzero])
    have hnlt : ¬ abv x < 1 := by
      intro habv_lt
      have hvpos :
          (0 : WithTop ℝ) < v x :=
        (associatedAbsoluteValue_lt_one_iff
          (v := v) (q := q) (abv := abv) hassoc hx).mp habv_lt
      simp [hvzero] at hvpos
    exact le_antisymm hle (le_of_not_gt hnlt)











/-- The positive-value elements form an ideal of the exponential-valuation ring. -/
def exponentialMaxIdeal {K : Type*} [Field K]
    (v : ExponentialValuation K) : Ideal (exponentialValuationSubring v) where
  carrier := {x | (0 : WithTop ℝ) < v (x : K)}
  zero_mem' := by
    change (0 : WithTop ℝ) < v (0 : K)
    rw [(v.eq_top_iff 0).mpr rfl]
    simp
  add_mem' := by
    intro x y hx hy
    change (0 : WithTop ℝ) < v ((x + y : exponentialValuationSubring v) : K)
    have hmin : (0 : WithTop ℝ) < min (v (x : K)) (v (y : K)) :=
      lt_min hx hy
    exact lt_of_lt_of_le hmin (by simpa using v.add_le_min (x : K) (y : K))
  smul_mem' := by
    intro a x hx
    change (0 : WithTop ℝ) < v ((a : K) * (x : K))
    have ha : (0 : WithTop ℝ) ≤ v (a : K) := a.property
    rw [v.map_mul]
    have hx_le : v (x : K) ≤ v (a : K) + v (x : K) := by
      simpa [zero_add] using
        (add_le_add ha (le_rfl : v (x : K) ≤ v (x : K)))
    exact lt_of_lt_of_le hx hx_le



/-- The unit element is not in the positive-value ideal. -/
theorem one_not_mem_exponentialMaxIdeal {K : Type*} [Field K]
    (v : ExponentialValuation K) :
    (1 : exponentialValuationSubring v) ∉ exponentialMaxIdeal v := by
  change ¬ (0 : WithTop ℝ) < v (1 : K)
  simp

/-- Inside the valuation ring, not lying in the positive-value ideal is the same
as having value zero. -/
theorem not_mem_exponentialMaxIdeal_iff_value_eq_zero {K : Type*} [Field K]
    (v : ExponentialValuation K) (x : exponentialValuationSubring v) :
    x ∉ exponentialMaxIdeal v ↔ v (x : K) = 0 := by
  constructor
  · intro hx
    change ¬ (0 : WithTop ℝ) < v (x : K) at hx
    exact le_antisymm (le_of_not_gt hx) x.property
  · intro hx
    change ¬ (0 : WithTop ℝ) < v (x : K)
    simp [hx]

/-- Value-zero elements of the valuation ring are units of that ring. -/
theorem isUnit_of_exponentialValuation_eq_zero {K : Type*} [Field K]
    (v : ExponentialValuation K) {x : exponentialValuationSubring v}
    (hx : v (x : K) = 0) :
    IsUnit x := by
  rw [Submonoid.isUnit_iff_and (S := exponentialValuationSubring v) (a := x)]
  constructor
  · exact exponentialValuation_ne_zero_of_value_eq_zero v hx
  · change (0 : WithTop ℝ) ≤ v ((x : K)⁻¹)
    simp [exponentialValuation_inv_of_value_eq_zero v hx]

/-- Units of the valuation ring have value zero. -/
theorem exponentialValuation_eq_zero_of_isUnit {K : Type*} [Field K]
    (v : ExponentialValuation K) {x : exponentialValuationSubring v}
    (hx : IsUnit x) :
    v (x : K) = 0 := by
  have hx_inv :=
    (Submonoid.isUnit_iff_and (S := exponentialValuationSubring v) (a := x)).mp hx
  have hx_nonneg : (0 : WithTop ℝ) ≤ v (x : K) := x.property
  have hinv_nonneg : (0 : WithTop ℝ) ≤ v ((x : K)⁻¹) := hx_inv.2
  have hmul := v.map_mul (x : K) ((x : K)⁻¹)
  rw [mul_inv_cancel₀ hx_inv.1, exponentialValuation_one v] at hmul
  have hx_le_zero : v (x : K) ≤ 0 := by
    calc
      v (x : K) ≤ v (x : K) + v ((x : K)⁻¹) :=
        le_add_of_nonneg_right hinv_nonneg
      _ = 0 := hmul.symm
  exact le_antisymm hx_le_zero hx_nonneg

/-- A valuation-ring element outside the positive-value ideal is a unit. -/
theorem isUnit_of_not_mem_exponentialMaxIdeal {K : Type*} [Field K]
    (v : ExponentialValuation K) {x : exponentialValuationSubring v}
    (hx : x ∉ exponentialMaxIdeal v) :
    IsUnit x :=
  isUnit_of_exponentialValuation_eq_zero v
    ((not_mem_exponentialMaxIdeal_iff_value_eq_zero v x).mp hx)

/-- Units of the valuation ring do not lie in the positive-value ideal. -/
theorem not_mem_exponentialMaxIdeal_of_isUnit {K : Type*} [Field K]
    (v : ExponentialValuation K) {x : exponentialValuationSubring v}
    (hx : IsUnit x) :
    x ∉ exponentialMaxIdeal v := by
  have hzero : v (x : K) = 0 :=
    exponentialValuation_eq_zero_of_isUnit v hx
  change ¬ (0 : WithTop ℝ) < v (x : K)
  simp [hzero]

/-- In the valuation ring, the units are exactly the complement of the
positive-value ideal. -/
theorem isUnit_iff_not_mem_exponentialMaxIdeal {K : Type*} [Field K]
    (v : ExponentialValuation K) (x : exponentialValuationSubring v) :
    IsUnit x ↔ x ∉ exponentialMaxIdeal v := by
  constructor
  · exact not_mem_exponentialMaxIdeal_of_isUnit v
  · exact isUnit_of_not_mem_exponentialMaxIdeal v

/-- For an associated absolute value, the units of the valuation ring are
exactly the elements of absolute value `1`. -/
theorem associatedAbsoluteValue_isUnit_iff_eq_one
    {K : Type*} [Field K] {v : ExponentialValuation K}
    {q : ℝ} {abv : AbsoluteValue K ℝ}
    (hassoc : AssociatedAbsoluteValue v q abv)
    (x : exponentialValuationSubring v) :
    IsUnit x ↔ abv (x : K) = 1 := by
  constructor
  · intro hx
    have hvzero : v (x : K) = 0 :=
      exponentialValuation_eq_zero_of_isUnit v hx
    have hx0 : (x : K) ≠ 0 :=
      exponentialValuation_ne_zero_of_value_eq_zero v hvzero
    exact
      (associatedAbsoluteValue_eq_one_iff
        (v := v) (q := q) (abv := abv) hassoc hx0).mpr hvzero
  · intro habv_one
    have hx0 : (x : K) ≠ 0 := by
      intro hx_zero
      have hzero : abv (x : K) = 0 := by
        simp [hx_zero]
      rw [hzero] at habv_one
      norm_num at habv_one
    have hvzero : v (x : K) = 0 :=
      (associatedAbsoluteValue_eq_one_iff
        (v := v) (q := q) (abv := abv) hassoc hx0).mp habv_one
    exact isUnit_of_exponentialValuation_eq_zero v hvzero

/-- The positive-value ideal is maximal in the exponential-valuation ring. -/
theorem exponentialMaxIdeal_isMaximal {K : Type*} [Field K]
    (v : ExponentialValuation K) :
    (exponentialMaxIdeal v).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  constructor
  · exact one_not_mem_exponentialMaxIdeal v
  · intro J x hIJ hx_not_mem hxJ
    exact (Ideal.eq_top_iff_one J).mp
      (J.eq_top_of_isUnit_mem hxJ
        ((isUnit_iff_not_mem_exponentialMaxIdeal v x).mpr hx_not_mem))

/-- The exponential-valuation ring is local. -/
instance exponentialValuationSubringIsLocalRing {K : Type*} [Field K]
    (v : ExponentialValuation K) :
    IsLocalRing (exponentialValuationSubring v) :=
  IsLocalRing.of_nonunits_add fun x y hx hy => by
    have hx_mem : x ∈ exponentialMaxIdeal v := by
      by_contra hx_not_mem
      exact hx ((isUnit_iff_not_mem_exponentialMaxIdeal v x).mpr hx_not_mem)
    have hy_mem : y ∈ exponentialMaxIdeal v := by
      by_contra hy_not_mem
      exact hy ((isUnit_iff_not_mem_exponentialMaxIdeal v y).mpr hy_not_mem)
    have hxy_mem : x + y ∈ exponentialMaxIdeal v :=
      (exponentialMaxIdeal v).add_mem hx_mem hy_mem
    exact fun hxy_unit =>
      (not_mem_exponentialMaxIdeal_of_isUnit v hxy_unit) hxy_mem

/-- The positive-value ideal agrees with mathlib's maximal ideal of the
valuation ring. -/
theorem exponentialMaxIdeal_eq_maximalIdeal {K : Type*} [Field K]
    (v : ExponentialValuation K) :
    exponentialMaxIdeal v =
      IsLocalRing.maximalIdeal (exponentialValuationSubring v) :=
  IsLocalRing.eq_maximalIdeal (exponentialMaxIdeal_isMaximal v)

/-- A discrete exponential valuation has a positive generator for its value group. -/
def DiscreteExponentialValuation {K : Type*} [Field K]
    (v : ExponentialValuation K) : Prop :=
  ∃ s : ℝ, 0 < s ∧
    (∀ x : K, x ≠ 0 → ∃ m : ℤ, v x = (((m : ℝ) * s : ℝ) : WithTop ℝ)) ∧
      ∃ π : K, v π = (s : WithTop ℝ)























































/-- The DVR ideal `π^n𝒪`. -/
def uniformizerPowerIdeal {O : Type*} [CommRing O] (π : O) (n : ℕ) : Ideal O :=
  Ideal.span ({π ^ n} : Set O)

/-- Value description of a principal power ideal from the value of powers of
its generator.  This is the common calculation behind both the normalized
and the scaled discrete forms of the ideal structure theorem for discrete valuation rings. -/
theorem uniformizerPowerIdeal_mem_iff_value_ge_of_pow_value
    {K : Type*} [Field K] (v : ExponentialValuation K)
    {π : K} (πR : exponentialValuationSubring v)
    (hπR : (πR : K) = π) {s : ℝ} (hπ0 : π ≠ 0)
    (hpow : ∀ n : ℕ, v (π ^ n) = (((n : ℝ) * s : ℝ) : WithTop ℝ))
    (n : ℕ) (x : exponentialValuationSubring v) :
    x ∈ uniformizerPowerIdeal πR n ↔
      (((n : ℝ) * s : ℝ) : WithTop ℝ) ≤ v (x : K) := by
  constructor
  · intro hx
    rw [uniformizerPowerIdeal, Ideal.mem_span_singleton'] at hx
    rcases hx with ⟨a, ha⟩
    have hcast : (x : K) = (a : K) * π ^ n := by
      have hcast0 :=
        congrArg (fun y : exponentialValuationSubring v => (y : K)) ha.symm
      simpa [hπR] using hcast0
    have ha_nonneg : (0 : WithTop ℝ) ≤ v (a : K) := a.property
    have hpow_val :
        v (π ^ n) = (((n : ℝ) * s : ℝ) : WithTop ℝ) :=
      hpow n
    have hx_val :
        v (x : K) = v (a : K) + (((n : ℝ) * s : ℝ) : WithTop ℝ) := by
      rw [hcast, v.map_mul, hpow_val]
    calc
      (((n : ℝ) * s : ℝ) : WithTop ℝ) =
          0 + (((n : ℝ) * s : ℝ) : WithTop ℝ) := by simp
      _ ≤ v (a : K) + (((n : ℝ) * s : ℝ) : WithTop ℝ) :=
        add_le_add ha_nonneg le_rfl
      _ = v (x : K) := hx_val.symm
  · intro hx
    by_cases hx0 : (x : K) = 0
    · have hx_eq : x = 0 := Subtype.ext hx0
      rw [hx_eq]
      exact Ideal.zero_mem (uniformizerPowerIdeal πR n)
    · obtain ⟨r, hr⟩ := exponentialValuation_exists_real_of_ne_zero v hx0
      have hn_le_r : (n : ℝ) * s ≤ r := by
        have hle :
            ((((n : ℝ) * s : ℝ) : WithTop ℝ) ≤ ((r : ℝ) : WithTop ℝ)) := by
          simpa [hr] using hx
        exact WithTop.coe_le_coe.mp hle
      have hpow_ne : π ^ n ≠ 0 := pow_ne_zero n hπ0
      have hpow_val :
          v (π ^ n) = (((n : ℝ) * s : ℝ) : WithTop ℝ) :=
        hpow n
      have hinv_val :
          v ((π ^ n)⁻¹) = ((-((n : ℝ) * s) : ℝ) : WithTop ℝ) :=
        exponentialValuation_inv_value v hpow_ne hpow_val
      let aK : K := (x : K) * (π ^ n)⁻¹
      have ha_val :
          v aK = (((r - (n : ℝ) * s) : ℝ) : WithTop ℝ) := by
        dsimp [aK]
        rw [v.map_mul, hr, hinv_val]
        simp [sub_eq_add_neg, add_comm]
      have ha_mem : aK ∈ exponentialValuationSubring v := by
        change (0 : WithTop ℝ) ≤ v aK
        rw [ha_val]
        exact WithTop.coe_le_coe.mpr (sub_nonneg.mpr hn_le_r)
      let a : exponentialValuationSubring v := ⟨aK, ha_mem⟩
      rw [uniformizerPowerIdeal, Ideal.mem_span_singleton']
      refine ⟨a, ?_⟩
      apply Subtype.ext
      change ((x : K) * (π ^ n)⁻¹) * (πR : K) ^ n = (x : K)
      rw [hπR, mul_assoc, inv_mul_cancel₀ hpow_ne, mul_one]







/-- A nonnegative member of a positive real lattice has a natural-number
index.  This is the order-theoretic step common to normalized and scaled
discrete valuations. -/
theorem exists_nat_index_of_nonneg_int_multiple
    {a : WithTop ℝ} {s : ℝ} (ha : 0 ≤ a) (hs : 0 < s)
    (h : ∃ m : ℤ, a = (((m : ℝ) * s : ℝ) : WithTop ℝ)) :
    ∃ n : ℕ, a = (((n : ℝ) * s : ℝ) : WithTop ℝ) := by
  rcases h with ⟨m, rfl⟩
  cases m with
  | ofNat n => exact ⟨n, by simp⟩
  | negSucc n =>
      have hmneg : ((Int.negSucc n : ℤ) : ℝ) < 0 := by
        have hcast :
            ((Int.negSucc n : ℤ) : ℝ) = -((n : ℝ) + 1) := by
          norm_num [Int.cast_negSucc]
        rw [hcast]
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
      exact False.elim <| (not_lt_of_ge (WithTop.coe_le_coe.mp ha))
        (mul_neg_of_neg_of_pos hmneg hs)











/-- A field element of positive discrete value, viewed inside the valuation ring. -/
def discretePrimeElementInValuationSubring
    {K : Type*} [Field K] (v : ExponentialValuation K)
    {π : K} {s : ℝ} (hs : 0 ≤ s) (hπ : v π = (s : WithTop ℝ)) :
    exponentialValuationSubring v :=
  ⟨π, by
    change (0 : WithTop ℝ) ≤ v π
    rw [hπ]
    exact WithTop.coe_le_coe.mpr hs⟩

/-- A finite positive value forces the chosen discrete prime element to be nonzero. -/
theorem discretePrimeElement_ne_zero_of_value
    {K : Type*} [Field K] (v : ExponentialValuation K)
    {π : K} {s : ℝ} (hπ : v π = (s : WithTop ℝ)) :
    π ≠ 0 := by
  intro hzero
  have htop : v π = ⊤ := (v.eq_top_iff π).mpr hzero
  rw [hπ] at htop
  simp at htop

/-- Powers of a discrete prime element have the expected scaled value. -/
theorem discretePrimeElement_pow_value
    {K : Type*} [Field K] (v : ExponentialValuation K)
    {π : K} {s : ℝ} (hπ : v π = (s : WithTop ℝ)) (n : ℕ) :
    v (π ^ n) = (((n : ℝ) * s : ℝ) : WithTop ℝ) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, v.map_mul, ih, hπ]
      change ((((n : ℝ) * s + s : ℝ) : WithTop ℝ) =
        ((((n + 1 : ℕ) : ℝ) * s : ℝ) : WithTop ℝ))
      congr 1
      norm_num [Nat.cast_succ]
      ring

/-- A nonzero element of the valuation ring of a discrete valuation has a
nonnegative integer multiple of the least positive value. -/
theorem discreteExponentialValuation_subring_exists_nat_value
    {K : Type*} [Field K] {v : ExponentialValuation K}
    {s : ℝ} (hs : 0 < s)
    (hvalues : ∀ x : K, x ≠ 0 → ∃ m : ℤ,
      v x = (((m : ℝ) * s : ℝ) : WithTop ℝ))
    {x : exponentialValuationSubring v} (hx : (x : K) ≠ 0) :
    ∃ n : ℕ, v (x : K) = (((n : ℝ) * s : ℝ) : WithTop ℝ) := by
  exact exists_nat_index_of_nonneg_int_multiple x.property hs (hvalues (x : K) hx)

/-- The ideal structure theorem for discrete valuation rings, scaled value description for a non-normalized discrete
prime element: membership in `π^n𝒪` is the lower bound `n * s ≤ v(x)`. -/
theorem discrete_uniformizerPowerIdeal_mem_iff_value_ge
    {K : Type*} [Field K] (v : ExponentialValuation K)
    {π : K} {s : ℝ} (hs : 0 < s) (hπ : v π = (s : WithTop ℝ))
    (n : ℕ) (x : exponentialValuationSubring v) :
    x ∈ uniformizerPowerIdeal
        (discretePrimeElementInValuationSubring v (le_of_lt hs) hπ) n ↔
      (((n : ℝ) * s : ℝ) : WithTop ℝ) ≤ v (x : K) := by
  have hπ0 : π ≠ 0 := discretePrimeElement_ne_zero_of_value v hπ
  exact
    uniformizerPowerIdeal_mem_iff_value_ge_of_pow_value
      (v := v) (π := π)
      (πR := discretePrimeElementInValuationSubring v (le_of_lt hs) hπ)
      rfl (s := s) hπ0 (discretePrimeElement_pow_value v hπ) n x






end Valuations
end LubinTate

end
