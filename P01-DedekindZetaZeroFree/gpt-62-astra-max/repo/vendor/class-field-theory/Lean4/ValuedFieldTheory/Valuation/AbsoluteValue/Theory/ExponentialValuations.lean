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

section

variable {K : Type*} [Field K] (v : ExponentialValuation K)

/-- A multiplicative absolute value associated to an exponential valuation by `|x| = q^{-v(x)}`. -/
def AssociatedAbsoluteValue (q : ℝ) (abv : AbsoluteValue K ℝ) : Prop :=
  1 < q ∧ ∀ x : K, x ≠ 0 → ∃ r : ℝ,
    v x = (r : WithTop ℝ) ∧ abv x = Real.rpow q (-r)

/-- The valuation ring `{x | v(x) ≥ 0}` attached to an exponential valuation. -/
def exponentialValuationRing : Set K :=
  {x | (0 : WithTop ℝ) ≤ v x}

/-- Nonzero elements have finite value for a exponential valuation. -/
theorem exponentialValuation_ne_top_of_ne_zero {x : K} (hx : x ≠ 0) :
    v x ≠ ⊤ := fun htop => hx ((v.eq_top_iff x).mp htop)

/-- A nonzero element has a real-valued exponential valuation. -/
theorem exponentialValuation_exists_real_of_ne_zero {x : K} (hx : x ≠ 0) :
    ∃ r : ℝ, v x = (r : WithTop ℝ) := by
  rcases WithTop.ne_top_iff_exists.mp
      (exponentialValuation_ne_top_of_ne_zero v hx) with ⟨r, hr⟩
  exact ⟨r, hr.symm⟩

/-- The value of `1` is `0` for a exponential valuation. -/
@[simp]
theorem exponentialValuation_one :
    v (1 : K) = 0 := by
  obtain ⟨r, hr⟩ :=
    exponentialValuation_exists_real_of_ne_zero v one_ne_zero
  have hmul := v.map_mul (1 : K) (1 : K)
  rw [one_mul, hr] at hmul
  have hmul_real : r = r + r :=
    WithTop.coe_eq_coe.mp (by simpa [WithTop.coe_add] using hmul)
  have hr0 : r = 0 := by linarith
  simp [hr, hr0]

/-- The value of `-1` is `0` for a exponential valuation. -/
@[simp]
theorem exponentialValuation_neg_one :
    v (-1 : K) = 0 := by
  obtain ⟨r, hr⟩ :=
    exponentialValuation_exists_real_of_ne_zero v
      (neg_ne_zero.mpr one_ne_zero)
  have hmul := v.map_mul (-1 : K) (-1 : K)
  have hsq : (-1 : K) * (-1 : K) = 1 := by ring
  rw [hsq, exponentialValuation_one v, hr] at hmul
  have hmul_real : (0 : ℝ) = r + r :=
    WithTop.coe_eq_coe.mp (by exact hmul)
  have hr0 : r = 0 := by linarith
  simp [hr, hr0]

/-- Negation does not change a exponential valuation. -/
@[simp]
theorem exponentialValuation_neg (x : K) :
    v (-x) = v x := by
  rw [← neg_one_mul, v.map_mul, exponentialValuation_neg_one, zero_add]

/-- An element of value zero is nonzero. -/
theorem exponentialValuation_ne_zero_of_value_eq_zero {x : K} (hx : v x = 0) :
    x ≠ 0 := by
  intro hzero
  simpa [hx] using (v.eq_top_iff x).mpr hzero

/-- The inverse of a value-zero element again has value zero. -/
theorem exponentialValuation_inv_of_value_eq_zero {x : K} (hx : v x = 0) :
    v x⁻¹ = 0 := by
  have hmul := v.map_mul x x⁻¹
  rw [mul_inv_cancel₀ (exponentialValuation_ne_zero_of_value_eq_zero v hx), exponentialValuation_one v, hx] at hmul
  simpa using hmul.symm

/-- Finite inverse-value formula for a exponential valuation. -/
theorem exponentialValuation_inv_value {x : K} (hx : x ≠ 0) {r : ℝ}
    (hval : v x = (r : WithTop ℝ)) :
    v x⁻¹ = ((-r : ℝ) : WithTop ℝ) := by
  obtain ⟨s, hs⟩ :=
    exponentialValuation_exists_real_of_ne_zero v (inv_ne_zero hx)
  have hmul := v.map_mul x x⁻¹
  rw [mul_inv_cancel₀ hx, exponentialValuation_one v, hval, hs] at hmul
  have hmul_real : (0 : ℝ) = r + s :=
    WithTop.coe_eq_coe.mp (by exact hmul)
  have hs_eq : s = -r := by
    linarith
  simp [hs, hs_eq]

/-- The set `{x | 0 ≤ v x}` is a subring. -/
def exponentialValuationSubring : Subring K where
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

end

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
      simp_all [hr]
    · right
      change (0 : WithTop ℝ) ≤ v x⁻¹
      rw [exponentialValuation_inv_value v hx hr]
      refine WithTop.coe_le_coe.mpr ?_
      linarith

section

variable {K : Type*} [Field K] (v : ExponentialValuation K)

/-- The absolute values subring satisfies mathlib's valuation-subring
membership alternative. -/
theorem exponentialValuationSubring_mem_or_inv_mem (x : K) :
    x ∈ exponentialValuationSubring v ∨
      x⁻¹ ∈ exponentialValuationSubring v := by
  solve_by_elim [exponentialValuationRing_mem_or_inv_mem]

/-- The exponential-valuation ring, bundled as mathlib's `ValuationSubring`. -/
def exponentialValuationSubringAsValuationSubring :
    ValuationSubring K :=
  ValuationSubring.ofSubring (exponentialValuationSubring v)
    (exponentialValuationSubring_mem_or_inv_mem v)

end

/-- Membership in the bundled mathlib valuation subring is the defining condition
`0 ≤ v x`. -/
theorem mem_exponentialValuationSubringAsValuationSubring_iff
    {K : Type*} [Field K] (v : ExponentialValuation K) (x : K) :
    x ∈ exponentialValuationSubringAsValuationSubring v ↔
      (0 : WithTop ℝ) ≤ v x :=
  Iff.rfl

section

variable {K : Type*} [Field K] {v : ExponentialValuation K} {q : ℝ} {abv : AbsoluteValue K ℝ}
    (hassoc : AssociatedAbsoluteValue v q abv) {x : K} (hx : x ≠ 0)

include hassoc hx in
/-- For an associated multiplicative absolute value, `|x| ≤ 1` is the same as
the exponential value being nonnegative. -/
theorem associatedAbsoluteValue_le_one_iff :
    abv x ≤ 1 ↔ (0 : WithTop ℝ) ≤ v x := by
  rcases hassoc.2 x hx with ⟨r, hval, habv⟩
  have hq := hassoc.1
  constructor
  · intro habv_le
    have hneg_nonpos : -r ≤ 0 := by
      rcases (Real.rpow_le_one_iff_of_pos (zero_lt_one.trans hq)).mp (by
        simpa [habv] using habv_le) with hcase | hcase
      · exact hcase.2
      · linarith
    simp_all
  · intro hval_nonneg
    have hr_nonneg : 0 ≤ r := by
      refine WithTop.coe_le_coe.mp ?_
      simpa [hval] using hval_nonneg
    have hneg_nonpos : -r ≤ 0 := by linarith
    simpa [habv] using Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt hq) hneg_nonpos

include hassoc hx in
/-- For an associated multiplicative absolute value, `|x| < 1` is the same as
the exponential value being positive. -/
theorem associatedAbsoluteValue_lt_one_iff :
    abv x < 1 ↔ (0 : WithTop ℝ) < v x := by
  rcases hassoc.2 x hx with ⟨r, hval, habv⟩
  have hq := hassoc.1
  constructor
  · intro habv_lt
    have hneg_neg : -r < 0 := by
      rcases (Real.rpow_lt_one_iff_of_pos (zero_lt_one.trans hq)).mp (by
        simpa [habv] using habv_lt) with hcase | hcase
      · exact hcase.2
      · linarith
    simp_all
  · intro hval_pos
    have hr_pos : 0 < r := by
      refine WithTop.coe_lt_coe.mp ?_
      simpa [hval] using hval_pos
    have hneg_neg : -r < 0 := by linarith
    simpa [habv] using Real.rpow_lt_one_of_one_lt_of_neg hq hneg_neg

include hassoc hx in
/-- For an associated multiplicative absolute value, `|x| = 1` is the same as
the exponential value being zero. -/
theorem associatedAbsoluteValue_eq_one_iff :
    abv x = 1 ↔ v x = 0 := by
  constructor
  · intro habv_one
    refine le_antisymm (le_of_not_gt ?_) ((associatedAbsoluteValue_le_one_iff
         hassoc hx).mp
      (le_of_eq habv_one))
    intro hvpos
    exact (not_lt_of_ge (le_of_eq habv_one.symm)) ((associatedAbsoluteValue_lt_one_iff
      hassoc hx).mpr hvpos)
  · intro hvzero
    refine le_antisymm ((associatedAbsoluteValue_le_one_iff
         hassoc hx).mpr
      (by simp [hvzero])) (le_of_not_gt ?_)
    intro habv_lt
    simpa [hvzero] using (associatedAbsoluteValue_lt_one_iff
           hassoc hx).mp habv_lt

end

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
    exact le_antisymm (le_of_not_gt hx) x.property
  · intro hx
    change ¬ (0 : WithTop ℝ) < v (x : K)
    simp [hx]

section

variable {K : Type*} [Field K] (v : ExponentialValuation K) {x : exponentialValuationSubring v}

/-- Value-zero elements of the valuation ring are units of that ring. -/
theorem isUnit_of_exponentialValuation_eq_zero
    (hx : v (x : K) = 0) :
    IsUnit x := by
  rw [Submonoid.isUnit_iff_and]
  constructor
  · exact exponentialValuation_ne_zero_of_value_eq_zero v hx
  · change (0 : WithTop ℝ) ≤ v ((x : K)⁻¹)
    simp [exponentialValuation_inv_of_value_eq_zero v hx]

/-- Units of the valuation ring have value zero. -/
theorem exponentialValuation_eq_zero_of_isUnit
    (hx : IsUnit x) :
    v (x : K) = 0 := by
  have hx_inv :=
    (Submonoid.isUnit_iff_and).mp hx
  have hmul := v.map_mul (x : K) ((x : K)⁻¹)
  simp [mul_inv_cancel₀ hx_inv.1] at hmul
  exact le_antisymm (Trans.trans (le_add_of_nonneg_right hx_inv.right) (Eq.symm hmul)) x.property

/-- A valuation-ring element outside the positive-value ideal is a unit. -/
theorem isUnit_of_not_mem_exponentialMaxIdeal
    (hx : x ∉ exponentialMaxIdeal v) :
    IsUnit x :=
  isUnit_of_exponentialValuation_eq_zero v
    ((not_mem_exponentialMaxIdeal_iff_value_eq_zero v x).mp hx)

end

/-- Units of the valuation ring do not lie in the positive-value ideal. -/
theorem not_mem_exponentialMaxIdeal_of_isUnit {K : Type*} [Field K]
    (v : ExponentialValuation K) {x : exponentialValuationSubring v}
    (hx : IsUnit x) :
    x ∉ exponentialMaxIdeal v := by
  change ¬ (0 : WithTop ℝ) < v (x : K)
  simp [(exponentialValuation_eq_zero_of_isUnit v hx)]

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
    have hvzero :=
      exponentialValuation_eq_zero_of_isUnit v hx
    exact
      (associatedAbsoluteValue_eq_one_iff
           hassoc (exponentialValuation_ne_zero_of_value_eq_zero v hvzero)).mpr hvzero
  · intro habv_one
    have hx0 : (x : K) ≠ 0 := by
      intro hx_zero
      have hzero : abv (x : K) = 0 := by
        simp [hx_zero]
      rw [hzero] at habv_one
      norm_num at habv_one
    exact isUnit_of_exponentialValuation_eq_zero v ((associatedAbsoluteValue_eq_one_iff
      hassoc hx0).mp habv_one)

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
    exact fun hxy_unit =>
      (not_mem_exponentialMaxIdeal_of_isUnit v hxy_unit) ((exponentialMaxIdeal v).add_mem hx_mem hy_mem)

section

variable {K : Type*} [Field K] (v : ExponentialValuation K)

/-- The positive-value ideal agrees with mathlib's maximal ideal of the
valuation ring. -/
theorem exponentialMaxIdeal_eq_maximalIdeal :
    exponentialMaxIdeal v =
      IsLocalRing.maximalIdeal (exponentialValuationSubring v) :=
  IsLocalRing.eq_maximalIdeal (exponentialMaxIdeal_isMaximal v)

/-- A discrete exponential valuation has a positive generator for its value group. -/
def DiscreteExponentialValuation : Prop :=
  ∃ s : ℝ, 0 < s ∧
    (∀ x : K, x ≠ 0 → ∃ m : ℤ, v x = (((m : ℝ) * s : ℝ) : WithTop ℝ)) ∧
      ∃ π : K, v π = (s : WithTop ℝ)

/-- A normalized discrete exponential valuation has value group `ℤ`
and a prime element of value `1`.
-/
def NormalizedExponentialValuation : Prop :=
  DiscreteExponentialValuation v ∧
    (∀ x : K, x ≠ 0 → ∃ m : ℤ, v x = ((m : ℝ) : WithTop ℝ)) ∧
      ∃ π : K, v π = (1 : WithTop ℝ)

/-- A prime element for a normalized exponential valuation. -/
def PrimeElementFor (π : K) : Prop :=
  π ≠ 0 ∧ v π = (1 : WithTop ℝ)

/-- A normalized prime element, regarded as an element of the valuation ring. -/
def primeElementInValuationSubring {π : K}
    (hπ : PrimeElementFor v π) :
    exponentialValuationSubring v :=
  ⟨π, by
    change (0 : WithTop ℝ) ≤ v π
    rw [hπ.2]
    exact WithTop.coe_le_coe.mpr zero_le_one⟩

end

/-- A normalized prime element lies in the positive-value maximal ideal. -/
theorem primeElement_mem_exponentialMaxIdeal
    {K : Type*} [Field K] (v : ExponentialValuation K) {π : K}
    (hπ : PrimeElementFor v π) :
    primeElementInValuationSubring v hπ ∈ exponentialMaxIdeal v := by
  change (0 : WithTop ℝ) < v π
  rw [hπ.2]
  positivity

/-- A normalized prime element lies in mathlib's maximal ideal of the valuation ring. -/
theorem primeElement_mem_maximalIdeal
    {K : Type*} [Field K] (v : ExponentialValuation K) {π : K}
    (hπ : PrimeElementFor v π) :
    primeElementInValuationSubring v hπ ∈
      IsLocalRing.maximalIdeal (exponentialValuationSubring v) := by
  rw [← exponentialMaxIdeal_eq_maximalIdeal v]
  apply primeElement_mem_exponentialMaxIdeal

section

variable {K : Type*} [Field K] (v : ExponentialValuation K) {π : K} (hπ : PrimeElementFor v π)

/-- A normalized prime element is nonzero as an element of the valuation ring. -/
theorem primeElementInValuationSubring_ne_zero :
    primeElementInValuationSubring v hπ ≠ 0 := fun hzero => hπ.1 (by
    simp_all [primeElementInValuationSubring])

include hπ in
/-- The inverse of a normalized prime element has value `-1`. -/
theorem primeElementFor_inv_value :
    v π⁻¹ = ((-1 : ℝ) : WithTop ℝ) := by
  obtain ⟨s, hs⟩ :=
    exponentialValuation_exists_real_of_ne_zero v (inv_ne_zero hπ.1)
  have hmul := v.map_mul π π⁻¹
  rw [mul_inv_cancel₀ hπ.1, exponentialValuation_one v, hπ.2, hs] at hmul
  have hmul_real : (0 : ℝ) = 1 + s :=
    WithTop.coe_eq_coe.mp (by exact hmul)
  have hs_eq : s = -1 := by
    linarith
  simp [hs, hs_eq]

include hπ in
/-- Powers of a normalized prime element have the expected normalized value. -/
theorem primeElementFor_pow_value (n : ℕ) :
    v (π ^ n) = ((n : ℝ) : WithTop ℝ) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, v.map_mul, ih, hπ.2]
      norm_num

end

section

variable {K : Type*} [Field K] {v : ExponentialValuation K} (hv : NormalizedExponentialValuation v)
    {π : K} (hπ : PrimeElementFor v π)

include hv in
/-- In a normalized exponential valuation, a normalized prime element generates the
positive-value maximal ideal. -/
theorem exponentialMaxIdeal_eq_span_primeElement_of_normalized :
    exponentialMaxIdeal v =
      Ideal.span
        ({primeElementInValuationSubring v hπ} :
          Set (exponentialValuationSubring v)) := by
  apply le_antisymm
  · intro x hx
    change (0 : WithTop ℝ) < v (x : K) at hx
    by_cases hx0 : (x : K) = 0
    · simp_all
    · rcases hv.2.1 (x : K) hx0 with ⟨m, hm⟩
      have hxpos_real : (0 : ℝ) < (m : ℝ) := by
        refine WithTop.coe_lt_coe.mp ?_
        simpa [hm] using hx
      have hm_pos := Int.cast_pos.mp hxpos_real
      have hm_ge_one : (1 : ℤ) ≤ m := by
        omega
      have hm_sub_nonneg : (0 : ℝ) ≤ (m : ℝ) - 1 := by
        have hm_real : (1 : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast hm_ge_one
        linarith
      have hy_val :
          v ((x : K) * π⁻¹) = (((m : ℝ) - 1 : ℝ) : WithTop ℝ) := by
        rw [v.map_mul, hm, (primeElementFor_inv_value v hπ)]
        simp [sub_eq_add_neg, add_comm]
      have hy_mem : (x : K) * π⁻¹ ∈ exponentialValuationSubring v := by
        change (0 : WithTop ℝ) ≤ v ((x : K) * π⁻¹)
        rw [hy_val]
        exact WithTop.coe_le_coe.mpr hm_sub_nonneg
      refine Ideal.mem_span_singleton'.mpr ⟨(⟨(x : K) * π⁻¹, hy_mem⟩), ?_⟩
      apply Subtype.ext
      change ((x : K) * π⁻¹) * π = (x : K)
      rw [mul_assoc, inv_mul_cancel₀ hπ.1, mul_one]
  exact (Ideal.span_singleton_le_iff_mem (exponentialMaxIdeal v)).mpr (primeElement_mem_exponentialMaxIdeal v hπ)

include hv in
/-- In a normalized exponential valuation, powers of the positive-value
maximal ideal are generated by powers of a normalized prime element. -/
theorem exponentialMaxIdeal_pow_eq_span_primeElement_pow_of_normalized (n : ℕ) :
    (exponentialMaxIdeal v) ^ n =
      Ideal.span
        ({(primeElementInValuationSubring v hπ) ^ n} :
          Set (exponentialValuationSubring v)) := by
  rw [exponentialMaxIdeal_eq_span_primeElement_of_normalized hv hπ]
  apply Ideal.span_singleton_pow

end

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
      simpa [hπR] using (congrArg (fun y : exponentialValuationSubring v => (y : K)) ha.symm)
    have hx_val :
        v (x : K) = v (a : K) + (((n : ℝ) * s : ℝ) : WithTop ℝ) := by
      rw [hcast, v.map_mul, (hpow n)]
    calc
      _ =
          0 + (((n : ℝ) * s : ℝ) : WithTop ℝ) := by simp
      _ ≤ v (a : K) + (((n : ℝ) * s : ℝ) : WithTop ℝ) :=
        add_le_add a.property le_rfl
      _ = v (x : K) := hx_val.symm
  · intro hx
    by_cases hx0 : (x : K) = 0
    · simp_all
    · obtain ⟨r, hr⟩ := exponentialValuation_exists_real_of_ne_zero v hx0
      have hn_le_r : (n : ℝ) * s ≤ r := by
        refine WithTop.coe_le_coe.mp ?_
        simpa [hr] using hx
      have hpow_ne := pow_ne_zero n hπ0
      let aK := (x : K) * (π ^ n)⁻¹
      have ha_val :
          v aK = (((r - (n : ℝ) * s) : ℝ) : WithTop ℝ) := by
        dsimp [aK]
        rw [v.map_mul, hr, (exponentialValuation_inv_value v hpow_ne (hpow n))]
        simp [sub_eq_add_neg, add_comm]
      have ha_mem : aK ∈ exponentialValuationSubring v := by
        change (0 : WithTop ℝ) ≤ v aK
        rw [ha_val]
        exact WithTop.coe_le_coe.mpr (sub_nonneg.mpr hn_le_r)
      rw [uniformizerPowerIdeal, Ideal.mem_span_singleton']
      refine ⟨(⟨aK, ha_mem⟩), ?_⟩
      apply Subtype.ext
      change ((x : K) * (π ^ n)⁻¹) * (πR : K) ^ n = (x : K)
      rw [hπR, mul_assoc, inv_mul_cancel₀ hpow_ne, mul_one]

/-- If an ideal contains an element whose value is exactly the value of
`π^n`, then it contains the principal ideal generated by `π^n`. -/
theorem uniformizerPowerIdeal_le_ideal_of_mem_value_eq_of_pow_value
    {K : Type*} [Field K] {v : ExponentialValuation K}
    {π : K} (πR : exponentialValuationSubring v)
    (hπR : (πR : K) = π) {s : ℝ} (hπ0 : π ≠ 0)
    (hpow : ∀ n : ℕ, v (π ^ n) = (((n : ℝ) * s : ℝ) : WithTop ℝ))
    {I : Ideal (exponentialValuationSubring v)} {n : ℕ}
    {x : exponentialValuationSubring v}
    (hxI : x ∈ I)
    (hxval : v (x : K) = (((n : ℝ) * s : ℝ) : WithTop ℝ)) :
    uniformizerPowerIdeal πR n ≤ I := by
  have hpow_ne : π ^ n ≠ 0 := pow_ne_zero n hπ0
  have hpow_val :
      v (π ^ n) = (((n : ℝ) * s : ℝ) : WithTop ℝ) :=
    hpow n
  have hinv_val :
      v ((π ^ n)⁻¹) = ((-((n : ℝ) * s) : ℝ) : WithTop ℝ) :=
    exponentialValuation_inv_value v hpow_ne hpow_val
  let uK : K := (x : K) * (π ^ n)⁻¹
  have hu_val : v uK = 0 := by
    dsimp [uK]
    rw [v.map_mul, hxval, hinv_val]
    change ((((n : ℝ) * s + -((n : ℝ) * s) : ℝ) : WithTop ℝ) = 0)
    simp
  have hu_mem : uK ∈ exponentialValuationSubring v := by
    change (0 : WithTop ℝ) ≤ v uK
    rw [hu_val]
  let u : exponentialValuationSubring v := ⟨uK, hu_mem⟩
  have hu_subval : v (u : K) = 0 := by
    simpa [u, uK] using hu_val
  have hu_unit : IsUnit u :=
    isUnit_of_exponentialValuation_eq_zero v hu_subval
  have hx_repr : x = u * πR ^ n := by
    apply Subtype.ext
    change (x : K) = ((x : K) * (π ^ n)⁻¹) * (πR : K) ^ n
    rw [hπR, mul_assoc, inv_mul_cancel₀ hpow_ne, mul_one]
  rw [uniformizerPowerIdeal, Ideal.span_singleton_le_iff_mem]
  rcases hu_unit with ⟨uUnit, huUnit⟩
  have hxI' : u * πR ^ n ∈ I := by
    simpa [hx_repr] using hxI
  have hmem :
      ((uUnit⁻¹ : (exponentialValuationSubring v)ˣ) :
          exponentialValuationSubring v) *
        (u * πR ^ n) ∈ I :=
    I.mul_mem_left _ hxI'
  simpa [← huUnit] using hmem

/-- A nonzero ideal has an element of least indexed value whenever every
nonzero element has a value in a monotone sequence.  This isolates the
well-ordering argument shared by the normalized and scaled forms of
the ideal structure theorem for discrete valuation rings. -/
theorem ideal_exists_min_value_of_nat_indexed_values
    {O α : Type*} [CommRing O] [Preorder α]
    (value : O → α) (weight : ℕ → α) (hweight : Monotone weight)
    (hvalue : ∀ x : O, x ≠ 0 → ∃ n : ℕ, value x = weight n)
    (I : Ideal O) (hI : I ≠ ⊥) :
    ∃ n : ℕ, ∃ x : O,
      x ∈ I ∧ x ≠ 0 ∧ value x = weight n ∧
        ∀ y : O, y ∈ I → y ≠ 0 → weight n ≤ value y := by
  classical
  have hnonzero : ∃ x : O, x ∈ I ∧ x ≠ 0 := by
    by_contra h
    push Not at h
    apply hI
    apply le_antisymm
    · exact h
    · exact bot_le
  have hP : ∃ n : ℕ, (fun n => ∃ x : O, x ∈ I ∧ x ≠ 0 ∧ value x = weight n) n := by
    rcases hnonzero with ⟨x, hxI, hx0⟩
    rcases hvalue x hx0 with ⟨n, hn⟩
    exact ⟨n, x, hxI, hx0, hn⟩
  let n := Nat.find hP
  rcases Nat.find_spec hP with ⟨x, hxI, hx0, hxval⟩
  refine ⟨n, x, hxI, hx0, hxval, ?_⟩
  intro y hyI hy0
  rcases hvalue y hy0 with ⟨m, hm⟩
  exact (hweight (Nat.find_min' hP ⟨y, hyI, hy0, hm⟩)).trans_eq hm.symm

/-- The ideal structure theorem for discrete valuation rings, value description of the ideals `π^n𝒪`: for a normalized
prime element, membership in the principal power ideal is exactly the lower
bound `v(x) ≥ n`. -/
theorem uniformizerPowerIdeal_mem_iff_value_ge
    {K : Type*} [Field K] (v : ExponentialValuation K) {π : K}
    (hπ : PrimeElementFor v π) (n : ℕ)
    (x : exponentialValuationSubring v) :
    x ∈ uniformizerPowerIdeal (primeElementInValuationSubring v hπ) n ↔
      ((n : ℝ) : WithTop ℝ) ≤ v (x : K) := by
  simpa using
    uniformizerPowerIdeal_mem_iff_value_ge_of_pow_value
      (v := v) (π := π) (πR := primeElementInValuationSubring v hπ)
      rfl (s := 1) hπ.1
      (fun n => by
        grind [primeElementFor_pow_value])
      n x

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
      refine False.elim <| (not_lt_of_ge (WithTop.coe_le_coe.mp ha))
        (mul_neg_of_neg_of_pos ?_ hs)
      have hcast :
          ((Int.negSucc n : ℤ) : ℝ) = -((n : ℝ) + 1) := by
        norm_num [Int.cast_negSucc]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]

section

variable {K : Type*} [Field K] {v : ExponentialValuation K}

/-- In a normalized exponential valuation, a nonzero element of the valuation
ring has a natural-number value. -/
theorem normalizedExponentialValuation_subring_exists_nat_value
    (hv : NormalizedExponentialValuation v)
    {x : exponentialValuationSubring v} (hx : (x : K) ≠ 0) :
    ∃ n : ℕ, v (x : K) = ((n : ℝ) : WithTop ℝ) := by
  have hindexed :
      ∃ m : ℤ, v (x : K) = (((m : ℝ) * 1 : ℝ) : WithTop ℝ) := by
    rcases hv.2.1 (x : K) hx with ⟨m, hm⟩
    exact ⟨m, by simpa using hm⟩
  rcases exists_nat_index_of_nonneg_int_multiple x.property zero_lt_one hindexed with
    ⟨n, hn⟩
  exact ⟨n, by simpa using hn⟩

/-- If an ideal contains an element of value exactly `n`, then it contains
`π^n𝒪`. -/
theorem uniformizerPowerIdeal_le_ideal_of_mem_value_eq {π : K}
    (hπ : PrimeElementFor v π)
    {I : Ideal (exponentialValuationSubring v)} {n : ℕ}
    {x : exponentialValuationSubring v}
    (hxI : x ∈ I)
    (hxval : v (x : K) = ((n : ℝ) : WithTop ℝ)) :
    uniformizerPowerIdeal (primeElementInValuationSubring v hπ) n ≤ I := uniformizerPowerIdeal_le_ideal_of_mem_value_eq_of_pow_value
      (v := v) (π := π) (πR := primeElementInValuationSubring v hπ)
      rfl (s := 1) hπ.1
      (fun n => by
        grind [primeElementFor_pow_value])
      hxI (by simpa using hxval)

end

variable {K : Type*} [Field K] {v : ExponentialValuation K} (hv : NormalizedExponentialValuation v)
    {π : K} (hπ : PrimeElementFor v π)

include hv in
/-- The ideal structure theorem for discrete valuation rings, ideal classification part: every nonzero ideal of a
normalized exponential-valuation ring is one of the ideals `π^n𝒪`. -/
theorem nonzero_ideal_eq_uniformizerPowerIdeal
    (I : Ideal (exponentialValuationSubring v)) (hI : I ≠ ⊥) :
    ∃ n : ℕ,
      I = uniformizerPowerIdeal (primeElementInValuationSubring v hπ) n := by
  have hvalue :
      ∀ x : exponentialValuationSubring v, x ≠ 0 →
        ∃ n : ℕ, v (x : K) = ((n : ℝ) : WithTop ℝ) := by
    intro x hx
    apply normalizedExponentialValuation_subring_exists_nat_value hv
    intro hxK
    exact hx (Subtype.ext hxK)
  rcases ideal_exists_min_value_of_nat_indexed_values
      (value := fun x : exponentialValuationSubring v => v (x : K))
      (weight := fun n : ℕ => ((n : ℝ) : WithTop ℝ))
      (fun _ _ hnm => WithTop.coe_le_coe.mpr (Nat.cast_le.mpr hnm))
      hvalue I hI with
    ⟨n, x, hxI, _hx0, hxval, hmin⟩
  refine ⟨n, le_antisymm ?_ ?_⟩
  · intro y hyI
    rw [uniformizerPowerIdeal_mem_iff_value_ge v hπ n y]
    by_cases hyK0 : (y : K) = 0
    · rw [((v.eq_top_iff (y : K)).mpr hyK0)]
      simp
    · simp_all
  · grind [uniformizerPowerIdeal_le_ideal_of_mem_value_eq]

include hv hπ in
/-- The ideal structure theorem for discrete valuation rings, PID part: the valuation ring of a normalized
exponential valuation is a principal ideal ring. -/
theorem normalizedExponentialValuationSubring_isPrincipalIdealRing :
    IsPrincipalIdealRing (exponentialValuationSubring v) := by
  constructor
  intro I
  by_cases hI : I = ⊥
  · rw [hI]
    exact ⟨0, by simp⟩
  · rcases nonzero_ideal_eq_uniformizerPowerIdeal hv hπ I hI with
      ⟨n, hIn⟩
    refine ⟨(primeElementInValuationSubring v hπ) ^ n, ?_⟩
    exact hIn

include hv hπ in
/-- The ideal structure theorem for discrete valuation rings, DVR part: the valuation ring of a normalized
exponential valuation is a discrete valuation ring. -/
theorem normalizedExponentialValuationSubring_isDiscreteValuationRing :
    IsDiscreteValuationRing (exponentialValuationSubring v) := by
  have :=
    normalizedExponentialValuationSubring_isPrincipalIdealRing hv hπ
  refine { not_a_field' := ?_ }
  intro hmax
  refine primeElementInValuationSubring_ne_zero v hπ ?_
  exact (by
  simpa [hmax] using (primeElement_mem_maximalIdeal v hπ))
end Valuations
end LubinTate

end
