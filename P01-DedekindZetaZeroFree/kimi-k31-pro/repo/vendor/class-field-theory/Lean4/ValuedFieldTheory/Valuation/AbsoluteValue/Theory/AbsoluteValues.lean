module

public import Mathlib.Analysis.AbsoluteValue.Equivalence
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.NumberTheory.Ostrowski
public import Mathlib.Topology.UniformSpace.AbsoluteValue

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Absolute values and exponential valuations

This module collects the valuation-theory material used by local class field
theory. General results on equivalence of absolute values, Ostrowski theory,
approximation, and rational-function examples are imported from Mathlib where
needed.
-/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace LubinTate
namespace Valuations

/-- The distance attached by the absolute-value construction to an absolute value. -/
def absoluteValueDist {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (x y : K) : ℝ :=
  v (x - y)



/-- The absolute-value distance separates points. -/
theorem absoluteValueDist_eq_zero_iff
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (x y : K) :
    absoluteValueDist v x y = 0 ↔ x = y := by
  change v (x - y) = 0 ↔ x = y
  exact AbsoluteValue.map_sub_eq_zero_iff (abv := v) x y

/-- The absolute-value distance from a point to itself is zero. -/
@[simp]
theorem absoluteValueDist_self
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (x : K) :
    absoluteValueDist v x x = 0 := by
  simpa using (absoluteValueDist_eq_zero_iff v x x).mpr rfl















/-- Finite triangle inequality for a absolute values. -/
theorem absoluteValue_finset_sum_le
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    {ι : Type*} (s : Finset ι) (f : ι → K) :
    v (s.sum f) ≤ s.sum (fun i => v (f i)) := by
  classical
  refine Finset.induction_on s ?empty ?insert
  · simp
  · intro i s his ih
    rw [Finset.sum_insert his, Finset.sum_insert his]
    exact (v.add_le (f i) (s.sum f)).trans
      (by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left ih (v (f i)))

/-- The equivalence relation on absolute values: two absolute values are equivalent if they induce the
same topology. -/
def EquivalentAbsoluteValues {K : Type*} [Field K]
    (v w : AbsoluteValue K ℝ) : Prop :=
  IsHomeomorph (WithAbs.congr v w (.refl K))

/-- absolute-value equivalence is the same as mathlib's equivalence relation on real
absolute values. -/
theorem equivalentAbsoluteValues_iff_isEquiv
    {K : Type*} [Field K] (v w : AbsoluteValue K ℝ) :
    EquivalentAbsoluteValues v w ↔ v.IsEquiv w :=
  (AbsoluteValue.isEquiv_iff_isHomeomorph v w).symm

/-- Mathlib-equivalent absolute values are equivalent under the defining equivalence relation. -/
theorem equivalentAbsoluteValues_of_isEquiv
    {K : Type*} [Field K] {v w : AbsoluteValue K ℝ}
    (h : v.IsEquiv w) :
    EquivalentAbsoluteValues v w :=
  (equivalentAbsoluteValues_iff_isEquiv v w).mpr h



/-- absolute-value equivalence is reflexive. -/
theorem equivalentAbsoluteValues_refl
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    EquivalentAbsoluteValues v v :=
  equivalentAbsoluteValues_of_isEquiv (AbsoluteValue.IsEquiv.rfl (v := v))





/-- The power characterization of equivalent absolute values: two real absolute values are equivalent exactly when
one is a positive real power of the other. -/
theorem equivalentAbsoluteValues_iff_exists_rpow_eq
    {K : Type*} [Field K] (v w : AbsoluteValue K ℝ) :
    EquivalentAbsoluteValues v w ↔ ∃ s : ℝ, 0 < s ∧ (v · ^ s) = w := by
  exact
    (equivalentAbsoluteValues_iff_isEquiv v w).trans
      (AbsoluteValue.isEquiv_iff_exists_rpow_eq (v := v) (w := w))

















/-- The archimedean/nonarchimedean dichotomy: a valuation is nonarchimedean when its values on the
natural numbers are bounded. -/
def NonarchimedeanAbsoluteValue {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, v (n : K) ≤ C



/-- The strong triangle inequality appearing in the boundedness characterization of nonarchimedean absolute values. -/
def StrongTriangle {K : Type*} [Field K] (v : AbsoluteValue K ℝ) : Prop :=
  ∀ x y : K, v (x + y) ≤ max (v x) (v y)





/-- The boundedness characterization of nonarchimedean absolute values, strong triangle inequality as mathlib's
`IsNonarchimedean` predicate. -/
theorem strong_triangle_iff_isNonarchimedean
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    StrongTriangle v ↔ IsNonarchimedean (v : K → ℝ) :=
  Iff.rfl

/-- The easy direction of the boundedness characterization of nonarchimedean absolute values: the strong triangle inequality
bounds the values of the natural numbers by `1`. -/
theorem nat_le_one_of_strong_triangle
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hstrong : StrongTriangle v) (n : ℕ) :
    v (n : K) ≤ 1 := by
  exact ((strong_triangle_iff_isNonarchimedean v).mp hstrong).apply_natCast_le_one
    (by simp) (by simp)

/-- The easy direction of the boundedness characterization of nonarchimedean absolute values: a valuation satisfying the strong
triangle inequality is nonarchimedean in the boundedness-on-integers sense. -/
theorem nonarchimedean_of_strong_triangle
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hstrong : StrongTriangle v) :
    NonarchimedeanAbsoluteValue v :=
  ⟨1, nat_le_one_of_strong_triangle v hstrong⟩

/-- In the boundedness characterization of nonarchimedean absolute values, any bound for the values of the natural numbers is at
least `1`. -/
theorem nat_bound_ge_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) {C : ℝ}
    (hC : ∀ n : ℕ, v (n : K) ≤ C) :
    1 ≤ C := by
  simpa using hC 1

/-- The binomial-estimate step in the proof of the boundedness characterization of nonarchimedean absolute values: boundedness
of the values of natural numbers gives a polynomial factor in the estimate for
`(x + y)^n`. -/
theorem add_pow_le_of_bounded_nat
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) {C : ℝ}
    (hC : ∀ n : ℕ, v (n : K) ≤ C) (x y : K) (n : ℕ) :
    v ((x + y) ^ n) ≤
      ((n + 1 : ℕ) : ℝ) * C * (max (v x) (v y)) ^ n := by
  classical
  let M : ℝ := max (v x) (v y)
  have hC_nonneg : 0 ≤ C :=
    (zero_le_one : (0 : ℝ) ≤ 1).trans
      (nat_bound_ge_one v hC)
  have hM_nonneg : 0 ≤ M :=
    (v.nonneg x).trans (le_max_left (v x) (v y))
  have hsum_le :
      v ((Finset.range (n + 1)).sum
          (fun m => x ^ m * y ^ (n - m) * (n.choose m : K))) ≤
        (Finset.range (n + 1)).sum
          (fun m => v (x ^ m * y ^ (n - m) * (n.choose m : K))) :=
    absoluteValue_finset_sum_le v (Finset.range (n + 1))
      (fun m => x ^ m * y ^ (n - m) * (n.choose m : K))
  have hterm :
      ∀ m ∈ Finset.range (n + 1),
        v (x ^ m * y ^ (n - m) * (n.choose m : K)) ≤ C * M ^ n := by
    intro m hm
    have hmle : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hxpow : v (x ^ m) ≤ M ^ m := by
      rw [map_pow]
      exact pow_le_pow_left₀ (v.nonneg x) (le_max_left (v x) (v y)) m
    have hypow : v (y ^ (n - m)) ≤ M ^ (n - m) := by
      rw [map_pow]
      exact pow_le_pow_left₀ (v.nonneg y) (le_max_right (v x) (v y)) (n - m)
    have hxy :
        v (x ^ m) * v (y ^ (n - m)) ≤ M ^ m * M ^ (n - m) :=
      mul_le_mul hxpow hypow (v.nonneg (y ^ (n - m))) (pow_nonneg hM_nonneg m)
    have hchoose : v ((n.choose m : ℕ) : K) ≤ C := hC (n.choose m)
    calc
      v (x ^ m * y ^ (n - m) * (n.choose m : K))
          = v (x ^ m) * v (y ^ (n - m)) * v ((n.choose m : ℕ) : K) := by
              rw [map_mul, map_mul]
      _ ≤ (M ^ m * M ^ (n - m)) * C := by
              exact mul_le_mul hxy hchoose
                (v.nonneg ((n.choose m : ℕ) : K))
                (mul_nonneg (pow_nonneg hM_nonneg m)
                  (pow_nonneg hM_nonneg (n - m)))
      _ = C * M ^ n := by
              rw [← pow_add, Nat.add_sub_of_le hmle]
              ring
  calc
    v ((x + y) ^ n)
        = v ((Finset.range (n + 1)).sum
            (fun m => x ^ m * y ^ (n - m) * (n.choose m : K))) := by
            rw [add_pow]
    _ ≤ (Finset.range (n + 1)).sum
          (fun m => v (x ^ m * y ^ (n - m) * (n.choose m : K))) := hsum_le
    _ ≤ (Finset.range (n + 1)).sum (fun _m => C * M ^ n) :=
          Finset.sum_le_sum hterm
    _ = ((n + 1 : ℕ) : ℝ) * C * M ^ n := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-- The real-variable limit used at the end of the boundedness characterization of nonarchimedean absolute values: after taking
`n`-th roots, the polynomial factor `(n+1)C` disappears. -/
theorem tendsto_linear_bound_rpow_inv
    {C : ℝ} (hC : 0 < C) :
    Tendsto
      (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)))
      atTop (𝓝 1) := by
  have hCroot :
      Tendsto (fun n : ℕ => C ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
    have hcont : ContinuousAt (fun t : ℝ => C ^ t) 0 :=
      Real.continuousAt_const_rpow hC.ne'
    have hzero : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    change Tendsto
      ((fun t : ℝ => C ^ t) ∘ fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 1)
    simpa only [Real.rpow_zero] using hcont.tendsto.comp hzero
  have hshiftReal :
      Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / (1 * x + (-1)))) atTop (𝓝 1) :=
    tendsto_rpow_div_mul_add 1 1 (-1) zero_ne_one
  have hshiftNat :
      Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ ((n : ℝ)⁻¹)))
        atTop (𝓝 1) := by
    have hnatshift : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    refine (hshiftReal.comp hnatshift).congr' ?_
    exact Eventually.of_forall fun n => by
      simp [Nat.cast_add, Nat.cast_one, one_div, add_assoc]
  have htarget :
      Tendsto
        (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)))
        atTop (𝓝 (1 * 1)) := by
    refine (hshiftNat.mul hCroot).congr' ?_
    exact Eventually.of_forall fun n => by
      have hn_nonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
      have hmul :=
        (Real.mul_rpow (z := ((n : ℝ)⁻¹)) hn_nonneg (le_of_lt hC)).symm
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  simpa using htarget

/-- The root form of the binomial estimate in the boundedness characterization of nonarchimedean absolute values. -/
theorem add_le_root_bound_of_bounded_nat
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) {C : ℝ}
    (hC : ∀ n : ℕ, v (n : K) ≤ C) (x y : K)
    {n : ℕ} (hn : n ≠ 0) :
    v (x + y) ≤
      ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)) *
        max (v x) (v y) := by
  classical
  let M : ℝ := max (v x) (v y)
  have hC_pos : 0 < C :=
    zero_lt_one.trans_le (nat_bound_ge_one v hC)
  have hM_nonneg : 0 ≤ M :=
    (v.nonneg x).trans (le_max_left (v x) (v y))
  by_cases hMzero : M = 0
  · have hx_le_zero : v x ≤ 0 := by
      simpa [M, hMzero] using (le_max_left (v x) (v y))
    have hy_le_zero : v y ≤ 0 := by
      simpa [M, hMzero] using (le_max_right (v x) (v y))
    have hxzero : x = 0 := (v.eq_zero).mp (le_antisymm hx_le_zero (v.nonneg x))
    have hyzero : y = 0 := (v.eq_zero).mp (le_antisymm hy_le_zero (v.nonneg y))
    simp [hxzero, hyzero]
  · have hpow :
        (v (x + y)) ^ n ≤ ((n + 1 : ℕ) : ℝ) * C * M ^ n := by
      simpa [map_pow, M] using
        add_pow_le_of_bounded_nat v hC x y n
    have hright_nonneg :
        0 ≤ ((n + 1 : ℕ) : ℝ) * C * M ^ n := by
      exact mul_nonneg
        (mul_nonneg (by positivity) (le_of_lt hC_pos))
        (pow_nonneg hM_nonneg n)
    have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hroot :
        v (x + y) ≤
          (((n + 1 : ℕ) : ℝ) * C * M ^ n) ^ ((n : ℝ)⁻¹) := by
      rw [Real.le_rpow_inv_iff_of_pos (v.nonneg (x + y)) hright_nonneg hn_pos]
      simpa [Real.rpow_natCast] using hpow
    calc
      v (x + y)
          ≤ (((n + 1 : ℕ) : ℝ) * C * M ^ n) ^ ((n : ℝ)⁻¹) := hroot
      _ = ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)) * M := by
            have hcoef_nonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) * C :=
              mul_nonneg (by positivity) (le_of_lt hC_pos)
            rw [Real.mul_rpow hcoef_nonneg (pow_nonneg hM_nonneg n)]
            rw [Real.pow_rpow_inv_natCast hM_nonneg hn]
      _ = ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)) *
            max (v x) (v y) := by
            rfl

/-- The converse direction of the boundedness characterization of nonarchimedean absolute values: a bounded-on-integers
valuation satisfies the strong triangle inequality. -/
theorem strong_triangle_of_nonarchimedean
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : NonarchimedeanAbsoluteValue v) :
    StrongTriangle v := by
  rcases hnonarch with ⟨C, hC⟩
  have hC_pos : 0 < C :=
    zero_lt_one.trans_le (nat_bound_ge_one v hC)
  intro x y
  let M : ℝ := max (v x) (v y)
  have hlim :
      Tendsto
        (fun n : ℕ =>
          ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)) * M)
        atTop (𝓝 M) := by
    simpa using
      (tendsto_linear_bound_rpow_inv hC_pos).mul
        (tendsto_const_nhds (x := M))
  have heventually :
      ∀ᶠ n : ℕ in atTop,
        v (x + y) ≤
          ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)) * M := by
    refine eventually_atTop.2 ⟨1, ?_⟩
    intro n hn
    exact add_le_root_bound_of_bounded_nat
      (v := v) hC x y (n := n) (by omega)
  have hle :
      v (x + y) ≤ M :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim heventually
  simpa [M, StrongTriangle] using hle



/-- A consequence of the boundedness characterization: unequal values force equality in the strong triangle inequality. -/
theorem strong_triangle_eq_max_of_ne
    {K : Type*} [Field K] {v : AbsoluteValue K ℝ}
    (hstrong : StrongTriangle v)
    {x y : K} (hxy : v x ≠ v y) :
    v (x + y) = max (v x) (v y) := by
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · have hy_le : v y ≤ v (x + y) := by
      have hbase : v y ≤ max (v (x + y)) (v x) := by
        calc
          v y = v ((x + y) + -x) := by ring_nf
          _ ≤ max (v (x + y)) (v (-x)) := hstrong (x + y) (-x)
          _ = max (v (x + y)) (v x) := by rw [AbsoluteValue.map_neg]
      by_contra hnot
      exact (not_lt_of_ge hbase) (max_lt (lt_of_not_ge hnot) hlt)
    apply le_antisymm
    · simpa [max_eq_right (le_of_lt hlt)] using hstrong x y
    · simpa [max_eq_right (le_of_lt hlt)] using hy_le
  · have hx_le : v x ≤ v (x + y) := by
      have hbase : v x ≤ max (v (x + y)) (v y) := by
        calc
          v x = v ((x + y) + -y) := by ring_nf
          _ ≤ max (v (x + y)) (v (-y)) := hstrong (x + y) (-y)
          _ = max (v (x + y)) (v y) := by rw [AbsoluteValue.map_neg]
      by_contra hnot
      exact (not_lt_of_ge hbase) (max_lt (lt_of_not_ge hnot) hgt)
    apply le_antisymm
    · simpa [max_eq_left (le_of_lt hgt)] using hstrong x y
    · simpa [max_eq_left (le_of_lt hgt)] using hx_le



end Valuations
end LubinTate

end
