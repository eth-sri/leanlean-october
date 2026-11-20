module
public import ValuedFieldTheory.Valuation.AbsoluteValue.Nonarchimedean

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

section

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ)

/-- The distance attached by the absolute-value construction to an absolute value. -/
def absoluteValueDist (x y : K) : ℝ :=
  v (x - y)

/-- The absolute-value distance separates points. -/
theorem absoluteValueDist_eq_zero_iff (x y : K) :
    absoluteValueDist v x y = 0 ↔ x = y := by
  exact AbsoluteValue.map_sub_eq_zero_iff v x y

/-- The absolute-value distance from a point to itself is zero. -/
@[simp]
theorem absoluteValueDist_self (x : K) :
    absoluteValueDist v x x = 0 := by
  exact (absoluteValueDist_eq_zero_iff v x x).mpr rfl

end

/-- Finite triangle inequality for a absolute values. -/
alias absoluteValue_finset_sum_le := AbsoluteValue.Nonarchimedean.finset_sum_le

section

variable {K : Type*} [Field K]

/-- The equivalence relation on absolute values: two absolute values are equivalent if they induce the
same topology. -/
def EquivalentAbsoluteValues
    (v w : AbsoluteValue K ℝ) : Prop :=
  IsHomeomorph (WithAbs.congr v w (.refl K))

/-- absolute-value equivalence is the same as mathlib's equivalence relation on real
absolute values. -/
theorem equivalentAbsoluteValues_iff_isEquiv (v w : AbsoluteValue K ℝ) :
    EquivalentAbsoluteValues v w ↔ v.IsEquiv w :=
  (AbsoluteValue.isEquiv_iff_isHomeomorph v w).symm

/-- Mathlib-equivalent absolute values are equivalent under the defining equivalence relation. -/
theorem equivalentAbsoluteValues_of_isEquiv {v w : AbsoluteValue K ℝ}
    (h : v.IsEquiv w) :
    EquivalentAbsoluteValues v w :=
  (equivalentAbsoluteValues_iff_isEquiv v w).mpr h

/-- absolute-value equivalence is reflexive. -/
theorem equivalentAbsoluteValues_refl (v : AbsoluteValue K ℝ) :
    EquivalentAbsoluteValues v v :=
  equivalentAbsoluteValues_of_isEquiv (AbsoluteValue.IsEquiv.rfl (v := v))

/-- The power characterization of equivalent absolute values: two real absolute values are equivalent exactly when
one is a positive real power of the other. -/
theorem equivalentAbsoluteValues_iff_exists_rpow_eq (v w : AbsoluteValue K ℝ) :
    EquivalentAbsoluteValues v w ↔ ∃ s : ℝ, 0 < s ∧ (v · ^ s) = w := (equivalentAbsoluteValues_iff_isEquiv v w).trans
      (AbsoluteValue.isEquiv_iff_exists_rpow_eq)

/-- The archimedean/nonarchimedean dichotomy: a valuation is nonarchimedean when its values on the
natural numbers are bounded. -/
def NonarchimedeanAbsoluteValue
    (v : AbsoluteValue K ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, v (n : K) ≤ C

end

/-- The strong triangle inequality appearing in the boundedness characterization of nonarchimedean absolute values. -/
def StrongTriangle {K : Type*} [Field K] (v : AbsoluteValue K ℝ) : Prop :=
  ∀ x y : K, v (x + y) ≤ max (v x) (v y)

section

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ)

/-- The boundedness characterization of nonarchimedean absolute values, strong triangle inequality as mathlib's
`IsNonarchimedean` predicate. -/
theorem strong_triangle_iff_isNonarchimedean :
    StrongTriangle v ↔ IsNonarchimedean (v : K → ℝ) :=
  Iff.rfl

/-- The easy direction of the boundedness characterization of nonarchimedean absolute values: the strong triangle inequality
bounds the values of the natural numbers by `1`. -/
theorem nat_le_one_of_strong_triangle
    (hstrong : StrongTriangle v) (n : ℕ) :
    v (n : K) ≤ 1 := ((strong_triangle_iff_isNonarchimedean v).mp hstrong).apply_natCast_le_one
    (by simp) (by simp)

end

/-- The easy direction of the boundedness characterization of nonarchimedean absolute values: a valuation satisfying the strong
triangle inequality is nonarchimedean in the boundedness-on-integers sense. -/
theorem nonarchimedean_of_strong_triangle
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hstrong : StrongTriangle v) :
    NonarchimedeanAbsoluteValue v :=
  ⟨1, nat_le_one_of_strong_triangle v hstrong⟩

/-- In the boundedness characterization of nonarchimedean absolute values, any bound for the values of the natural numbers is at
least `1`. -/
alias nat_bound_ge_one := AbsoluteValue.Nonarchimedean.nat_bound_ge_one

/-- The binomial-estimate step in the proof of the boundedness characterization of nonarchimedean absolute values: boundedness
of the values of natural numbers gives a polynomial factor in the estimate for
`(x + y)^n`. -/
alias add_pow_le_of_bounded_nat := AbsoluteValue.Nonarchimedean.add_pow_le_of_bounded_nat

/-- The real-variable limit used at the end of the boundedness characterization of nonarchimedean absolute values: after taking
`n`-th roots, the polynomial factor `(n+1)C` disappears. -/
alias tendsto_linear_bound_rpow_inv := AbsoluteValue.Nonarchimedean.tendsto_linear_bound_rpow_inv

/-- The root form of the binomial estimate in the boundedness characterization of nonarchimedean absolute values. -/
alias add_le_root_bound_of_bounded_nat := AbsoluteValue.Nonarchimedean.add_le_root_bound_of_bounded_nat

/-- The converse direction of the boundedness characterization of nonarchimedean absolute values: a bounded-on-integers
valuation satisfies the strong triangle inequality. -/
theorem strong_triangle_of_nonarchimedean
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : NonarchimedeanAbsoluteValue v) :
    StrongTriangle v := by
  rcases hnonarch with ⟨C, hC⟩
  intro x y
  let M := max (v x) (v y)
  have hlim :
      Tendsto
        (fun n : ℕ =>
          ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)) * M)
        atTop (𝓝 M) := by
    simpa using
      (tendsto_linear_bound_rpow_inv (zero_lt_one.trans_le (nat_bound_ge_one v hC))).mul
        (tendsto_const_nhds)
  have heventually :
      ∀ᶠ n : ℕ in atTop,
        v (x + y) ≤
          ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)) * M := by
    refine eventually_atTop.2 ⟨1, ?_⟩
    intro n hn
    exact add_le_root_bound_of_bounded_nat
      (v := v) hC x y (n := n) (by omega)
  exact (le_of_tendsto_of_tendsto tendsto_const_nhds hlim heventually)

end Valuations
end LubinTate

end
