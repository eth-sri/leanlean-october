module
import Mathlib
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

open Complex Finset
open scoped BigOperators

namespace GuthMaynard.NativeMoment

lemma sum_sq_le_card_mul_sum_sq {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
  (∑ i ∈ s, f i)^2 ≤ (s.card : ℝ) * ∑ i ∈ s, (f i)^2 := by
  have h_CS := Finset.sum_mul_sq_le_sq_mul_sq s f (fun _ => 1)
  simp_all <;> nlinarith

lemma complex_sum_sq_le_card_mul_sum_sq {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
  ‖∑ i ∈ s, f i‖^2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖^2 := by
  have h1 : ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le s f
  have h2 : 0 ≤ ‖∑ i ∈ s, f i‖ := norm_nonneg _
  have h3 : 0 ≤ ∑ i ∈ s, ‖f i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have h4 : ‖∑ i ∈ s, f i‖^2 ≤ (∑ i ∈ s, ‖f i‖)^2 := by
    nlinarith [h1, h2, h3]
  have h5 := sum_sq_le_card_mul_sum_sq s (fun i => ‖f i‖)
  exact le_trans h4 h5


