module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Finset
open scoped BigOperators

namespace GuthMaynard.NativeMoment

lemma pigeonhole_real_sum (n : ℕ) (a : ℕ → ℝ) (S : ℝ) (hS : S ≤ ∑ i ∈ range n, a i) (hn : 0 < n) :
  ∃ i ∈ range n, S / n ≤ a i := by
  by_contra h
  push Not at h
  have h_sum : ∑ i ∈ range n, a i < ∑ i ∈ range n, (S / n) := by
    apply Finset.sum_lt_sum
    grind
    aesop
  have h_sum_eq : ∑ i ∈ range n, (S / n) = S := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    pm_300 hn_real n
    grind
  rw [h_sum_eq] at h_sum
  linarith
end GuthMaynard.NativeMoment
