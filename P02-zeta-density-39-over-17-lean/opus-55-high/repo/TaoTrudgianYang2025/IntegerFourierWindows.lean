module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.IntegerFourierTails
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# Exact symmetric-window decomposition around an integer core

The exterior blocks are the literal integer intervals. The reversed
left enumeration and forward right enumeration each include every
frequency once and retain the nearest exterior integer.
-/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

section
variable (f : ℤ → ℂ)
include f
theorem sum_int_interval_three_parts
    {a b c d : ℤ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    (∑ q ∈ Finset.Icc a d, f q) =
      (∑ q ∈ Finset.Ico a b, f q)+(∑ q ∈ Finset.Icc b c, f q)+
        ∑ q ∈ Finset.Ioc c d, f q := by
  have hs : Finset.Icc a d =
      (Finset.Ico a b ∪ Finset.Icc b c) ∪ Finset.Ioc c d := by
    pm_187 q Finset.mem_Icc Finset.mem_Ico Finset.mem_Ioc Finset.mem_union
    omega
  have hd₁ : Disjoint (Finset.Ico a b) (Finset.Icc b c) := by
    rw [Finset.disjoint_left]
    intro q hq hq'
    simp only [Finset.mem_Ico,Finset.mem_Icc] at hq hq'
    omega
  have hd₂ : Disjoint (Finset.Ico a b ∪ Finset.Icc b c) (Finset.Ioc c d) := by
    rw [Finset.disjoint_left]
    intro q hq hq'
    simp only [Finset.mem_union,Finset.mem_Ico,Finset.mem_Icc,Finset.mem_Ioc] at hq hq'
    omega
  rw [hs,Finset.sum_union hd₂,Finset.sum_union hd₁]

theorem sum_int_Ico_eq_reverse_range {a b : ℤ} (hab : a ≤ b) :
    (∑ q ∈ Finset.Ico a b, f q) =
      ∑ n ∈ Finset.range (b-a).toNat, f (b-((n+1 : ℕ) : ℤ)) := by
  pm_1247
  apply Finset.sum_bij (fun n _ => b-((n+1 : ℕ) : ℤ))
  grind
  grind
  · intro q hq
    pm_294 Finset.mem_Ico b q
    grind
    grind
  grind

theorem sum_int_Ioc_eq_forward_range {a b : ℤ} (hab : a ≤ b) :
    (∑ q ∈ Finset.Ioc a b, f q) =
      ∑ n ∈ Finset.range (b-a).toNat, f (a+((n+1 : ℕ) : ℤ)) := by
  pm_1247
  pm_6381 a
  grind
  grind
  · intro q hq
    pm_294 Finset.mem_Ioc q a
    · simp only [Finset.mem_range]
      omega
    grind
  grind
end

end TaoTrudgianYang2025
