module

public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Finite-sum squared `L²` seminorm estimate

This module records the finite Cauchy estimate for the squared real `L²`
seminorm of a finite sum.
-/

 public section



namespace HypoellipticAleksandrov.Analysis

open MeasureTheory
open scoped ENNReal

/-- The squared real `L²` seminorm of a finite sum is bounded by the number of
terms times the sum of the squared component seminorms. -/
theorem eLpNorm_sum_toReal_sq_le_card_mul
    {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {μ : Measure α} (f : ι → α → ℝ) (hf : ∀ i, MemLp (f i) 2 μ) :
    (ENNReal.toReal (eLpNorm (∑ i, f i) 2 μ)) ^ 2 ≤
      (Fintype.card ι : ℝ) *
        ∑ i, (ENNReal.toReal (eLpNorm (f i) 2 μ)) ^ 2 := by
  let sharedTerm_a27a24236e := ((eLpNorm (∑ i, f i) 2 μ))


  have hreal := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun i _ => (hf i).eLpNorm_ne_top) (by
      simpa only using (eLpNorm_sum_le (s := Finset.univ) (by norm_num : (1 : ℝ≥0∞) ≤ 2)))
  rw [ENNReal.toReal_sum (fun i (_hi : i ∈ Finset.univ) =>
    (hf i).eLpNorm_ne_top)] at hreal
  have hsum0 : 0 ≤ ∑ i, ENNReal.toReal (eLpNorm (f i) 2 μ) :=
    Finset.sum_nonneg fun i _ => ENNReal.toReal_nonneg
  calc
    (ENNReal.toReal sharedTerm_a27a24236e) ^ 2 ≤
        (∑ i, ENNReal.toReal (eLpNorm (f i) 2 μ)) ^ 2 := by
      nlinarith [ENNReal.toReal_nonneg (a := sharedTerm_a27a24236e)]
    _ ≤ (Fintype.card ι : ℝ) *
        ∑ i, (ENNReal.toReal (eLpNorm (f i) 2 μ)) ^ 2 := sq_sum_le_card_mul_sum_sq

end HypoellipticAleksandrov.Analysis
