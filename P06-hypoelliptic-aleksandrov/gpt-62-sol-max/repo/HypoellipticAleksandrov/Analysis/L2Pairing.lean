module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! # Linearity of the real L² pairing on representatives -/

@[expose] public section
namespace HypoellipticAleksandrov.Analysis
open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g φ : α → ℝ}

section
variable (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hφ : MemLp φ 2 μ)
include hf hg hφ

theorem integral_add_mul_L2 :
    (∫ z, (f z + g z) * φ z ∂μ) = (∫ z, f z * φ z ∂μ) + ∫ z, g z * φ z ∂μ := by
  simpa only [add_mul, Pi.mul_apply, Pi.add_apply] using
    integral_add (hf.integrable_mul hφ) (hg.integrable_mul hφ)

theorem integral_sub_mul_L2 :
    (∫ z, (f z - g z) * φ z ∂μ) = (∫ z, f z * φ z ∂μ) - ∫ z, g z * φ z ∂μ := by
  simpa only [sub_mul, Pi.mul_apply, Pi.sub_apply] using
    integral_sub (hf.integrable_mul hφ) (hg.integrable_mul hφ)

end

theorem integral_sum_mul_L2 {ι : Type*} [Fintype ι] {v : ι → α → ℝ}
    (hv : ∀ i, MemLp (v i) 2 μ) (hφ : MemLp φ 2 μ) :
    (∫ z, (∑ i, v i z) * φ z ∂μ) = ∑ i, ∫ z, v i z * φ z ∂μ := by
  simp_rw [Finset.sum_mul]
  exact integral_finsetSum _ fun i _ => (hv i).integrable_mul hφ

end HypoellipticAleksandrov.Analysis
