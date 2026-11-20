module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ActiveTerminalDominationPoint
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripKernelIntegral

/-! # Integrating and telescoping stopped kernel inequalities -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory

/-- Integrating two actual kernel actions preserves their pointwise sum inequality. -/
theorem enlarged_integral_kernel_pair_le
    (K L : Kernel Point Point) (mu : Measure Point) [IsFiniteMeasure mu]
    (f g : Point → ℝ) (hK : Integrable f (K ∘ₘ mu)) (hL : Integrable f (L ∘ₘ mu))
    (hg : Integrable g mu)
    (hstep : ∀ᵐ p ∂mu, (∫ q, f q ∂K p) + (∫ q, f q ∂L p) ≤ g p) :
    (∫ q, f q ∂K ∘ₘ mu) + (∫ q, f q ∂L ∘ₘ mu) ≤ ∫ p, g p ∂mu := by
  rw [integral_measure_comp hK, integral_measure_comp hL,
    ← integral_add (integrable_integral_measure_comp hK) (integrable_integral_measure_comp hL)]
  exact integral_mono_ae ((integrable_integral_measure_comp hK).add
    (integrable_integral_measure_comp hL)) hg hstep

/-- Integrating one actual kernel action preserves a pointwise bound. -/
theorem enlarged_integral_kernel_le
    (K : Kernel Point Point) (mu : Measure Point) [IsFiniteMeasure mu]
    (f g : Point → ℝ) (hK : Integrable f (K ∘ₘ mu)) (hg : Integrable g mu)
    (hstep : ∀ᵐ p ∂mu, (∫ q, f q ∂K p) ≤ g p) :
    (∫ q, f q ∂K ∘ₘ mu) ≤ ∫ p, g p ∂mu := by
  rw [integral_measure_comp hK]
  exact integral_mono_ae (integrable_integral_measure_comp hK) hg hstep

/-- Finite nonnegative terminal spends telescope through successive active and waiting values. -/
theorem enlarged_terminal_values_telescope (U R D : ℕ → ℝ)
    (hU : ∀ n, 0 ≤ U n) (ha : ∀ n, D n + R n ≤ U n)
    (hw : ∀ n, U (n + 1) ≤ R n) (N : ℕ) :
    (∑ n ∈ Finset.range N, D n) ≤ U 0 := by
  have hh : ∀ N, (∑ n ∈ Finset.range N, D n) + U N ≤ U 0 := by
    intro N
    induction N with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, zero_add, le_refl]
    | succ N ih =>
      rw [Finset.sum_range_succ]
      linarith [ha N, hw N]
  linarith [hh N, hU N]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
