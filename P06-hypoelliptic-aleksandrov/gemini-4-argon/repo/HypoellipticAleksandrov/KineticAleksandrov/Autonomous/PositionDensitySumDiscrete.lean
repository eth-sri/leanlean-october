module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumGrid

/-! # Summing the source overlap convolution on the two-index lattice -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory
open scoped ENNReal

/- Young's inequality in the source-index rather than displacement-index convention. -/
theorem position_two_index_young_source (w a : ℤ × ℤ → ℝ≥0∞) (q : ℝ) (hq : 1 < q) :
    (∑' g, (∑' h, w (g - h) * a h) ^ q) ≤
      (∑' h, w h) ^ q * ∑' g, a g ^ q := by
  have he (g : ℤ × ℤ) : (∑' h, w (g - h) * a h) =
      ∑' h, w h * a (g - h) := by
    have h := (Equiv.subLeft g).tsum_eq (fun h => w (g - h) * a h)
    simpa only [Equiv.subLeft_apply, sub_sub_cancel] using h.symm
  simp_rw [he]
  exact position_two_index_young w a q hq

/- The source overlap q-power sum is bounded by the starting-mass q-power sum. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
