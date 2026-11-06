module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.LocalWeakTimeProduct

section
open private HypoellipticAleksandrov.Parabolic.toReal_eLpNorm_mul_le from HypoellipticAleksandrov.Parabolic.LocalWeakTimeProduct
private alias _sharedProof_126_2 := HypoellipticAleksandrov.Parabolic.toReal_eLpNorm_mul_le
end


/-!
# Bounded measurable scalar multiplier on `Lᵖ`

This module records the generic `Lᵖ` membership and real-valued seminorm estimate for
multiplication by an almost-everywhere bounded measurable scalar function.
-/

 public section



namespace HypoellipticAleksandrov.Analysis

open MeasureTheory
open scoped ENNReal

/-- Multiplication by an almost-everywhere bounded measurable scalar preserves
`Lᵖ` and obeys the corresponding real-valued seminorm estimate. -/
theorem memLp_mul_eLpNorm_toReal_le_of_ae_abs_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} {a f : α → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (ha : AEStronglyMeasurable a μ)
    (hf : MemLp f p μ) (haM : ∀ᵐ x ∂μ, |a x| ≤ M) :
    MemLp (fun x => a x * f x) p μ ∧
      ENNReal.toReal (eLpNorm (fun x => a x * f x) p μ) ≤
        M * ENNReal.toReal (eLpNorm f p μ) := (_sharedProof_126_2 hM ha hf haM)


end HypoellipticAleksandrov.Analysis
