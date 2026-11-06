module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10PositivePart
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialForm

/-!
# Reverse-time source order on positive parts

This file records the source-sign inequality used in weak comparison.  The
order is reversed by the minus sign in the reverse-time source functional.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal RealInnerProductSpace


namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The reverse-time source difference is nonpositive on the canonical
positive part when the second source is almost everywhere below the first. -/
theorem reverseTimeSourceFunctional_sub_nonpos_of_ae_le
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω)
    (f₁ f₂ : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (hf : ∀ᵐ y ∂PDE.volumeOn Ω, f₂ y ≤ f₁ y)
    (u : H10HilbertGraph hΩ) :
    reverseTimeSourceFunctional hΩ f₁ (h10PositivePart hΩ u) -
      reverseTimeSourceFunctional hΩ f₂ (h10PositivePart hΩ u) ≤ 0 := by
  have hvalueNonneg :
      ∀ᵐ y ∂PDE.volumeOn Ω,
        0 ≤ valueCLM hΩ (h10PositivePart hΩ u) y := by
    rw [valueCLM_h10PositivePart]
    filter_upwards [Lp.coeFn_posPart (valueCLM hΩ u)] with y hy
    simp_all
  have hinner :
      inner ℝ (valueCLM hΩ (h10PositivePart hΩ u)) f₂ ≤
        inner ℝ (valueCLM hΩ (h10PositivePart hΩ u)) f₁ := by
    apply integral_mono_ae (L2.integrable_inner _ _) (L2.integrable_inner _ _)
    filter_upwards [hf, hvalueNonneg] with y hyf hyv
    exact mul_le_mul_of_nonneg_right hyf hyv
  rw [reverseTimeSourceFunctional_apply, reverseTimeSourceFunctional_apply]
  simp_all

end HypoellipticAleksandrov.Parabolic.Dirichlet
