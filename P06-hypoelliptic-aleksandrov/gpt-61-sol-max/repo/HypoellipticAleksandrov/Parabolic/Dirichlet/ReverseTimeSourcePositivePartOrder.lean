module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10PositivePart
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialForm

/-!
# Reverse-time source order on positive parts

This file records the source-sign inequality used in weak comparison.  The
order is reversed by the minus sign in the reverse-time source functional.
-/

 public section

open MeasureTheory
open scoped ENNReal



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The reverse-time source difference is nonpositive on the canonical
positive part when the second source is almost everywhere below the first. -/
theorem reverseTimeSourceFunctional_sub_nonpos_of_ae_le
    {d : ℕ} {Ω : PDE.VelocityRegion d}
    (hΩ : IsOpen Ω)
    (f₁ f₂ : PDE.ScalarLp Ω (2 ))
    (hf : ∀ᵐ y ∂PDE.volumeOn Ω, f₂ y ≤ f₁ y)
    (u : H10HilbertGraph hΩ) :
    reverseTimeSourceFunctional hΩ f₁ (h10PositivePart hΩ u) -
      reverseTimeSourceFunctional hΩ f₂ (h10PositivePart hΩ u) ≤ 0 := by


  rw [reverseTimeSourceFunctional_apply, reverseTimeSourceFunctional_apply,
    neg_sub_neg]
  exact sub_nonpos.mpr (by
      rw [L2.inner_def, L2.inner_def]
      apply integral_mono_ae (L2.integrable_inner _ _) (L2.integrable_inner _ _)
      filter_upwards [hf, (show ∀ᵐ y ∂PDE.volumeOn Ω,
        0 ≤ valueCLM hΩ (h10PositivePart hΩ u) y by
          rw [valueCLM_h10PositivePart]
          filter_upwards [Lp.coeFn_posPart (valueCLM hΩ u)] with y hy
          rw [hy]
          exact le_max_right _ _)] with y hyf hyv
      simp only [RCLike.inner_apply, conj_trivial]
      exact mul_le_mul_of_nonneg_right hyf hyv)

end HypoellipticAleksandrov.Parabolic.Dirichlet
