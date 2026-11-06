module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Tactic

/-!
# The exterior consequence of actual physical antiholomorphic moments

The moment identities produced by the driven boundary rows imply that the
actual exterior Cauchy transform vanishes outside a circle containing the
centered physical boundary.  A uniformly dominated geometric series justifies
the interchange of the interval integral and the sum.  The multiplier is the
actual `conj γ' * H`, with no Fourier-support premise or real-part replacement.

This is a genuine consequence of the physical moments, not the complete Jordan
Cauchy criterion.  Analytic continuation through the exterior and a boundary
jump/extension theorem are still needed to deduce Hardy support in supplied
conformal coordinates.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter
open scoped ComplexConjugate

/-- The physical antiholomorphic Cauchy transform, with ordinary parameter
measure and the actual differentiated boundary factor. -/
def physicalExteriorCauchy (γ H : ℝ → ℂ) (w : ℂ) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi),
    (conj (deriv γ θ) * H θ) / (conj w - conj (γ θ))

variable (γ H : ℝ → ℂ)

/-- All centered physical antiholomorphic moments force the exterior Cauchy
transform to vanish beyond any containing circle.  No Hardy support, Jordan
jump formula, or polynomial-approximation hypothesis is assumed. -/
theorem physicalExteriorCauchy_eq_zero_of_moments
    (hγ : ContDiff ℝ 1 γ) (hH : Continuous H)
    (hmom : ∀ m : ℕ,
      (∫ θ in 0..(2 * Real.pi),
        (conj (deriv γ θ) * H θ) * (conj (γ θ) - conj (γ 0)) ^ m) = 0)
    {R : ℝ} (hR : 0 ≤ R)
    (hbound : ∀ θ ∈ Icc 0 (2 * Real.pi), ‖γ θ - γ 0‖ ≤ R)
    {w : ℂ} (hw : R < ‖w - γ 0‖) :
    physicalExteriorCauchy γ H w = 0 := by
  let g  := fun θ => conj (deriv γ θ) * H θ
  let z  := fun θ => conj (γ θ) - conj (γ 0)
  let ξ  := conj w - conj (γ 0)
  have hg  :=
    (Complex.continuous_conj.comp hγ.continuous_deriv_one).mul hH
  have hξnorm : ‖ξ‖ = ‖w - γ 0‖ := by
    simp [ξ, ← map_sub]
  have hwξ : R < ‖ξ‖ := by linarith
  have hξpos  := lt_of_le_of_lt hR hwξ
  have hzbound (θ : ℝ) (hθ : θ ∈ Icc 0 (2 * Real.pi)) : ‖z θ‖ ≤ R := by
    simp_all [z, ← map_sub]
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
     hg.continuousOn
  have hM0  := (norm_nonneg (g 0)).trans
    (hM 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  let q  := R / ‖ξ‖
  have hq1  := (div_lt_one hξpos).mpr hwξ
  have hseries (θ : ℝ) (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
      HasSum (fun m  => (g θ / ξ) * (z θ / ξ) ^ m)
        (g θ / (conj w - conj (γ θ))) := by
    have hs := (hasSum_geometric_of_norm_lt_one (by
      rw [norm_div]
      exact lt_of_le_of_lt (div_le_div_of_nonneg_right (hzbound θ hθ) hξpos.le) hq1)).mul_left (g θ / ξ)
    grind
  have hi : HasSum (fun m  => ∫ θ in 0..(2 * Real.pi),
      (g θ / ξ) * (z θ / ξ) ^ m)
      (physicalExteriorCauchy γ H w) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun m _ => (M / ‖ξ‖) * q ^ m)
      (fun m => ((hg.div_const ξ).mul ((((Complex.continuous_conj.comp hγ.continuous).sub continuous_const).div_const ξ).pow m)).aestronglyMeasurable)
      (fun m => Eventually.of_forall fun θ hθ => ?_)
      (Eventually.of_forall fun _ _ => (summable_geometric_of_lt_one (div_nonneg hR hξpos.le) hq1).mul_left (M / ‖ξ‖)) intervalIntegrable_const
      (Eventually.of_forall fun θ hθ => ?_)
    · have hθ' : θ ∈ Icc 0 (2 * Real.pi) := by
        rw [uIoc_of_le Real.two_pi_pos.le] at hθ
        grind
      rw [norm_mul, norm_div, norm_pow, norm_div]
      dsimp only [q]
      gcongr
      · exact hM θ hθ'
      simp_all
    · exact hseries θ (by
        rw [uIoc_of_le Real.two_pi_pos.le] at hθ
        grind)
  have hint (m : ℕ) : (∫ θ in 0..(2 * Real.pi),
      (g θ / ξ) * (z θ / ξ) ^ m) = 0 := by
    have heq : (fun θ => (g θ / ξ) * (z θ / ξ) ^ m) =
        (fun θ => (ξ⁻¹ * (ξ⁻¹) ^ m) * (g θ * z θ ^ m)) := by
      funext θ
      ring
    rw [heq, intervalIntegral.integral_const_mul]
    rw [hmom, mul_zero]
  simpa only [hint, tsum_zero] using hi.tsum_eq.symm

/-- A containing radius exists for every actual C¹ boundary.  Thus the
physical moments give vanishing of the transform on a genuine neighborhood
of infinity, without supplying an extra boundedness premise. -/
theorem exists_radius_physicalExteriorCauchy_eq_zero_of_moments
    (hγ : ContDiff ℝ 1 γ) (hH : Continuous H)
    (hmom : ∀ m : ℕ,
      (∫ θ in 0..(2 * Real.pi),
        (conj (deriv γ θ) * H θ) * (conj (γ θ) - conj (γ 0)) ^ m) = 0) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ w : ℂ, R < ‖w - γ 0‖ →
      physicalExteriorCauchy γ H w = 0 := by
  have hc : Continuous (fun θ => γ θ - γ 0) := hγ.continuous.sub continuous_const
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
     hc.continuousOn
  have hR0 : 0 ≤ R := by
    simpa only [sub_self, norm_zero] using hR 0 ⟨le_rfl, Real.two_pi_pos.le⟩
  exact ⟨R, hR0, fun w hw =>
    physicalExteriorCauchy_eq_zero_of_moments γ H hγ hH hmom hR0 hR hw⟩

end PolyaNeumann

end
