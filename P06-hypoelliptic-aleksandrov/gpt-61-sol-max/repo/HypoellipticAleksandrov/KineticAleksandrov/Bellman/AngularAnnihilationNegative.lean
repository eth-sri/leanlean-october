module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilationNegativeMoments
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilationTailReflection
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularPositiveTailGrowth
import Mathlib.Tactic

/-! # Vanishing of negative angular moments and densities -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set Filter
open scoped Topology

/-- Finite tails force every negative first moment to vanish once the value and flux at zero
vanish. -/
theorem bellmanAngularFirstMoment_negative_zero (R β : ℝ) (hR : 1 ≤ R) (hβ : 3 ≤ β)
    (f h J : ℝ → ℝ) (hf : LocallyIntegrable f )
    (hn : ∀ᵐ z, 0 ≤ f z) (hcomp : ∀ᵐ y, h y ≤ R * f y)
    (h0 : h 0 = 0) (hj0 : J 0 = 0)
    (he : ∀ y : ℝ, h y = h 0 + J 0 * y - ((β - 2) / 3) * y *
      bellmanAngularFirstMoment f y + ((β - 3) / 3) * bellmanAngularSecondMoment f y)
    (htail : IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} ) :
    ∀ a : ℝ, a < 0 → bellmanAngularFirstMoment f a = 0 := by
  intro a ha

  by_contra hne


  let b := max 2 (-a)
  have hb : 2 ≤ b := le_max_left _ _

  apply bellmanAngularTail_not_power_lower_bound (fun y => f (-y)) β b
    (bellmanAngularFirstMoment f a / (3 * R)) (β - 3)
    (bellmanAngularTail_reflect β f htail) hb (div_pos (lt_of_le_of_ne (bellmanAngularFirstMoment_nonneg_negative hn ha.le) (Ne.symm hne)) (by positivity)) (by linarith)

  filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae (bellmanAngularComparison_reflect R f h hcomp)] with y hy hcy
  have hyp : 0 < y := by have : 2 < y := hb.trans_lt hy; linarith

  have hm := bellmanAngularFirstMoment_negative_mono hf hn (-y) a (by have := (le_max_right 2 (-a)).trans hy.le; linarith) ha.le
  have hl := bellmanAngularDensity_negative_lower β f h J hβ hf hn h0 hj0 he (-y)
    (by linarith)


  have hp : y * y ^ (β - 4) = y ^ (β - 3) := by
    calc
      y * y ^ (β - 4) = y ^ (1 : ℝ) * y ^ (β - 4) := by rw [Real.rpow_one]
      _ = y ^ (1 + (β - 4)) := (Real.rpow_add hyp _ _).symm
      _ = y ^ (β - 3) := by congr 1; ring
  calc
    (bellmanAngularFirstMoment f a / (3 * R)) * y ^ (β - 3) =
        ((bellmanAngularFirstMoment f a / (3 * R)) * y) * y ^ (β - 4) := by
      rw [mul_assoc, hp]
    _ ≤ _ := (mul_le_mul_of_nonneg_right (by
        have hm' := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ y / 3)
        simp only [neg_neg] at hl

        apply le_of_mul_le_mul_left (a := R) _ (by linarith)
        have heq : R * ((bellmanAngularFirstMoment f a / (3 * R)) * y) =
            (y / 3) * bellmanAngularFirstMoment f a := by field_simp
        rw [heq]
        exact (show (y / 3) * bellmanAngularFirstMoment f a ≤ h (-y) by
            exact hm'.trans hl).trans hcy) (Real.rpow_nonneg hyp.le (β - 4)))

/-- A vanishing first moment on the negative half-line forces its density to vanish there. -/
theorem bellmanAngularDensity_negative_zero (f : ℝ → ℝ)
    (hf : LocallyIntegrable f )
    (hz : ∀ y : ℝ, y < 0 → bellmanAngularFirstMoment f y = 0) :
    ∀ᵐ y ∂volume.restrict (Iio 0), f y = 0 := by


  filter_upwards [ae_restrict_of_ae (_root_.LocallyIntegrable.ae_hasDerivAt_integral (show LocallyIntegrable (fun z => z * f z) by
      simpa using bellman_polynomial_locallyIntegrable f hf 1)), ae_restrict_mem measurableSet_Iio] with y hdy hy

  have heder := (show bellmanAngularFirstMoment f =ᶠ[𝓝 y] (fun _ => 0) by
      filter_upwards [isOpen_Iio.mem_nhds hy] with z hz'
      exact hz z hz').deriv_eq
  rw [deriv_const] at heder
  have hder : deriv (bellmanAngularFirstMoment f) y = y * f y := (hdy 0).deriv
  rw [hder] at heder
  exact (mul_eq_zero.mp heder).resolve_left hy.ne

end HypoellipticAleksandrov.KineticAleksandrov
