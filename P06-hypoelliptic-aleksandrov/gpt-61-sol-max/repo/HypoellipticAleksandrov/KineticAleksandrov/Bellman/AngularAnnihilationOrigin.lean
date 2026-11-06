module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularPositiveTailGrowth
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilationMoments
import Mathlib.Tactic

/-! # Vanishing angular value and flux at the origin -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set Filter
open scoped Topology

/-- A nonnegative angular density bounded below by its value at zero must vanish there. -/
theorem bellmanAngularDensity_zero_at_origin (R β : ℝ) (hR : 1 ≤ R) (hβ : 3 ≤ β)
    (f h : ℝ → ℝ) (hh : 0 ≤ h 0)
    (hcomp : ∀ᵐ y, h y ≤ R * f y)
    (hlower : ∀ y : ℝ, 0 < y → h 0 ≤ h y)
    (htail : IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} ) :
    h 0 = 0 := by
  by_contra hn

  have hRp : 0 < R := by linarith
  apply bellmanAngularTail_not_power_lower_bound f β 2 (h 0 / R) (β - 4)
    htail le_rfl (div_pos (lt_of_le_of_ne hh (Ne.symm hn)) hRp) (by linarith)
  filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hcomp] with y hy hc


  exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hRp).mpr (by simpa only [mul_comm] using (hlower y (by have : 2 < y := hy; linarith)).trans hc)) (Real.rpow_nonneg (by have : 2 < y := hy; linarith) _)

section
variable (f : ℝ → ℝ) (hf : LocallyIntegrable f volume)

include hf
/-- The first moment tends to zero at the angular origin. -/
theorem bellmanAngularFirstMoment_tendsto_zero  :
    Tendsto (bellmanAngularFirstMoment f) (𝓝 (0 )) (𝓝 0) := by

  have hc := bellman_lebesguePrimitive_continuous _ (by
      simpa using bellman_polynomial_locallyIntegrable f hf 1)
  change Tendsto (fun y => ∫ z in 0..y, z * f z) (𝓝 (0 )) (𝓝 0)
  simpa only [intervalIntegral.integral_same] using hc.tendsto (0 )

/-- The normalized second moment tends to zero at the origin without pointwise regularity of
f. -/
theorem bellmanAngularSecondMoment_div_tendsto_zero  (hn : ∀ᵐ z, 0 ≤ f z) :
    Tendsto (fun y => bellmanAngularSecondMoment f y / y) (𝓝 (0 )) (𝓝 0) := by
  apply squeeze_zero_norm
    (fun y => bellmanAngularSecondMoment_div_norm_le hf hn y)
    (bellmanAngularFirstMoment_tendsto_zero f hf)
end


/-- Nonnegativity on both sides and the integrated identity force the flux at zero to vanish. -/
theorem bellmanAngularFlux_zero_at_origin (β : ℝ) (f h J : ℝ → ℝ)
    (hf : LocallyIntegrable f ) (hn : ∀ᵐ z, 0 ≤ f z)
    (hh : ∀ y : ℝ, 0 ≤ h y) (h0 : h 0 = 0)
    (he : ∀ y : ℝ, h y = h 0 + J 0 * y - ((β - 2) / 3) * y *
      bellmanAngularFirstMoment f y + ((β - 3) / 3) * bellmanAngularSecondMoment f y) :
    J 0 = 0 := by


  have ht : Tendsto (fun y => J 0 - ((β - 2) / 3) * bellmanAngularFirstMoment f y +
      ((β - 3) / 3) * (bellmanAngularSecondMoment f y / y)) (𝓝 (0 )) (𝓝 (J 0)) := by
    simpa only [mul_zero, sub_zero, add_zero] using
      (tendsto_const_nhds.sub ((bellmanAngularFirstMoment_tendsto_zero f hf).const_mul ((β - 2) / 3))).add
        ((bellmanAngularSecondMoment_div_tendsto_zero f hf hn).const_mul ((β - 3) / 3))
  have heq (y : ℝ) (hy : y ≠ 0) : h y / y =
      J 0 - ((β - 2) / 3) * bellmanAngularFirstMoment f y +
        ((β - 3) / 3) * (bellmanAngularSecondMoment f y / y) := by
    rw [he y, h0]
    field_simp
    ring


  exact le_antisymm (by
      apply le_of_tendsto (ht.mono_left (nhdsWithin_le_nhds (s := Iio (0 : ℝ))))
      filter_upwards [self_mem_nhdsWithin] with y hy
      rw [← heq y hy.ne]
      exact div_nonpos_of_nonneg_of_nonpos (hh y) hy.le) (by
      apply ge_of_tendsto (ht.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
      filter_upwards [self_mem_nhdsWithin] with y hy
      rw [← heq y hy.ne']
      exact div_nonneg (hh y) hy.le)

end HypoellipticAleksandrov.KineticAleksandrov
