module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDensities
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularPositiveTailLimitCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilationOrigin
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

/-! # Vanishing of the actual angular densities on the positive half-line -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set Filter
open scoped Topology

/-- At degree at least three, finite tails force the positive angular density and origin flux
to vanish. -/
theorem angular_positive_vanishes (R β : ℝ) (hR : 1 ≤ R) (hβ : 3 ≤ β)
    {F H : Measure ℝ} {f h J : ℝ → ℝ} (hd : AngularDensityPair R β F H f h J)
    (htail : IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume) :
    h 0 = 0 ∧ J 0 = 0 ∧ (∀ᵐ y ∂volume.restrict (Ioi 0), f y = 0) := by
  have hf := hd.first_locallyIntegrable
  have hn := hd.first_nonneg
  have hh := hd.second_nonneg
  have hcomp := hd.upper_bound
  have he := hd.integrated
  obtain ⟨L, _, hI, _, hj, hlower⟩ :=
    bellmanAngularPositiveTail_limit R β hR hβ f h J hf hn hh hcomp he htail
  have h0 := bellmanAngularDensity_zero_at_origin R β hR hβ f h (hh 0) hcomp hlower htail
  have hj0 := bellmanAngularFlux_zero_at_origin β f h J hf hn hh h0 he
  have hL0 : L = 0 := by
    have hc : 0 < (β - 2) / 3 := by linarith
    rw [hj0] at hj
    nlinarith
  have hi := bellmanAngularFirstMoment_integrable β f h J hβ hf hn hh he
  have htotal : (∫ z in Ioi 0, z * f z) = 0 := by
    have heq := tendsto_nhds_unique hI (bellmanAngularFirstMoment_tendsto f hi)
    linarith
  have hzn : ∀ᵐ z ∂volume.restrict (Ioi 0), 0 ≤ z * f z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hn] with z hz hnz
    exact mul_nonneg hz.le hnz
  have hz := (integral_eq_zero_iff_of_nonneg_ae hzn hi).mp htotal
  refine ⟨h0, hj0, ?_⟩
  filter_upwards [hz, ae_restrict_mem measurableSet_Ioi] with z hz hpos
  exact (mul_eq_zero.mp hz).resolve_left hpos.ne'

end HypoellipticAleksandrov.KineticAleksandrov
