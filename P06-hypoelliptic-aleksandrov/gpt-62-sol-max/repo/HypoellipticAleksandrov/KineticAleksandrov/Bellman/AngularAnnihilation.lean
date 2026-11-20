module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilationPositive
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilationNegative
import Mathlib.Tactic

/-! # Vanishing of both angular measures and the positive-position part -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

section
variable (R β : ℝ) (hR : 1 ≤ R) (hβ : 3 ≤ β)
include hR hβ

/-- At degree at least three every angular pair with actual densities and finite tails
vanishes. -/
theorem bellmanAngularMeasures_eq_zero
    {F H : Measure ℝ} {f h J : ℝ → ℝ} (hd : AngularDensityPair R β F H f h J)
    (htail : IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume) :
    F = 0 ∧ H = 0 := by
  obtain ⟨h0, hj0, hpos⟩ := angular_positive_vanishes R β hR hβ hd htail
  have hf := hd.first_locallyIntegrable
  have hn := hd.first_nonneg
  have hcomp := hd.upper_bound
  have hIneg := bellmanAngularFirstMoment_negative_zero R β hR hβ f h J hf hn
    hcomp h0 hj0 hd.integrated htail
  have hneg := bellmanAngularDensity_negative_zero f hf hIneg
  have hfn : ∀ᵐ y ∂volume, f y = 0 := by
    have hp := (ae_restrict_iff' measurableSet_Ioi).mp hpos
    have hm := (ae_restrict_iff' measurableSet_Iio).mp hneg
    have hne : ∀ᵐ y : ℝ ∂volume, y ≠ 0 := Measure.ae_ne volume 0
    filter_upwards [hp, hm, hne] with y hypos hyneg hyne
    rcases lt_or_gt_of_ne hyne with hy | hy
    · exact hyneg hy
    · exact hypos hy
  have hhn : ∀ᵐ y ∂volume, h y = 0 := by
    filter_upwards [hfn, hcomp] with y hy hc
    rw [hy, mul_zero] at hc
    exact le_antisymm hc (hd.second_nonneg y)
  have hzero (g : ℝ → ℝ) (hg : ∀ᵐ y ∂volume, g y = 0) :
      volume.withDensity (fun y => ENNReal.ofReal (g y)) = 0 := by
    simpa only [withDensity_zero] using (withDensity_congr_ae
      (μ := volume) (g := 0) (hg.mono fun y hy => by simp [hy]))
  rw [hd.first_measure, hd.second_measure, hzero f hfn, hzero h hhn]
  exact ⟨rfl, rfl⟩

/-- A homogeneous stationary pair of degree at least three has no mass on positive position. -/
theorem bellmanAdjointPair_positive_position_zero
    (μ η : Measure BellmanPuncturedPlane) (hp : IsBellmanAdjointPair 1 R β μ η) :
    μ {q | 0 < q.val.1} = 0 ∧ η {q | 0 < q.val.1} = 0 := by
  obtain ⟨F, H, f, h, J, hrep, hd, ht⟩ := exists_angular_densities_tail R β hR hβ μ η hp
  obtain ⟨hF, hH⟩ := bellmanAngularMeasures_eq_zero R β hR hβ hd ht
  have hμ : μ.restrict {q | 0 < q.val.1} = 0 := by
    rw [hrep.1, hF, bellmanAngularRep, Measure.prod_zero, Measure.map_zero]
  have hη : η.restrict {q | 0 < q.val.1} = 0 := by
    rw [hrep.2, hH, bellmanAngularRep, Measure.prod_zero, Measure.map_zero]
  constructor
  · simpa only [Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] using
      congrArg (fun ν : Measure BellmanPuncturedPlane => ν univ) hμ
  · simpa only [Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] using
      congrArg (fun ν : Measure BellmanPuncturedPlane => ν univ) hη

end

end HypoellipticAleksandrov.KineticAleksandrov
