module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilationPositive
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilationNegative
import Mathlib.Tactic

/-! # Vanishing of both angular measures and the positive-position part -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

variable (R β : ℝ) (hR : 1 ≤ R) (hβ : 3 ≤ β)
include hR hβ

/-- At degree at least three every angular pair with actual densities and finite tails
vanishes. -/
theorem bellmanAngularMeasures_eq_zero
    (F H : Measure ℝ) (f h J : ℝ → ℝ)
    (hd :
    F = volume.withDensity (fun y => ENNReal.ofReal (f y)) ∧
    H = volume.withDensity (fun y => ENNReal.ofReal (h y)) ∧
    LocallyIntegrable f volume ∧ (∀ᵐ y ∂volume, 0 ≤ f y) ∧
    (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval h a b) ∧
    (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval J a b) ∧
    (∀ᵐ y ∂volume, f y ≤ h y ∧ h y ≤ R * f y) ∧
    (∀ᵐ y ∂volume, deriv h y = J y - y ^ 2 * f y / 3) ∧
    (∀ᵐ y ∂volume, deriv J y = -(β - 2) / 3 * y * f y))
    (he : ∀ y : ℝ, h y = h 0 + J 0 * y - ((β - 2) / 3) * y *
      bellmanAngularFirstMoment f y + ((β - 3) / 3) * bellmanAngularSecondMoment f y)
    (htail : IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume) :
    F = 0 ∧ H = 0 := by
  obtain ⟨h0, hj0, hpos, _⟩ := angular_positive_vanishes R β hR hβ F H f h J hd he htail
  have hf := hd.2.2.1
  have hn := hd.2.2.2.1
  have hcomp := hd.2.2.2.2.2.2.1.mono (fun _ hx => hx.2)
  have hneg := bellmanAngularDensity_negative_zero f hf (bellmanAngularFirstMoment_negative_zero R β hR hβ f h J hf hn hcomp h0 hj0 he htail)
  have hfn : ∀ᵐ y ∂volume, f y = 0 := by
    filter_upwards [((ae_restrict_iff' measurableSet_Ioi).mp hpos), ((ae_restrict_iff' measurableSet_Iio).mp hneg), (Measure.ae_ne volume 0)] with y hypos hyneg hyne
    grind
  have hhn : ∀ᵐ y ∂volume, h y = 0 := by
    filter_upwards [hfn, hcomp] with y hy hc
    rw [hy, mul_zero] at hc
    exact le_antisymm hc ((bellmanAngularDensity_nonneg hd.2.2.2.2.1 hn (hd.2.2.2.2.2.2.1.mono (fun _ hx => hx.1))) y)
  constructor
  · rw [hd.1]
    calc
      _ = volume.withDensity (fun _ => 0) := by
        apply withDensity_congr_ae
        filter_upwards [hfn] with y hy
        rw [hy, ENNReal.ofReal_zero]
      _ = 0 := withDensity_zero
  · rw [hd.2.1]
    calc
      _ = volume.withDensity (fun _ => 0) := by
        apply withDensity_congr_ae
        filter_upwards [hhn] with y hy
        rw [hy, ENNReal.ofReal_zero]
      _ = 0 := withDensity_zero

/-- A homogeneous stationary pair of degree at least three has no mass on positive position. -/
theorem bellmanAdjointPair_positive_position_zero
    (μ η : Measure BellmanPuncturedPlane) (hp : IsBellmanAdjointPair 1 R β μ η) :
    μ {q | 0 < q.val.1} = 0 ∧ η {q | 0 < q.val.1} = 0 := by
  obtain ⟨F, H, f, h, J, hrep, hd, ht⟩ := exists_angular_densities_tail R β hR hβ μ η hp
  obtain ⟨hF, hH⟩ := bellmanAngularMeasures_eq_zero R β hR hβ F H f h J hd (angular_integrated R β F H f h J hd) ht
  have hμ : μ.restrict {q | 0 < q.val.1} = 0 := by
    rw [hrep.1, hF, bellmanAngularRep, Measure.prod_zero, Measure.map_zero]
  have hη : η.restrict {q | 0 < q.val.1} = 0 := by
    grind
  constructor
  · simpa using
      congrArg (fun ν : Measure BellmanPuncturedPlane => ν univ) hμ
  · simpa using
      congrArg (fun ν : Measure BellmanPuncturedPlane => ν univ) hη

end HypoellipticAleksandrov.KineticAleksandrov
