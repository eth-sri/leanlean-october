module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularTailDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquation

/-! # Compatible angular representations, densities and tail estimates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- A genuine homogeneous pair produces compatible angular measures, densities and finite
tails. -/
theorem exists_angular_densities_tail (R β : ℝ) (hR : 1 ≤ R) (hβ : 3 ≤ β)
    (μ η : Measure BellmanPuncturedPlane) (hp : IsBellmanAdjointPair 1 R β μ η) :
    ∃ (F H : Measure ℝ) (f h J : ℝ → ℝ),
      (μ.restrict {q | 0 < q.val.1} = bellmanAngularRep β F ∧
        η.restrict {q | 0 < q.val.1} = bellmanAngularRep β H) ∧
      AngularDensityPair R β F H f h J ∧
      IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume := by
  obtain ⟨F, H, hrep, hang⟩ := exists_angular_adjoint R β hR hβ μ η hp
  obtain ⟨f, h, J, hd⟩ := angular_has_densities R β hR F H hang
  let : IsFiniteMeasureOnCompacts μ := hp.1.1
  let : IsFiniteMeasureOnCompacts F := hang.1
  exact ⟨F, H, f, h, J, hrep, hd,
    bellmanAngularDensity_tail β μ F hrep.1 f hd.first_measure hd.first_locallyIntegrable hd.first_nonneg⟩

end HypoellipticAleksandrov.KineticAleksandrov
