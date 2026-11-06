module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilationReflectionMeasure
import Mathlib.Tactic
public import PDEFoundation.Calculus.RegularityOrder


/-! # Preservation of the stationary adjoint equation under simultaneous reflection -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory

/-- Simultaneous position–velocity reflection preserves the stationary adjoint equation. -/
theorem IsBellmanStationaryAdjointPair.reflect {μ η : Measure BellmanPuncturedPlane}
    (hpair : IsBellmanStationaryAdjointPair μ η) :
    IsBellmanStationaryAdjointPair (Measure.map bellmanReflection μ)
      (Measure.map bellmanReflection η) := by
  intro φ hφ hc hs
  let ψ := fun q  => φ (-q)



  have he := hpair ψ (hφ.comp contDiff_neg) (hc.comp_homeomorph (Homeomorph.neg (ℝ × ℝ))) (by
      intro q hq hzero

      apply (hs ((tsupport_comp_subset_preimage φ continuous_neg) hq))
      rw [hzero]
      simp)
  rw [bellmanReflection.measurableEmbedding.integral_map,
    bellmanReflection.measurableEmbedding.integral_map]
  have htransport : (fun q  =>
      (bellmanReflection q).val.2 * fderiv ℝ φ (bellmanReflection q).val (1, 0)) =
      (fun q => q.val.2 * fderiv ℝ ψ q.val (1, 0)) := by
    funext q
    change (-q.val.2) * fderiv ℝ φ (-q.val) (1, 0) =
      q.val.2 * fderiv ℝ (fun z => φ (-z)) q.val (1, 0)
    rw [bellman_reflected_fderiv φ hφ]
    ring
  have hvv : (fun q  =>
      fderiv ℝ (fun z => fderiv ℝ φ z (0, 1)) (bellmanReflection q).val (0, 1)) =
      (fun q => fderiv ℝ (fun z => fderiv ℝ ψ z (0, 1)) q.val (0, 1)) := by
    funext q
    exact (bellman_reflected_second_velocity φ hφ q.val).symm
  rw [htransport, hvv]
  exact he

/-- Reflection preserves the complete genuine homogeneous adjoint-pair condition. -/
theorem IsBellmanAdjointPair.reflect {R β : ℝ} {μ η : Measure BellmanPuncturedPlane}
    (hp : IsBellmanAdjointPair 1 R β μ η) :
    IsBellmanAdjointPair 1 R β (Measure.map bellmanReflection μ)
      (Measure.map bellmanReflection η) := by
  refine ⟨hp.1.reflect, hp.2.1.reflect, Or.inl ?_, ?_, ?_, hp.2.2.2.2.2.1.reflect,
    hp.2.2.2.2.2.2.1.reflect, hp.2.2.2.2.2.2.2.reflect⟩
  · intro he
    apply hp.left_ne_zero
    apply bellmanReflection.measurableEmbedding.map_injective
    simpa only [Measure.map_zero] using he
  · have he := Measure.map_mono hp.2.2.2.1 bellmanReflection.measurable
    rwa [Measure.map_smul _ bellmanReflection.measurable.aemeasurable] at he
  · have he := Measure.map_mono hp.2.2.2.2.1 bellmanReflection.measurable
    rwa [Measure.map_smul _ bellmanReflection.measurable.aemeasurable] at he

end HypoellipticAleksandrov.KineticAleksandrov
