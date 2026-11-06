module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilationReflectionGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationReweight
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationHomogeneity
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureJets
import Mathlib.Analysis.Calculus.FDeriv.Add

/-! # Measure-level homogeneity and Radon properties under simultaneous reflection -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/- The pushforward homogeneity formula implies the source measurable-set density degree. -/
theorem bellman_densityDegree_of_map_dilation (β : ℝ) (μ )
    (hm : ∀ r : ℝ, ∀ hr : 0 < r, Measure.map (bellmanDilation r hr) μ =
      ENNReal.ofReal (r ^ (β - 4)) • μ) : HasBellmanDensityDegree β μ := by
  intro r hr E hE
  let D := bellmanDilationHomeomorph r hr
  have hi : MeasurableSet (D '' E) := D.measurableEmbedding.measurableSet_image.mpr hE
  have he := congrArg (fun ν : Measure BellmanPuncturedPlane => ν (D '' E)) (hm r hr)
  change (Measure.map D μ) (D '' E) = _ at he
  rw [Measure.map_apply D.measurable hi, D.injective.preimage_image,
    Measure.smul_apply, smul_eq_mul] at he
  have hc := bellmanRadial_degreeFactors_cancel β r hr
  calc
    μ (bellmanDilation r hr '' E) =
        (ENNReal.ofReal (r ^ (4 - β)) * ENNReal.ofReal (r ^ (β - 4))) * μ (D '' E) := by
      rw [mul_comm (ENNReal.ofReal (r ^ (4 - β))), hc, one_mul]
      rfl
    _ = ENNReal.ofReal (r ^ (4 - β)) * μ E := by rw [mul_assoc, ← he]

/- Simultaneous reflection preserves every source density degree. -/
theorem HasBellmanDensityDegree.reflect {β μ}
    (hμ : HasBellmanDensityDegree β μ) :
    HasBellmanDensityDegree β (Measure.map bellmanReflection μ) := by
  apply bellman_densityDegree_of_map_dilation
  intro r hr
  have he : bellmanDilation r hr ∘ bellmanReflection =
      bellmanReflection ∘ bellmanDilation r hr := by
    funext q
    have _h_xinl_0 : bellmanReflection (bellmanDilation r hr q) =
      bellmanDilation r hr (bellmanReflection q) := by
        apply Subtype.ext
        apply Prod.ext
        · change -(r ^ 3 * q.val.1) = r ^ 3 * (-q.val.1)
          ring
        · change -(r * q.val.2) = r * (-q.val.2)
          ring

      /- The first reflected test jet changes sign. -/
    exact _h_xinl_0.symm
  rw [Measure.map_map (measurable_bellmanDilation r hr) bellmanReflection.measurable,
    he, ← Measure.map_map bellmanReflection.measurable (measurable_bellmanDilation r hr),
    hμ.map_dilation r hr, Measure.map_smul _ bellmanReflection.measurable.aemeasurable]

/- Simultaneous reflection preserves the positive Radon property on the punctured plane. -/
theorem IsBellmanRadon.reflect {μ } (hμ : IsBellmanRadon μ) :
    IsBellmanRadon (Measure.map bellmanReflection μ) := by
  let : IsFiniteMeasureOnCompacts μ := hμ.1
  let : Measure.InnerRegular μ := hμ.2
  exact ⟨bellman_map_homeomorph_finiteOnCompacts bellmanReflection μ,
    Measure.InnerRegular.map bellmanReflection⟩

end HypoellipticAleksandrov.KineticAleksandrov
