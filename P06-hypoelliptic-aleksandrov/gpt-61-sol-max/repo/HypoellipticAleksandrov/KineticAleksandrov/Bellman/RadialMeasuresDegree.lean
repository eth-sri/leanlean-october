module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RadialMeasuresScaling
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.ExponentSetting
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueAdjointLimitDegree
import Mathlib.Tactic

/-! # The radial constructions have the exact adjoint density degree two plus alpha -/

 public section

open MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Scaling only the radius transforms the product by its literal radial factor. -/
theorem bellman_radial_product_scale {lam Lam : ℝ} (alpha r : ℝ) (hr : 0 < r)
    (pi : Measure (BellmanSphere × BellmanCoefficient lam Lam)) [IsFiniteMeasure pi] :
    Measure.map ((bellmanRadialScale r hr).prodCongr (Homeomorph.refl
      (BellmanSphere × BellmanCoefficient lam Lam)))
      ((bellmanRadiusMeasure alpha).prod pi) =
      ENNReal.ofReal (r ^ (alpha - 2)) • ((bellmanRadiusMeasure alpha).prod pi) := by
  change Measure.map (Prod.map (bellmanRadialScale r hr) id) _ = _
  rw [← Measure.map_prod_map _ _ (bellmanRadialScale r hr).measurable measurable_id,
    Measure.map_id, map_bellmanRadiusMeasure_radialScale, Measure.prod_smul_left]

variable {lam Lam : ℝ}

/-- The coefficient-weighted product has the same radial scaling factor. -/
theorem bellman_radial_weighted_product_scale  (alpha r : ℝ) (hr : 0 < r)
    (pi : Measure (BellmanSphere × BellmanCoefficient lam Lam)) [IsFiniteMeasure pi] :
    Measure.map ((bellmanRadialScale r hr).prodCongr (Homeomorph.refl
      (BellmanSphere × BellmanCoefficient lam Lam)))
      (((bellmanRadiusMeasure alpha).prod pi).withDensity
        (fun w => ENNReal.ofReal w.2.2.val)) =
      ENNReal.ofReal (r ^ (alpha - 2)) •
        (((bellmanRadiusMeasure alpha).prod pi).withDensity
          (fun w => ENNReal.ofReal w.2.2.val)) := by

  rw [bellman_map_withDensity _ _ _ (by
      fun_prop), bellman_radial_product_scale,
    withDensity_smul_measure]
  rfl

/-- Dilation of the projected point equals scaling its radius before projection. -/
theorem bellman_radial_projection_commute  (r : ℝ) (hr : 0 < r) :
    bellmanDilation r hr ∘ (sphereRadialPoint (lam := lam) (Lam := Lam)) =
      sphereRadialPoint ∘ ((bellmanRadialScale r hr).prodCongr
        (Homeomorph.refl (BellmanSphere × BellmanCoefficient lam Lam))) := by
  funext w
  apply Subtype.ext
  exact bellmanPlaneDilation_comp r w.1.val w.2.1.val

variable (alpha : ℝ) (pi : Measure (BellmanSphere × BellmanCoefficient lam Lam))

/-- The first radial measure has degree two plus alpha in the source convention. -/
theorem radialMu_densityDegree   [IsFiniteMeasure pi] :
    HasBellmanDensityDegree (2 + alpha) (radialMu alpha pi) := by
  apply bellman_degree_of_map_dilation
  intro r hr
  unfold radialMu
  have hf := (continuous_sphereRadialPoint lam Lam).measurable
  have hd := (bellmanDilationHomeomorph r hr).measurable
  change Measurable (bellmanDilation r hr) at hd
  rw [Measure.map_map hd hf,
    bellman_radial_projection_commute,
    ← Measure.map_map hf ((bellmanRadialScale r hr).prodCongr
      (Homeomorph.refl (BellmanSphere × BellmanCoefficient lam Lam))).measurable,
    bellman_radial_product_scale, Measure.map_smul _ hf.aemeasurable]
  have he : 2 + alpha - 4 = alpha - 2 := by ring
  rw [he]

/-- The second radial measure has the same degree despite its diffusion coefficient weight. -/
theorem radialEta_densityDegree   [IsFiniteMeasure pi] :
    HasBellmanDensityDegree (2 + alpha) (radialEta alpha pi) := by
  apply bellman_degree_of_map_dilation
  intro r hr
  unfold radialEta
  have hf := (continuous_sphereRadialPoint lam Lam).measurable
  have hd := (bellmanDilationHomeomorph r hr).measurable
  change Measurable (bellmanDilation r hr) at hd
  rw [Measure.map_map hd hf,
    bellman_radial_projection_commute,
    ← Measure.map_map hf ((bellmanRadialScale r hr).prodCongr
      (Homeomorph.refl (BellmanSphere × BellmanCoefficient lam Lam))).measurable,
    bellman_radial_weighted_product_scale, Measure.map_smul _ hf.aemeasurable]
  have he : 2 + alpha - 4 = alpha - 2 := by ring
  rw [he]

end HypoellipticAleksandrov.KineticAleksandrov
