module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationMeasure
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularCoordinates
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationFactorization
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationLogFactorization
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationRadialHaar
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationReweight
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Maps.Basic

/-! # Undoing the degree weight gives the literal source radial representation -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set
open Topology

/- Undoing the degree weight on ds/s gives exactly s^(3-β) ds. -/
theorem bellmanRadialDegreeWeight_inv (β : ℝ) (w : BellmanPositiveTime × ℝ) :
    (bellmanRadialDegreeWeight β w)⁻¹ = ENNReal.ofReal (w.1.val ^ (4 - β)) := by
  rw [bellmanRadialDegreeWeight,
    ← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos w.1.property _),
    ← Real.rpow_neg w.1.property.le]
  congr 1
  congr 1
  ring

/- The actual homogeneous coordinate measure is s^(3-β) ds times its actual angular measure. -/
theorem bellmanAngularMeasure_representation (β : ℝ)
    (μ : Measure BellmanPuncturedPlane) (hμ : IsFiniteMeasureOnCompacts μ)
    (hd : HasBellmanDensityDegree β μ) :
    μ.restrict {q | 0 < q.val.1} = bellmanAngularRep β (bellmanAngularMeasure β μ) := by
  have _h_inl_9 : bellmanAngularPullback μ =
      (bellmanRadialWeight β).prod (bellmanAngularMeasure β μ) := by
      let : IsFiniteMeasureOnCompacts (bellmanAngularMeasure β μ) :=
        bellmanAngularMeasure_finiteOnCompacts β μ hμ
      have hn : ∀ᵐ w ∂bellmanAngularPullback μ, bellmanRadialDegreeWeight β w ≠ 0 :=
        ae_of_all _ fun w => (ENNReal.ofReal_pos.mpr
          (Real.rpow_pos_of_pos w.1.property _)).ne'
      have ht : ∀ᵐ w ∂bellmanAngularPullback μ, bellmanRadialDegreeWeight β w ≠ ⊤ :=
        ae_of_all _ fun _ => ENNReal.ofReal_ne_top
      have _h_xinl_0 : (bellmanAngularPullback μ).withDensity (bellmanRadialDegreeWeight β) = bellmanRadialHaar.prod (bellmanAngularMeasure β μ) := by
        let : IsFiniteMeasureOnCompacts (bellmanAngularMeasure β μ) :=
          bellmanAngularMeasure_finiteOnCompacts β μ hμ
        apply bellmanLogAngularHomeomorph.measurableEmbedding.map_injective
        change bellmanLogAngularMeasure β μ = _
        change bellmanLogAngularMeasure β μ =
          Measure.map (Prod.map bellmanLogRadiusHomeomorph id)
            (bellmanRadialHaar.prod (bellmanAngularMeasure β μ))
        rw [← Measure.map_prod_map _ _ bellmanLogRadiusHomeomorph.measurable measurable_id,
          Measure.map_id]
        exact bellmanLogAngularMeasure_factorization_radial β μ hμ hd
      have he := congrArg (fun ρ : Measure (BellmanPositiveTime × ℝ) =>
        ρ.withDensity (fun w => (bellmanRadialDegreeWeight β w)⁻¹))
          _h_xinl_0
      rw [withDensity_inv_same (measurable_bellmanRadialDegreeWeight β) hn ht] at he
      have hw :=
        funext (bellmanRadialDegreeWeight_inv β)
      rw [hw] at he
      have hm : Measurable (fun s : BellmanPositiveTime =>
          ENNReal.ofReal (s.val ^ (4 - β))) := by fun_prop
      have _h_inl_7 (β) : bellmanRadialHaar.withDensity (fun s : BellmanPositiveTime => ENNReal.ofReal (s.val ^ (4 - β))) = bellmanRadialWeight β := by
        have h1 : Measurable (fun s : BellmanPositiveTime => ENNReal.ofReal s.val⁻¹) := by
          fun_prop
        have h2 : Measurable (fun s : BellmanPositiveTime =>
            ENNReal.ofReal (s.val ^ (4 - β))) := by fun_prop
        rw [bellmanRadialHaar, ← withDensity_mul _ h1 h2]
        unfold bellmanRadialWeight
        congr 1
        funext s
        change ENNReal.ofReal s.val⁻¹ * ENNReal.ofReal (s.val ^ (4 - β)) = _
        rw [← ENNReal.ofReal_mul (inv_nonneg.mpr s.property.le),
          ← Real.rpow_neg_one, ← Real.rpow_add s.property]
        congr 1
        congr 1
        ring
      rw [← prod_withDensity_left (μ := bellmanRadialHaar)
        (ν := bellmanAngularMeasure β μ) hm, _h_inl_7] at he
      exact he

    /- Mapping the proved product representation yields the exact positive-position restriction. -/
  rw [← map_bellmanAngularPullback μ, _h_inl_9]
  rfl

end HypoellipticAleksandrov.KineticAleksandrov
