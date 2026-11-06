
import GS.NonmanifoldClosure.ChartBalls



/-!
# Sphere retractions supplied by an existing chart

Only subneighborhoods contained in the chart source are used. A local chart
cannot in general provide a retraction on an arbitrary larger neighborhood.
-/
open GS.NonmanifoldObstruction GS.NonmanifoldFinal
namespace GS.NonmanifoldClosure

variable {X : Type*} [TopologicalSpace X]

/-- Restrict a chart after removing the marked point, preserving its actual image. -/
def OpenEuclideanChart.punctured {n : ℕ} (c : OpenEuclideanChart X n)
    (x : X) (hx : x ∈ c.source) :
    PuncturedIn c.source x ≃ₜ PuncturedIn c.target (c.chart ⟨x,hx⟩).val where
  toFun p := ⟨(c.chart ⟨p.val,p.property.1⟩).val,
    (c.chart ⟨p.val,p.property.1⟩).property,by
      intro he
      exact p.property.2 (congrArg Subtype.val (c.chart.injective (Subtype.ext he)))⟩
  invFun z := ⟨(c.chart.symm ⟨z.val,z.property.1⟩).val,
    (c.chart.symm ⟨z.val,z.property.1⟩).property,by
      intro he
      apply z.property.2
      have hh : c.chart.symm ⟨z.val,z.property.1⟩ = ⟨x,hx⟩ := Subtype.ext he
      simpa only [c.chart.apply_symm_apply] using
        congrArg (fun a => (c.chart a).val) hh⟩
  left_inv p := by simp_all
  right_inv z := by simp_all
  continuous_toFun := (continuous_subtype_val.comp
    (c.chart.continuous.comp (continuous_subtype_val.subtype_mk _))).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp
    (c.chart.symm.continuous.comp (continuous_subtype_val.subtype_mk _))).subtype_mk _

/-- m is the ambient dimension of the sphere; the sphere itself has dimension m-1. -/
def SphereRetractionsOn (O : Set X) (x : X) (m : ℕ) : Prop :=
  ∀ U : Set X, IsOpen U → x ∈ U → U ⊆ O →
    Nonempty (ContinuousSectionPair (UnitSphere (Fin m)) (PuncturedIn U x))

/-- The property is derived from a chart, not postulated as a manifold axiom. -/
theorem OpenEuclideanChart.sphereRetractions {m : ℕ} (c : OpenEuclideanChart X m)
    (x : X) (hx : x ∈ c.source) : SphereRetractionsOn c.source x m := by
  intro U hU hxU hsub
  let d := c.restrict U hU
  have hxd : x ∈ d.source := ⟨hx,hxU⟩
  let y := (d.chart ⟨x,hxd⟩).val
  let r : GS.UnitaryTopology.IsolatedEuclideanRetract (Eucl m) y m := {
    sectionMap := fun z => y+z
    projectionMap := fun z => z-y
    section_continuous := by fun_prop
    projection_continuous := by fun_prop
    projection_section := by aesop
    section_zero := by simp
    projection_zero_iff := fun z => sub_eq_zero }
  obtain ⟨p⟩ := r.punctured_sphere d.target d.target_open (d.chart ⟨x,hxd⟩).property
  have he : PuncturedIn d.source x ≃ₜ PuncturedIn U x :=
    Homeomorph.setCongr (by
      ext z
      
      exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨hsub h.1,h.1⟩,h.2⟩⟩)
  exact ⟨transportSectionPair p (Homeomorph.refl _)
    ((d.punctured x hxd).symm.trans he)⟩

end GS.NonmanifoldClosure
