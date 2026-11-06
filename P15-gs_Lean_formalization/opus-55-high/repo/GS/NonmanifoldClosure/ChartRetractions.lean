module

public import GS.NonmanifoldClosure.ChartBalls

@[expose] public section



/-!
# Sphere retractions supplied by an existing chart

Only subneighborhoods contained in the chart source are used. A local chart
cannot in general provide a retraction on an arbitrary larger neighborhood.
-/
noncomputable section
open GS.NonmanifoldObstruction GS.NonmanifoldFinal
namespace GS.NonmanifoldClosure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every punctured open neighborhood in a real normed space contains a small
sphere with an explicit left inverse. -/
theorem normSphere_retract_open (U : Set E) (hU : IsOpen U) (y : E) (hy : y ∈ U) :
    Nonempty (ContinuousSectionPair (NormSphere E) (PuncturedIn U y)) := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hy)
  have hne (p : PuncturedIn U y) : ‖p.val-y‖ ≠ 0 := by simpa [sub_eq_zero] using p.property.2
  refine ⟨⟨fun v => ⟨y+(r/2) • v.val, hball (by simp [dist_eq_norm, norm_smul, v.property, abs_of_pos hr]; linarith),
    by aesop⟩, fun p => ⟨‖p.val-y‖⁻¹ • (p.val-y), by simp [norm_smul, hne]⟩, by fun_prop,
    by fun_prop (disch := exact hne _), fun v => Subtype.ext ?_⟩⟩
  simp [norm_smul, v.property, abs_of_pos hr, smul_smul, hr.ne']

variable {X : Type*} [TopologicalSpace X]

/-- Restrict a chart after removing the marked point, preserving its actual image. -/
def OpenEuclideanChart.punctured {n : ℕ} (c : OpenEuclideanChart X n)
    (x : X) (hx : x ∈ c.source) :
    PuncturedIn c.source x ≃ₜ PuncturedIn c.target (c.chart ⟨x,hx⟩).val where
  toFun p := ⟨(c.chart ⟨p.val,p.property.1⟩).val,
    (c.chart _).property, fun he => p.property.2 (congrArg Subtype.val (c.chart.injective (Subtype.ext he)))⟩
  invFun z := ⟨(c.chart.symm ⟨z.val,z.property.1⟩).val, (c.chart.symm _).property, fun he => z.property.2 (by
    simpa using congrArg (c.chart · |>.val) (Subtype.ext he : _ = (⟨x,hx⟩ : c.source)))⟩
  left_inv p := by simp
  right_inv z := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- m is the ambient dimension of the sphere; the sphere itself has dimension m-1. -/
def SphereRetractionsOn (O : Set X) (x : X) (m : ℕ) : Prop :=
  ∀ U : Set X, IsOpen U → x ∈ U → U ⊆ O →
    Nonempty (ContinuousSectionPair (UnitSphere (Fin m)) (PuncturedIn U x))

/-- The property is derived from a chart, not postulated as a manifold axiom. -/
theorem OpenEuclideanChart.sphereRetractions {m : ℕ} (c : OpenEuclideanChart X m)
    (x : X) (hx : x ∈ c.source) : SphereRetractionsOn c.source x m := by
  intro U hU hxU hsub
  have hxd : x ∈ (c.restrict U hU).source := ⟨hx,hxU⟩
  obtain ⟨p⟩ := normSphere_retract_open _ (c.restrict U hU).target_open _ ((c.restrict U hU).chart ⟨x,hxd⟩).property
  exact ⟨transportSectionPair p (normSphereStandard m).symm
    ((OpenEuclideanChart.punctured _ x hxd).symm.trans (Homeomorph.setCongr (by
      ext z
      change ((z ∈ c.source ∧ z ∈ U) ∧ z ≠ x) ↔ (z ∈ U ∧ z ≠ x)
      grind)))⟩

end GS.NonmanifoldClosure
