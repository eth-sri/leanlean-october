import GS.Topology.SphereApproximationHomotopy
import GS.Topology.SectionPair
import GS.Topology.CompactParameter
import GS.Topology.EuclideanSphere
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
open GS.NonmanifoldObstruction GS.NonmanifoldFinal
namespace GS.UnitaryTopology
structure IsolatedEuclideanRetract (X : Type*) [TopologicalSpace X]
    (x₀ : X) (m : ℕ) where
  sectionMap : EuclideanSpace ℝ (Fin m) → X
  projectionMap : X → EuclideanSpace ℝ (Fin m)
  section_continuous : Continuous sectionMap
  projection_continuous : Continuous projectionMap
  projection_section : ∀ x, projectionMap (sectionMap x) = x
  section_zero : sectionMap 0 = x₀
  projection_zero_iff : ∀ x, projectionMap x = 0 ↔ x = x₀

variable {X : Type*} [TopologicalSpace X] {x₀ : X}

theorem IsolatedEuclideanRetract.punctured_sphere
    (r : IsolatedEuclideanRetract X x₀ m)
    (U : Set X) (hU : IsOpen U) (hx : x₀ ∈ U) :
    Nonempty (ContinuousSectionPair (UnitSphere (Fin m)) (PuncturedIn U x₀)) := by
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp
    (hU.preimage r.section_continuous) 0 (by simpa only [Set.mem_preimage, r.section_zero] using hx)
  let t := δ/2
  have ht : 0<t := by aesop
  have hnorm (v : UnitSphere (Fin m)) : ‖v.val‖ = 1 := by aesop
  have hmem (v : UnitSphere (Fin m)) : r.sectionMap (t • v.val) ∈ U := by aesop (add norm [abs_of_pos,norm_smul])
  let s : UnitSphere (Fin m) → PuncturedIn U x₀ := fun v =>
    ⟨r.sectionMap (t • v.val), hmem v, by
      intro he
      have hp := congrArg r.projectionMap he
      rw [r.projection_section, (r.projection_zero_iff x₀).mpr rfl] at hp
      have hn := congrArg norm hp
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht,hnorm v,mul_one,norm_zero] at hn
      exact (ne_of_gt ht) hn⟩
  have hne (p : PuncturedIn U x₀) : r.projectionMap p.val ≠ 0 :=
    fun he => p.property.2 ((r.projection_zero_iff p.val).mp he)
  let p : C(PuncturedIn U x₀, UnitSphere (Fin m)) :=
    GS.Topology.sphereNormalize
      ⟨fun x => r.projectionMap x.val, r.projection_continuous.comp continuous_subtype_val⟩ hne
  refine ⟨{
    sectionMap := s
    retractionMap := p
    section_continuous := ?_
    retraction_continuous := ?_
    retraction_section := ?_ }⟩
  · exact (r.section_continuous.comp
      (continuous_subtype_val.const_smul t)).subtype_mk _
  · exact p.continuous
  · intro v
    apply Subtype.ext
    change ‖r.projectionMap (r.sectionMap (t • v.val))‖⁻¹ •
      r.projectionMap (r.sectionMap (t • v.val)) = v.val
    rw [r.projection_section,norm_smul,Real.norm_eq_abs,abs_of_pos ht,
      hnorm v,mul_one,smul_smul,inv_mul_cancel₀ (ne_of_gt ht),one_smul]

end GS.UnitaryTopology
