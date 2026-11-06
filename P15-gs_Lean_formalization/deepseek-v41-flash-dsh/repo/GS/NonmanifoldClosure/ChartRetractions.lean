module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Real.Lemmas
public import GS.CompactFibres
public import GS.Continuation.CompactCoverageTools
public import GS.Continuation.ExponentialBasics
public import GS.Continuation.ExponentialChart
public import GS.Continuation.PointedCompactImage
public import GS.Core
public import GS.Extensions.FiniteTopology
public import GS.Extensions.MatrixCalculus
public import GS.Extensions.OrbitCompact
public import GS.Extensions.OriginalCompact
public import GS.Extensions.OriginalFibres
public import GS.Extensions.OriginalUniform
public import GS.Extensions.ProjectionSmooth
public import GS.Extensions.TransportedProjection
public import GS.Fibres
public import GS.Frobenius
public import GS.GeometryAlgebra
public import GS.GlobalGeometry.OriginalGImage
public import GS.M4Certificate
public import GS.M4Necessary
public import GS.M4Obstruction
public import GS.Nonmanifold.CircleRetract
public import GS.Nonmanifold.NormalizationEstimates
public import GS.Nonmanifold.OriginalCompactModel
public import GS.Nonmanifold.OriginalModelCoordinates
public import GS.Nonmanifold.RadialCone
public import GS.Nonmanifold.RankOneGeometry
public import GS.Nonmanifold.SkewCoordinates
public import GS.NonmanifoldClosure.ChartBalls
public import GS.NonmanifoldClosure.PuncturedBall
public import GS.NonmanifoldCompletion.BaseFibreGauges
public import GS.NonmanifoldCompletion.BlockExtraction
public import GS.NonmanifoldCompletion.BlockRealization
public import GS.NonmanifoldCompletion.FactorSpace
public import GS.NonmanifoldCompletion.FullFibreCoverage
public import GS.NonmanifoldCompletion.LocalAngles
public import GS.NonmanifoldCompletion.NeighbourhoodModel
public import GS.NonmanifoldCompletion.OriginalCoordinates
public import GS.NonmanifoldCompletion.OriginalMembership
public import GS.NonmanifoldCompletion.SmallLogarithms
public import GS.NonmanifoldCompletion.SpectralTwo
public import GS.NonmanifoldFinal.EuclideanTransport
public import GS.NonmanifoldFinal.FiniteCoordinates
public import GS.NonmanifoldFinal.RetractTransport
public import GS.NonmanifoldFinal.SphereCoordinates
public import GS.NonmanifoldObstruction.HomogeneousRetraction
public import GS.NonmanifoldObstruction.OpenGerms
public import GS.NonmanifoldObstruction.ProductSphere
public import GS.NonmanifoldObstruction.PuncturedNeighbourhood
public import GS.OriginalLocalModel
public import GS.Projection
public import GS.Shuffle
public import GS.Specifications
public import GS.ThreeFactor
public import GS.Topology.EuclideanSphere
public import GS.Topology.SectionPair


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

/-!
# Sphere retractions supplied by an existing chart

Only subneighborhoods contained in the chart source are used. A local chart
cannot in general provide a retraction on an arbitrary larger neighborhood.
-/
noncomputable section
open GS.NonmanifoldObstruction GS.NonmanifoldFinal
open scoped Topology
namespace GS.NonmanifoldClosure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every punctured open neighborhood in a real normed space contains a small
sphere with an explicit left inverse. -/
theorem normSphere_retract_open (U : Set E) (hU : IsOpen U) (y : E) (hy : y ∈ U) :
    Nonempty (ContinuousSectionPair (NormSphere E) (PuncturedIn U y)) := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hy)
  let t := r / 2
  have ht : 0 < t := by dsimp [t]; linarith
  have htr : t < r := by dsimp [t]; linarith
  let s : NormSphere E → PuncturedIn U y := fun v =>
    ⟨y+t • v.val, hball (by
      rw [Metric.mem_ball, dist_eq_norm]
      have hsub : y+t • v.val-y = t • v.val := by abel
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos ht,v.property,mul_one]
      exact htr),by
        intro he
        have hz : t • v.val = 0 := by simpa using congrArg (fun z => z-y) he
        have hn := congrArg norm hz
        rw [norm_smul, Real.norm_eq_abs,abs_of_pos ht,v.property,mul_one,norm_zero] at hn
        linarith⟩
  have hne (p : PuncturedIn U y) : p.val-y ≠ 0 :=
    sub_ne_zero.mpr p.property.2
  let rmap : PuncturedIn U y → NormSphere E := fun p =>
    ⟨‖p.val-y‖⁻¹ • (p.val-y),by
      have hp := norm_pos_iff.mpr (hne p)
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp),
        inv_mul_cancel₀ (ne_of_gt hp)]⟩
  refine ⟨{ sectionMap := s
            retractionMap := rmap
            section_continuous := ?_
            retraction_continuous := ?_
            retraction_section := ?_ }⟩
  · exact (continuous_const.add (continuous_const.smul continuous_subtype_val)).subtype_mk _
  · apply Continuous.subtype_mk
    exact (((continuous_subtype_val.sub continuous_const).norm).inv₀
      (fun p => norm_ne_zero_iff.mpr (hne p))).smul
        (continuous_subtype_val.sub continuous_const)
  · intro v
    apply Subtype.ext
    change ‖y+t • v.val-y‖⁻¹ • (y+t • v.val-y)=v.val
    have hh : y+t • v.val-y=t • v.val := by abel
    rw [hh,norm_smul,Real.norm_eq_abs,abs_of_pos ht,v.property,mul_one,
      smul_smul,inv_mul_cancel₀ (ne_of_gt ht),one_smul]

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
  left_inv p := by
    apply Subtype.ext
    exact congrArg (fun a : c.source => a.val)
      (c.chart.symm_apply_apply ⟨p.val,p.property.1⟩)
  right_inv z := by
    apply Subtype.ext
    exact congrArg (fun a : c.target => a.val)
      (c.chart.apply_symm_apply ⟨z.val,z.property.1⟩)
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
  let y : Eucl m := (d.chart ⟨x,hxd⟩).val
  obtain ⟨p⟩ := normSphere_retract_open d.target d.target_open y
    (d.chart ⟨x,hxd⟩).property
  have he : PuncturedIn d.source x ≃ₜ PuncturedIn U x :=
    Homeomorph.setCongr (by
      ext z
      change ((z ∈ c.source ∧ z ∈ U) ∧ z ≠ x) ↔ (z ∈ U ∧ z ≠ x)
      exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨hsub h.1,h.1⟩,h.2⟩⟩)
  exact ⟨transportSectionPair p (normSphereStandard m).symm
    ((d.punctured x hxd).symm.trans he)⟩

end GS.NonmanifoldClosure
