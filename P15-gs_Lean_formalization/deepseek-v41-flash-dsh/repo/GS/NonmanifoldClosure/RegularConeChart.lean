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
public import GS.Nonmanifold.RankOneChart
public import GS.Nonmanifold.RankOneGeometry
public import GS.Nonmanifold.SkewCoordinates
public import GS.NonmanifoldClosure.ChartBalls
public import GS.NonmanifoldClosure.ChartRetractions
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
# A regular chart with free coordinates, and regular points arbitrarily near zero

The explicit pivot chart has dimension card(ι)+card(κ)+1. No dimension is
inferred from a redundant parametrization. One rank-one ray suffices to find
regular points in each open neighborhood of the vertex.
-/
noncomputable section
open Matrix GS GS.Nonmanifold GS.NonmanifoldObstruction GS.NonmanifoldFinal
open scoped Topology
namespace GS.NonmanifoldClosure

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

def scalarCoordinates : ℝ ≃ₜ (Fin 1 → ℝ) where
  toFun a _ := a
  invFun v := v 0
  left_inv a := rfl
  right_inv v := by funext j; fin_cases j; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

abbrev RegularCoordinates (ι κ : Type*) := (ι → ℝ) × ((κ → ℝ) × ℝ)

/-- This is a homeomorphism between coordinate conventions, not a norm identity. -/
def regularCoordinatesEuclidean : RegularCoordinates ι κ ≃ₜ
    Eucl (Fintype.card ι + Fintype.card κ + 1) := by
  let h₁ : RegularCoordinates ι κ ≃ₜ (ι → ℝ) × ((κ ⊕ Fin 1) → ℝ) :=
    (Homeomorph.refl _).prodCongr
      (((Homeomorph.refl _).prodCongr scalarCoordinates).trans sumCoordinates)
  let h₂ : RegularCoordinates ι κ ≃ₜ ((ι ⊕ (κ ⊕ Fin 1)) → ℝ) :=
    h₁.trans sumCoordinates
  have hcard : Fintype.card (ι ⊕ (κ ⊕ Fin 1)) =
      Fintype.card ι + Fintype.card κ + 1 := by simp [Nat.add_assoc]
  let e := (Fintype.equivFin (ι ⊕ (κ ⊕ Fin 1))).trans
    (Equiv.cast (congrArg Fin hcard))
  exact (h₂.trans (reindexReal e)).trans
    (EuclideanSpace.equiv (Fin (Fintype.card ι + Fintype.card κ + 1)) ℝ).symm.toHomeomorph

def pivotProductSource (j : κ) : Set (ConeSpace ι κ) := {p | p.2.val 0 j ≠ 0}
def pivotProductDomain (j : κ) : Set (RegularCoordinates ι κ) := {p | p.2.1 j ≠ 0}

theorem isOpen_pivotProductSource (j : κ) : IsOpen (pivotProductSource (ι := ι) j) := by
  change IsOpen ({p : ConeSpace ι κ | p.2.val 0 j = 0}ᶜ)
  have h : Continuous (fun p : ConeSpace ι κ => p.2.val 0 j) :=
    (continuous_apply j).comp ((continuous_apply 0).comp
      (continuous_subtype_val.comp continuous_snd))
  exact (isClosed_eq h continuous_const).isOpen_compl

theorem isOpen_pivotProductDomain (j : κ) : IsOpen (pivotProductDomain (ι := ι) j) := by
  change IsOpen ({p : RegularCoordinates ι κ | p.2.1 j = 0}ᶜ)
  exact (isClosed_eq (by fun_prop) continuous_const).isOpen_compl

/-- First flatten the pivot condition into the already constructed rank-one chart. -/
def pivotProductSplit (j : κ) : pivotProductSource (ι := ι) j ≃ₜ
    (ι → ℝ) × RankOnePivot j where
  toFun p := (p.val.1,⟨p.val.2.val,p.val.2.property,p.property⟩)
  invFun p := ⟨(p.1,⟨p.2.val,p.2.property.1⟩),p.2.property.2⟩
  left_inv p := rfl
  right_inv p := rfl
  continuous_toFun := by
    apply Continuous.prodMk
    · fun_prop
    · apply Continuous.subtype_mk
      exact continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact continuous_fst
    · apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_snd

def pivotCoordinateFlatten (j : κ) : ((ι → ℝ) × PivotCoordinates j) ≃ₜ
    pivotProductDomain (ι := ι) j where
  toFun p := ⟨(p.1,(p.2.1.val,p.2.2)),p.2.1.property⟩
  invFun p := (p.val.1,(⟨p.val.2.1,p.property⟩,p.val.2.2))
  left_inv p := rfl
  right_inv p := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_fst.prodMk
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp continuous_snd))
  continuous_invFun := by fun_prop

def pivotProductHomeomorph (j : κ) : pivotProductSource (ι := ι) j ≃ₜ
    pivotProductDomain (ι := ι) j :=
  ((pivotProductSplit j).trans
    ((Homeomorph.refl _).prodCongr (rankOnePivotHomeomorph j))).trans
    (pivotCoordinateFlatten j)

/-- Genuine open chart in the exact coordinate space ConeSpace. -/
def pivotProductChart (j : κ) : OpenEuclideanChart (ConeSpace ι κ)
    (Fintype.card ι + Fintype.card κ + 1) where
  source := pivotProductSource j
  target := regularCoordinatesEuclidean '' pivotProductDomain j
  source_open := isOpen_pivotProductSource j
  target_open := regularCoordinatesEuclidean.isOpenMap _ (isOpen_pivotProductDomain j)
  chart := (pivotProductHomeomorph j).trans
    (restrictImage regularCoordinatesEuclidean (pivotProductDomain j))

/-- An exact rank-one ray with the selected pivot equal to t. -/
def regularRay (j : κ) (t : ℝ) : ConeSpace ι κ :=
  (0,⟨outer ![t,0] (fun k => if k=j then 1 else 0),rank_outer_le_one _ _⟩)

theorem continuous_regularRay (j : κ) : Continuous (regularRay (ι := ι) j) := by
  apply Continuous.prodMk
  · exact continuous_const
  · apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    apply continuous_pi
    intro k
    by_cases hkj : k = j <;> fin_cases i <;> simp [regularRay, outer, hkj] <;> fun_prop

@[simp] theorem regularRay_zero (j : κ) : regularRay (ι := ι) j 0 = productZero := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    ext i k
    fin_cases i <;> simp [regularRay,productZero,coneZero,outer]

@[simp] theorem regularRay_pivot (j : κ) (t : ℝ) :
    (regularRay (ι := ι) j t).2.val 0 j = t := by simp [regularRay,outer]

/-- Every open vertex-neighborhood meets the regular pivot chart. -/
theorem exists_regular_in_open (j : κ) (U : Set (ConeSpace ι κ))
    (hU : IsOpen U) (hzero : productZero ∈ U) :
    ∃ p : ConeSpace ι κ, p ∈ U ∧ p ∈ (pivotProductChart (ι := ι) j).source := by
  have hopen : IsOpen (regularRay j ⁻¹' U) := hU.preimage (continuous_regularRay j)
  have hz : (0 : ℝ) ∈ regularRay j ⁻¹' U := by
    simpa only [Set.mem_preimage,regularRay_zero] using hzero
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hz)
  refine ⟨regularRay j (δ/2),hball ?_,?_⟩
  · rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (by linarith)]
    linarith
  · change (regularRay j (δ/2)).2.val 0 j ≠ 0
    rw [regularRay_pivot]
    linarith

end GS.NonmanifoldClosure
