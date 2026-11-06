module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Trace
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
public import GS.ComplexAlgebra
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
public import GS.Unitary.CholeskySupport
public import GS.Unitary.Factorization
public import GS.Unitary.GeometryAlgebra
public import GS.Unitary.OrdinaryQR
public import GS.Unitary.Permutations
public import GS.Unitary.StructuredQR
public import GS.Unitary.Support
public import GS.UnitaryLocalModel.OuterFibres
public import GS.UnitaryLocalModel.PauliCoordinates
public import GS.UnitaryLocalModel.RankCone
public import GS.UnitaryNonmanifold.BlockInvariant
public import GS.UnitaryNonmanifold.ScalarBridge
public import GS.UnitaryTopology.QuaternionRetraction


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Genuine regular pivot charts of the three-row real rank-one cone,
including arbitrary Euclidean factors and regular points near the vertex. -/
noncomputable section
open Matrix GS GS.UnitaryLocalModel GS.NonmanifoldObstruction GS.NonmanifoldFinal
  GS.NonmanifoldClosure
open scoped Topology
namespace GS.UnitaryTopology
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

abbrev RankThreePivot (j : κ) :=
  {W : Matrix (Fin 3) κ ℝ // W.rank ≤ 1 ∧ W 0 j ≠ 0}
abbrev PivotCoordinates3 (j : κ) := {x : κ → ℝ // x j ≠ 0} × (Fin 2 → ℝ)

def pivotEncode3 (j : κ) (W : RankThreePivot j) : PivotCoordinates3 j :=
  (⟨W.val 0,W.property.2⟩,![W.val 1 j / W.val 0 j,W.val 2 j / W.val 0 j])
def pivotDecode3 (j : κ) (p : PivotCoordinates3 j) : RankThreePivot j :=
  ⟨sphereOuter ![1,p.2 0,p.2 1] p.1.val,rank_sphereOuter_le_one _ _,by
    simpa [sphereOuter] using p.1.property⟩

theorem pivotDecode_encode3 (j : κ) (W : RankThreePivot j) :
    pivotDecode3 j (pivotEncode3 j W) = W := by
  apply Subtype.ext
  ext i k
  fin_cases i
  · simp [pivotDecode3,pivotEncode3,sphereOuter]
  · have hm := rank_le_one_minor W.val W.property.1 0 1 j k
    change (W.val 1 j / W.val 0 j) * W.val 0 k = W.val 1 k
    field_simp [W.property.2]
    nlinarith [hm]
  · have hm := rank_le_one_minor W.val W.property.1 0 2 j k
    change (W.val 2 j / W.val 0 j) * W.val 0 k = W.val 2 k
    field_simp [W.property.2]
    nlinarith [hm]

theorem pivotEncode_decode3 (j : κ) (p : PivotCoordinates3 j) :
    pivotEncode3 j (pivotDecode3 j p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    funext k
    simp [pivotDecode3,pivotEncode3,sphereOuter]
  · funext i
    fin_cases i <;> simp [pivotEncode3,pivotDecode3,sphereOuter,p.1.property]

omit [DecidableEq κ] in
theorem continuous_pivotEncode3 (j : κ) : Continuous (pivotEncode3 j) := by
  unfold pivotEncode3
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    exact (continuous_apply 0).comp continuous_subtype_val
  · apply continuous_pi
    intro i
    have h₀ : Continuous (fun W : RankThreePivot j => W.val 0 j) :=
      (continuous_apply j).comp ((continuous_apply 0).comp continuous_subtype_val)
    have h₁ (r : Fin 3) : Continuous (fun W : RankThreePivot j => W.val r j) :=
      (continuous_apply j).comp ((continuous_apply r).comp continuous_subtype_val)
    fin_cases i
    · exact (h₁ 1).div h₀ (fun W => W.property.2)
    · exact (h₁ 2).div h₀ (fun W => W.property.2)

theorem continuous_pivotDecode3 (j : κ) : Continuous (pivotDecode3 j) := by
  unfold pivotDecode3
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro k
  have hx : Continuous (fun p : PivotCoordinates3 j => p.1.val k) :=
    (continuous_apply k).comp (continuous_subtype_val.comp continuous_fst)
  fin_cases i <;> simp [sphereOuter]
  · exact hx
  · exact ((continuous_apply 0).comp continuous_snd).mul hx
  · exact ((continuous_apply 1).comp continuous_snd).mul hx

def rankThreePivotHomeomorph (j : κ) : RankThreePivot j ≃ₜ PivotCoordinates3 j where
  toFun := pivotEncode3 j
  invFun := pivotDecode3 j
  left_inv := pivotDecode_encode3 j
  right_inv := pivotEncode_decode3 j
  continuous_toFun := continuous_pivotEncode3 j
  continuous_invFun := continuous_pivotDecode3 j

def productZero3 : (ι → ℝ) × RankThreeCone κ := (0,rankThreeZero)

abbrev RegularCoordinates3 (ι κ : Type*) := (ι → ℝ) × ((κ → ℝ) × (Fin 2 → ℝ))

/-- This is a homeomorphism between coordinate conventions, not a norm identity. -/
def regularCoordinatesEuclidean3 : RegularCoordinates3 ι κ ≃ₜ
    Eucl (Fintype.card ι + Fintype.card κ + 2) := by
  let h₁ : RegularCoordinates3 ι κ ≃ₜ (ι → ℝ) × ((κ ⊕ Fin 2) → ℝ) :=
    (Homeomorph.refl _).prodCongr
      sumCoordinates
  let h₂ : RegularCoordinates3 ι κ ≃ₜ ((ι ⊕ (κ ⊕ Fin 2)) → ℝ) :=
    h₁.trans sumCoordinates
  have hcard : Fintype.card (ι ⊕ (κ ⊕ Fin 2)) =
      Fintype.card ι + Fintype.card κ + 2 := by simp [Nat.add_assoc]
  let e := (Fintype.equivFin (ι ⊕ (κ ⊕ Fin 2))).trans
    (Equiv.cast (congrArg Fin hcard))
  exact (h₂.trans (reindexReal e)).trans
    (EuclideanSpace.equiv (Fin (Fintype.card ι + Fintype.card κ + 2)) ℝ).symm.toHomeomorph

def pivotProductSource3 (j : κ) : Set (((ι → ℝ) × RankThreeCone κ)) := {p | p.2.val 0 j ≠ 0}
def pivotProductDomain3 (j : κ) : Set (RegularCoordinates3 ι κ) := {p | p.2.1 j ≠ 0}

omit [Fintype ι] [DecidableEq κ] in
theorem isOpen_pivotProductSource3 (j : κ) : IsOpen (pivotProductSource3 (ι := ι) j) := by
  change IsOpen ({p : ((ι → ℝ) × RankThreeCone κ) | p.2.val 0 j = 0}ᶜ)
  have h : Continuous (fun p : ((ι → ℝ) × RankThreeCone κ) => p.2.val 0 j) :=
    (continuous_apply j).comp ((continuous_apply 0).comp
      (continuous_subtype_val.comp continuous_snd))
  exact (isClosed_eq h continuous_const).isOpen_compl

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem isOpen_pivotProductDomain3 (j : κ) : IsOpen (pivotProductDomain3 (ι := ι) j) := by
  change IsOpen ({p : RegularCoordinates3 ι κ | p.2.1 j = 0}ᶜ)
  exact (isClosed_eq (by fun_prop) continuous_const).isOpen_compl

/-- First flatten the pivot condition into the already constructed rank-one chart. -/
def pivotProductSplit3 (j : κ) : pivotProductSource3 (ι := ι) j ≃ₜ
    (ι → ℝ) × RankThreePivot j where
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

def pivotCoordinateFlatten3 (j : κ) : ((ι → ℝ) × PivotCoordinates3 j) ≃ₜ
    pivotProductDomain3 (ι := ι) j where
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

def pivotProductHomeomorph3 (j : κ) : pivotProductSource3 (ι := ι) j ≃ₜ
    pivotProductDomain3 (ι := ι) j :=
  ((pivotProductSplit3 j).trans
    ((Homeomorph.refl _).prodCongr (rankThreePivotHomeomorph j))).trans
    (pivotCoordinateFlatten3 j)

/-- Genuine open chart in the exact coordinate space ConeSpace. -/
def pivotProductChart3 (j : κ) : OpenEuclideanChart (((ι → ℝ) × RankThreeCone κ))
    (Fintype.card ι + Fintype.card κ + 2) where
  source := pivotProductSource3 j
  target := regularCoordinatesEuclidean3 '' pivotProductDomain3 j
  source_open := isOpen_pivotProductSource3 j
  target_open := regularCoordinatesEuclidean3.isOpenMap _ (isOpen_pivotProductDomain3 j)
  chart := (pivotProductHomeomorph3 j).trans
    (restrictImage regularCoordinatesEuclidean3 (pivotProductDomain3 j))

/-- An exact rank-one ray with the selected pivot equal to t. -/
def regularRay3 (j : κ) (t : ℝ) : ((ι → ℝ) × RankThreeCone κ) :=
  (0,⟨sphereOuter ![t,0,0] (fun k => if k=j then 1 else 0),rank_sphereOuter_le_one _ _⟩)

omit [Fintype ι] in
theorem continuous_regularRay3 (j : κ) : Continuous (regularRay3 (ι := ι) j) := by
  apply Continuous.prodMk
  · exact continuous_const
  · apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    apply continuous_pi
    intro k
    by_cases hkj : k = j <;> fin_cases i <;> simp [regularRay3, sphereOuter, hkj] <;> fun_prop

omit [Fintype ι] in
@[simp] theorem regularRay3_zero (j : κ) : regularRay3 (ι := ι) j 0 = productZero3 := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    ext i k
    fin_cases i <;> simp [regularRay3,productZero3,rankThreeZero,sphereOuter]

omit [Fintype ι] in
@[simp] theorem regularRay3_pivot (j : κ) (t : ℝ) :
    (regularRay3 (ι := ι) j t).2.val 0 j = t := by simp [regularRay3,sphereOuter]

/-- Every open vertex-neighborhood meets the regular pivot chart. -/
theorem exists_regular_in_open3 (j : κ) (U : Set (((ι → ℝ) × RankThreeCone κ)))
    (hU : IsOpen U) (hzero : productZero3 ∈ U) :
    ∃ p : ((ι → ℝ) × RankThreeCone κ), p ∈ U ∧ p ∈ (pivotProductChart3 (ι := ι) j).source := by
  have hopen : IsOpen (regularRay3 j ⁻¹' U) := hU.preimage (continuous_regularRay3 j)
  have hz : (0 : ℝ) ∈ regularRay3 j ⁻¹' U := by
    simpa only [Set.mem_preimage,regularRay3_zero] using hzero
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hz)
  refine ⟨regularRay3 j (δ/2),hball ?_,?_⟩
  · rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (by linarith)]
    linarith
  · change (regularRay3 j (δ/2)).2.val 0 j ≠ 0
    rw [regularRay3_pivot]
    linarith


end GS.UnitaryTopology
