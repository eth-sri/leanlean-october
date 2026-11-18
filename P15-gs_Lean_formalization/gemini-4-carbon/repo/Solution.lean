module

public import GS.Core
public import GS.Frobenius
public import GS.Projection
public import GS.Fibres
public import GS.CompactFibres
public import GS.OriginalLocalModel
public import GS.M4Certificate
public import GS.ComplexAlgebra
public import GS.Specifications
public import GS.Extensions.FiniteTopology
public import GS.Extensions.OriginalCompact
public import GS.Extensions.OrbitCompact
public import GS.Extensions.OriginalFibres
public import GS.Extensions.OriginalUniform
public import GS.Continuation.CompactCoverageTools
public import GS.Continuation.ExponentialBasics
public import GS.Continuation.ExponentialChart
public import GS.Continuation.PointedCompactImage
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic.Choose
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Tactic.FunProp
public import GS.Topology.SectionPair
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import GS.NonmanifoldClosure.PuncturedBall
public import GS.Topology.EuclideanSphere
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import GS.Nonmanifold.RankOneGeometry
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import GS.NonmanifoldCompletion.FullFibreCoverage
public import GS.Nonmanifold.SkewCoordinates
public import GS.Nonmanifold.OriginalModelCoordinates
public import GS.Nonmanifold.OriginalCompactModel
public import GS.Nonmanifold.NormalizationEstimates
public import GS.NonmanifoldObstruction.OpenGerms
public import GS.NonmanifoldCompletion.OriginalMembership
public import GS.NonmanifoldCompletion.BaseFibreGauges
public import GS.NonmanifoldCompletion.LocalAngles
public import GS.NonmanifoldCompletion.NeighbourhoodModel
public import GS.NonmanifoldFinal.ConditionalGS
public import GS.NonmanifoldFinal.RetractTransport
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import GS.NonmanifoldClosure.ChartRetractions
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.BigOperators.Intervals
public import GS.NonmanifoldFinal.FiniteCoordinates
public import GS.NonmanifoldFinal.EuclideanTransport
public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
public import Mathlib.Topology.Homotopy.TopCat.ToSSet
public import GS.NonmanifoldClosure.TopologicalClosure
public import GS.Results.Nonmanifold
public import GS.Results.CosineSine
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import GS.Unitary.Factorization
public import GS.Unitary.GeometryAlgebra
public import GS.Unitary.Frobenius
public import GS.Unitary.Projection
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import GS.Unitary.RealEmbedding
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import GS.UnitaryNonmanifold.ScalarBridge
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import GS.OverlapGeometry.HorizontalModel
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import GS.OverlapGeometry.FactorChartOpen
public import GS.OverlapGeometry.SliceAtlas
public import GS.OverlapGeometry.SmoothMaps
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import GS.OverlapGeometry.ManifoldSmoothMaps
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.MeanValue
public import GS.UnitaryManifold.CayleyCharts
public import GS.UnitaryManifold.LocalProduct
public import GS.UnitaryManifold.Action
public import Mathlib.Topology.Algebra.Group.Quotient
public import GS.Unitary.Permutations
public import GS.UnitaryManifold.CayleyDifferential
public import GS.UnitaryManifold.MatrixCalculus
public import GS.UnitaryManifold.KernelCayley
public import GS.Unitary.FrobeniusProjection
public import GS.UnitaryManifold.FrobeniusDual
public import GS.UnitaryManifold.UnitCayley
public import Mathlib.Tactic.Abel
public import GS.UnitaryManifold.Dimension
public import GS.UnitaryTopology.MatrixNonmanifold
public import GS.UnitarySharing.Geometry

@[expose] public section

/-! # Proofs of the Palomar statement of record

Every declaration below is proved by the full library. Challenge is never
imported here. The existing project README and coverage documents describe
the paper correspondence and the additional results.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
open Matrix
open scoped BigOperators Manifold ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GS.GlobalGeometry
def TiedEntries {n : ℕ} (b : ℕ) (τ : ℕ → ℕ) (A : GS.Mat n) : Prop :=
  ∀ i j i' j' : Fin n,
    i.val / b = j.val / b → i'.val / b = j'.val / b →
    τ (i.val / b) = τ (i'.val / b) →
    i.val % b = i'.val % b → j.val % b = j'.val % b → A i j = A i' j'

def SharedOrthogonalFactor {n : ℕ} (b : ℕ) (τ : ℕ → ℕ) (A : GS.Mat n) : Prop :=
  GS.BlockDiagonal b A ∧ GS.Orthogonal A ∧ TiedEntries b τ A

def InSharedA2Orth {n : ℕ} (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P X : GS.Mat n) : Prop :=
  ∃ L R, SharedOrthogonalFactor b₂ τ₂ L ∧ SharedOrthogonalFactor b₁ τ₁ R ∧ X = GS.product2 L P R
end GS.GlobalGeometry

namespace GSPalomar

/-- Every orthogonal matrix in the two-layer class admits orthogonal layers. -/
theorem two_factor (n : ℕ) (s₁ s₂ : GS.BlockSpec n)
    (σ : Equiv.Perm (Fin n)) (A : GS.Mat n) :
    GS.InA2 s₁.size s₂.size (GS.permMatrix σ) A ∧ GS.Orthogonal A ↔
      GS.InA2Orth s₁.size s₂.size (GS.permMatrix σ) A :=
  GS.Extensions.twoFactorOrthogonalization n s₁ s₂ σ A

/-- The same equality holds for three layers and arbitrary fixed permutations. -/
theorem three_factor (n : ℕ) (s₁ s₂ s₃ : GS.BlockSpec n)
    (σ₁ σ₂ : Equiv.Perm (Fin n)) (A : GS.Mat n) :
    GS.InA3 s₁.size s₂.size s₃.size (GS.permMatrix σ₁) (GS.permMatrix σ₂) A ∧
      GS.Orthogonal A ↔
    GS.InA3Orth s₁.size s₂.size s₃.size (GS.permMatrix σ₁) (GS.permMatrix σ₂) A :=
  GS.Extensions.threeFactorOrthogonalization n s₁ s₂ s₃ σ₁ σ₂ A

/-- Four 2-by-2-block layers need not admit an orthogonal-layer realization. -/
theorem four_factor_counterexample :
    ∃ A : GS.Mat 6,
      GS.InA4 2 2 2 2 GS.M4.P GS.M4.P GS.M4.P A ∧ GS.Orthogonal A ∧
      ¬ GS.InA4Orth 2 2 2 2 GS.M4.P GS.M4.P GS.M4.P A :=
  ⟨GS.M4.Q, GS.M4.counterexample⟩

open GS GS.UnitaryGeometry

/-- Unrestricted two-layer unitary matrices admit unitary layers. -/
theorem unitary_two_factor {n : ℕ} (b₁ b₂ : ℕ)
    (σ : Equiv.Perm (Fin n)) (A : CMat n) :
    CInA2 b₁ b₂ (cPermMatrix σ) A ∧ Unitary A ↔
      CInA2Unitary b₁ b₂ (cPermMatrix σ) A := GS.UnitaryGeometry.twoFactorUnitarization b₁ b₂ σ A

/-- Unrestricted three-layer unitary matrices admit unitary layers. -/
theorem unitary_three_factor {n : ℕ} (b₁ b₂ b₃ : ℕ)
    (σ₁ σ₂ : Equiv.Perm (Fin n)) (A : CMat n) :
    CInA3 b₁ b₂ b₃ (cPermMatrix σ₁) (cPermMatrix σ₂) A ∧ Unitary A ↔
      CInA3Unitary b₁ b₂ b₃ (cPermMatrix σ₁) (cPermMatrix σ₂) A := GS.UnitaryGeometry.threeFactorUnitarization b₁ b₂ b₃ σ₁ σ₂ A

/-- Allowing complex unitary layers does not remove the four-layer obstruction. -/
theorem unitary_four_factor_counterexample :
    ∃ A : CMat 6, let P : CMat 6 := fun i j => (GS.M4.P i j : ℂ)
      CInA4 2 2 2 2 P P P A ∧ Unitary A ∧ ¬CInA4Unitary 2 2 2 2 P P P A := ⟨GS.UnitaryFour.Q, GS.UnitaryFour.counterexample⟩

/-- The scalar (p,2,p) family fills the orthogonal group (including p=0). -/
theorem real_cs_exhaustion {p : ℕ} {A : Mat (2*p)} :
    InA3Orth p 2 p (permMatrix (scalarShuffle 2 p))
      (permMatrix (scalarShuffle 2 p))ᵀ A ↔ Orthogonal A := GS.Results.CosineSine.scalar_exhaustion

/-- Complex cosine-sine decomposition gives the entire unitary group. -/
theorem unitary_cs_exhaustion {p : ℕ} {A : CMat (2*p)} :
    CInA3Unitary p 2 p (cPermMatrix (scalarShuffle 2 p))
      (cPermMatrix (scalarShuffle 2 p))ᴴ A ↔ Unitary A := GS.Results.UnitaryCosineSine.scalar_exhaustion

/-- A rank-one determinantal singularity survives any Euclidean factor. -/
theorem rank_one_cone_singularity (d e : ℕ) (hd : 2 ≤ d) :
    ¬ EuclideanAtSubset
      {p : (Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ | p.2.rank ≤ 1} (0, 0) := GS.Results.cone_rankOne_not_euclidean d e hd

/-- Every all-nonzero orthogonal base gives a genuine topological singularity. -/
theorem real_three_factor_singularity {q : ℕ} (hq : 3 ≤ q)
    (Q : Mat q) (hQ : Orthogonal Q) (hne : ∀ i j, Q i j ≠ 0) :
    ¬ EuclideanAtSubset (localFamily q) (basePoint Q) := GS.Results.gs_not_euclidean_at hq Q hQ hne

/-- There is a singular point for every q≥3, with no conditional base assumption. -/
theorem real_singular_point (q : ℕ) (hq : 3 ≤ q) :
    ∃ A : Mat (q*2), A ∈ localFamily q ∧ ¬ EuclideanAtSubset (localFamily q) A := GS.Results.exists_nonEuclidean_point q hq

/-- The unitary topological result is restricted to odd q. -/
theorem unitary_singular_point (q : ℕ) (hq : 3 ≤ q) (hodd : Odd q) :
    let P := cPermMatrix (scalarShuffle q 2)
    let S : Set (CMat (q*2)) := {A | CInA3Unitary 2 q 2 P Pᴴ A}
    ∃ A : CMat (q*2), A ∈ S ∧ ¬ EuclideanAtSubset S A := GS.UnitaryTopology.exists_unitary_nonEuclidean_point q hq hodd

/-- A finite-dimensional atlas on the given matrix subtype, an injective
inclusion differential with exactly the prescribed tangent image, a jointly
smooth orthogonal projector, a smooth whole-tangent-bundle retraction, and
smooth gradient sections for every smooth ambient loss. The topology of the
subtype is fixed before the atlas is chosen. -/
def EmbeddedGeometry {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (pairing : A → A → ℝ) (S : Set A) (D : A → A → Prop) : Prop :=
  ∃ E : Type, ∃ normE : NormedAddCommGroup E, letI := normE
  ∃ spaceE : NormedSpace ℝ E, letI := spaceE
  FiniteDimensional ℝ E ∧
  ∃ cs : ChartedSpace E S, letI := cs
  ∃ hm : IsManifold (𝓘(ℝ, E)) ⊤ S, letI := hm
  ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, A)) ⊤ (fun X : S => X.val) ∧
  (∀ X : S, Function.Injective (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, A))
    (fun Y : S => Y.val) X)) ∧
  (∀ (X : S) (Z : A), D X.val Z ↔ ∃ v : E,
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, A)) (fun Y : S => Y.val) X v = Z) ∧
  (∃ π : S × A → A,
    ContMDiff ((𝓘(ℝ, E)).prod (𝓘(ℝ, A))) (𝓘(ℝ, A)) ⊤ π ∧
    ∀ (X : S) (Z : A), D X.val (π (X, Z)) ∧
      ∀ Y : A, D X.val Y → pairing (Z - π (X, Z)) Y = 0) ∧
  (∃ R : TangentBundle (𝓘(ℝ, E)) S → S,
    ContMDiff (𝓘(ℝ, E)).tangent (𝓘(ℝ, E)) ⊤ R ∧
    (∀ X : S, R ⟨X, 0⟩ = X) ∧
    ∀ X : S, mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E))
      (fun v : E => R ⟨X, v⟩) 0 = ContinuousLinearMap.id ℝ E) ∧
  (∀ f : A → ℝ, ContDiff ℝ ∞ f → ∃ g : S → E,
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)).tangent ∞
      (fun X : S => (⟨X, g X⟩ : TangentBundle (𝓘(ℝ, E)) S)) ∧
    ∀ (X : S) (v : E),
      pairing (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, A)) (fun Y : S => Y.val) X (g X))
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, A)) (fun Y : S => Y.val) X v) =
      mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) (fun Y : S => f Y.val) X v)

/-- Exact real tangent directions with the prescribed layer supports and ties. -/
def RealDirections {n : ℕ} (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (X Z : Mat n) : Prop :=
  ∃ C Ω : Mat n,
    (BlockDiagonal b₂ C ∧ Cᵀ = -C ∧ GS.GlobalGeometry.TiedEntries b₂ τ₂ C) ∧
    (BlockDiagonal b₁ Ω ∧ Ωᵀ = -Ω ∧ GS.GlobalGeometry.TiedEntries b₁ τ₁ Ω) ∧
    Z = C * X + X * Ω

/-- Exact real tangent directions in the unitary case; phases are retained. -/
def ComplexDirections {n : ℕ} (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (X Z : CMat n) : Prop :=
  ∃ C Ω : CMat n,
    (CBlockDiagonal b₂ C ∧ Cᴴ = -C ∧ GS.UnitarySharing.TiedEntries b₂ τ₂ C) ∧
    (CBlockDiagonal b₁ Ω ∧ Ωᴴ = -Ω ∧ GS.UnitarySharing.TiedEntries b₁ τ₁ Ω) ∧
    Z = C * X + X * Ω

private theorem shared_embedded_geometry {𝕂 : Type} [RCLike 𝕂] {n : ℕ} (b₁ b₂ : ℕ)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hd₁ : b₁ ∣ n) (hd₂ : b₂ ∣ n)
    (τ₁ τ₂ : ℕ → ℕ) (P : Matrix (Fin n) (Fin n) 𝕂)
    (pairing : Matrix (Fin n) (Fin n) 𝕂 → Matrix (Fin n) (Fin n) 𝕂 → ℝ)
    (hpair : pairing = cFrobInner)
    (S : Set (Matrix (Fin n) (Fin n) 𝕂))
    (hS : S = {X | GS.UnitarySharing.KInSharedA2 b₁ b₂ τ₁ τ₂ P X})
    (D : Matrix (Fin n) (Fin n) 𝕂 → Matrix (Fin n) (Fin n) 𝕂 → Prop)
    (hD : ∀ X Z, D X Z ↔ Z ∈ GS.UnitarySharing.pointDirections ⟨b₁, hb₁, hd₁, τ₁⟩ ⟨b₂, hb₂, hd₂, τ₂⟩ X) :
    EmbeddedGeometry pairing S D := by
  let right : GS.UnitarySharing.Pattern 𝕂 n := ⟨b₁, hb₁, hd₁, τ₁⟩
  let left : GS.UnitarySharing.Pattern 𝕂 n := ⟨b₂, hb₂, hd₂, τ₂⟩
  subst hpair
  rw [hS, ← GS.UnitarySharing.orbit_set_eq_inShared (right := right) (left := left) P]
  let E := GS.UnitarySharing.HorizontalModel right left P
  let : NormedSpace ℝ E := Submodule.normedSpace _
  let : ChartedSpace E (GS.UnitarySharing.MatrixOrbit right left P) :=
    GS.UnitarySharing.sharedOrbitChartedSpace right left P
  let : IsManifold (𝓘(ℝ, E)) ⊤ (GS.UnitarySharing.MatrixOrbit right left P) :=
    GS.UnitarySharing.sharedOrbitIsManifold right left P
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    GS.UnitarySharing.sharedOrbit_val_contMDiff right left P,
    GS.UnitarySharing.sharedOrbit_val_mfderiv_injective right left P, ?_, ?_, ?_, ?_⟩
  · intro X Z
    exact (hD X.val Z).trans (GS.UnitarySharing.orbit_tangent_image_iff right left P X Z).symm
  · refine ⟨fun p => GS.UnitarySharing.pointProjection right left p.1.val p.2,
      GS.UnitarySharing.pointProjection_contMDiff right left P, fun X Z =>
        ⟨(hD _ _).mpr (GS.UnitarySharing.pointProjection_mem X.val Z),
         fun Y hY => GS.UnitarySharing.pointProjection_normal X.val Z Y ((hD _ _).mp hY)⟩⟩
  · exact ⟨GS.UnitarySharing.cayleyRetraction right left P,
      GS.UnitarySharing.cayleyRetraction_contMDiff right left P,
      GS.UnitarySharing.cayleyRetraction_zero_section right left P,
      GS.UnitarySharing.cayleyRetraction_fibre_mfderiv_zero right left P⟩
  · intro f hf
    exact ⟨GS.UnitarySharing.intrinsicGradient right left P f,
      GS.UnitarySharing.intrinsicGradientSection_smooth right left P f hf,
      fun X v => GS.UnitarySharing.intrinsicGradient_characterization right left P f X
        ((hf.differentiable (by simp)) X) v⟩

/-- Smooth geometry of the actual orthogonal image, including arbitrary overlap,
complete within-layer sharing, and arbitrary fixed carriers. -/
theorem orthogonal_shared_geometry {n : ℕ} (b₁ b₂ : ℕ)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hd₁ : b₁ ∣ n) (hd₂ : b₂ ∣ n)
    (τ₁ τ₂ : ℕ → ℕ) (P : Mat n) :
    EmbeddedGeometry (fun A B : Mat n => ∑ i, ∑ j, A i j * B i j)
      {X | GS.GlobalGeometry.InSharedA2Orth b₁ b₂ τ₁ τ₂ P X}
      (RealDirections b₁ b₂ τ₁ τ₂) := by
  refine shared_embedded_geometry (𝕂 := ℝ) b₁ b₂ hb₁ hb₂ hd₁ hd₂ τ₁ τ₂ P _ ?_ _ ?_ _ ?_
  · ext A B; simp [cFrobInner]
  · ext X; simp [GS.GlobalGeometry.InSharedA2Orth, GS.GlobalGeometry.SharedOrthogonalFactor,
      GS.UnitarySharing.KInSharedA2, GS.UnitarySharing.KSharedFactor,
      GS.BlockDiagonal, GS.Supported, KSSupported, GS.GlobalGeometry.TiedEntries,
      GS.UnitarySharing.KTiedEntries, GS.product2, GS.UnitaryGeometry.kProduct2, GS.KUnitary, GS.Orthogonal]
  · intro X Z; rw [GS.UnitarySharing.mem_pointDirections_iff]
    simp only [RealDirections, GS.UnitarySharing.sharedSkewSpace, Submodule.mem_mk, Set.mem_setOf_eq,
      GS.BlockDiagonal, GS.Supported, KSSupported, GS.IsSkewHermitian,
      Matrix.conjTranspose_eq_transpose_of_trivial, GS.GlobalGeometry.TiedEntries,
      GS.UnitarySharing.KTiedEntries]
    exact ⟨fun ⟨C, Ω, hC, hΩ, he⟩ => ⟨C, hC, Ω, hΩ, he⟩,
           fun ⟨C, hC, Ω, hΩ, he⟩ => ⟨C, Ω, hC, hΩ, he⟩⟩

/-- The same real differential geometry for shared unitary layers, with the
full continuous stabilizer allowed. No special-unitary restriction is imposed. -/
theorem unitary_shared_geometry {n : ℕ} (b₁ b₂ : ℕ)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hd₁ : b₁ ∣ n) (hd₂ : b₂ ∣ n)
    (τ₁ τ₂ : ℕ → ℕ) (P : CMat n) :
    EmbeddedGeometry (fun A B : CMat n =>
      ∑ i, ∑ j, ((A i j).re * (B i j).re + (A i j).im * (B i j).im))
      {X | GS.UnitarySharing.InSharedA2Unitary b₁ b₂ τ₁ τ₂ P X}
      (ComplexDirections b₁ b₂ τ₁ τ₂) := by
  refine shared_embedded_geometry (𝕂 := ℂ) b₁ b₂ hb₁ hb₂ hd₁ hd₂ τ₁ τ₂ P _ ?_ _ ?_ _ ?_
  · ext A B
    simp only [cFrobInner, RCLike.re_eq_complex_re, Complex.mul_re, Complex.star_def,
      Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add]
  · ext X; simp [GS.UnitarySharing.InSharedA2Unitary, GS.UnitarySharing.SharedUnitaryFactor,
      GS.UnitarySharing.KInSharedA2, GS.UnitarySharing.KSharedFactor,
      GS.UnitarySharing.TiedEntries, GS.UnitarySharing.KTiedEntries,
      CSupported, KSSupported, GS.UnitaryGeometry.product2, GS.UnitaryGeometry.kProduct2,
      GS.KUnitary, GS.Unitary]
  · intro X Z; rw [GS.UnitarySharing.mem_pointDirections_iff]
    simp only [ComplexDirections, GS.UnitarySharing.sharedSkewSpace, Submodule.mem_mk,
      Set.mem_setOf_eq, CBlockDiagonal, CSupported, KSSupported, GS.IsSkewHermitian,
      GS.UnitarySharing.TiedEntries, GS.UnitarySharing.KTiedEntries]
    exact ⟨fun ⟨C, Ω, hC, hΩ, he⟩ => ⟨C, hC, Ω, hΩ, he⟩,
           fun ⟨C, hC, Ω, hΩ, he⟩ => ⟨C, Ω, hC, hΩ, he⟩⟩

private theorem exists_factor_of_rank_le {n : ℕ} {τ : Type*} [Fintype τ]
    {A : Mat n} (h : A.rank ≤ Fintype.card τ) :
    ∃ (U : Matrix (Fin n) τ ℝ) (V : Matrix τ (Fin n) ℝ), A = U * V := by
  let S : Submodule ℝ (Fin n → ℝ) := LinearMap.range A.mulVecLin
  let b : Module.Basis (Fin A.rank) ℝ S := Module.finBasis ℝ S
  let x (j : Fin n) : S := A.mulVecLin.rangeRestrict (Pi.single j 1)
  have h0 (i j : Fin n) : (x j : Fin n → ℝ) i = ∑ k : Fin A.rank, b.repr (x j) k * (b k : Fin n → ℝ) i := by
    have hb := congrArg (fun y : S => (y : Fin n → ℝ) i) (b.sum_repr (x j))
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] using hb.symm
  classical
  let e : Fin A.rank → τ := (Fintype.equivFin τ).symm ∘ Fin.castLE h
  have he : Function.Injective e :=
    (Fintype.equivFin τ).symm.injective.comp (Fin.castLE_injective h)
  let U : Matrix (Fin n) τ ℝ := fun i => Function.extend e (fun k => (b k : Fin n → ℝ) i) 0
  let V : Matrix τ (Fin n) ℝ := fun t j => Function.extend e (fun k => b.repr (x j) k) 0 t
  refine ⟨U, V, Matrix.ext fun i j => ?_⟩
  have hx : (x j : Fin n → ℝ) i = A i j := by simp [x, LinearMap.rangeRestrict]
  rw [← hx, h0 i j, Matrix.mul_apply]
  exact (Finset.sum_congr rfl fun k _ => mul_comm _ _).trans <|
    Fintype.sum_of_injective e he
      (fun k => (b k : Fin n → ℝ) i * b.repr (x j) k) (fun t => U i t * V t j)
      (fun t ht => by simp [U, V, Function.extend_apply', show ¬∃ k, e k = t from ht])
      (fun k => by simp [U, V, he.extend_apply])

/-- Exact cell-rank criterion, including singular matrices and empty cells. -/
theorem two_factor_rank_criterion {n : ℕ} (b₁ b₂ : ℕ)
    (σ : Equiv.Perm (Fin n)) (A : GS.Mat n) :
    GS.InA2 b₁ b₂ (GS.permMatrix σ) A ↔
      ∀ a b : ℕ,
        (Matrix.of fun i j : Fin n =>
          if a = i.val / b₂ ∧ b = j.val / b₁ then A i j else 0).rank ≤
        Fintype.card {t : Fin n // a = (σ t).val / b₂ ∧ b = t.val / b₁} := by
  classical
  let Slots (a b : ℕ) := {t : Fin n // a = (σ t).val / b₂ ∧ b = t.val / b₁}
  let blk (a b : ℕ) (M : Mat n) : Mat n := Matrix.of fun i j =>
    if a = i.val / b₂ ∧ b = j.val / b₁ then M i j else 0
  constructor
  · rintro ⟨B₁, B₂, hb₁, hb₂, rfl⟩ a b
    let U : Matrix (Fin n) (Slots a b) ℝ := fun i t =>
      if a = i.val / b₂ then B₂ i (σ t.1) else 0
    let V : Matrix (Slots a b) (Fin n) ℝ := fun t j =>
      if b = j.val / b₁ then B₁ t.1 j else 0
    have hUV : blk a b (GS.product2 B₂ (permMatrix σ) B₁) = U * V := Matrix.ext fun i j => by
      rw [Matrix.mul_apply]
      dsimp [blk, U, V, GS.product2]
      by_cases ha : a = i.val / b₂ <;> by_cases hb : b = j.val / b₁
      · rw [if_pos ⟨ha, hb⟩, Matrix.mul_apply]
        simp only [ha, hb, ↓reduceIte, mul_perm_apply]
        symm
        refine Fintype.sum_of_injective Subtype.val Subtype.val_injective
          (fun t : Slots a b => B₂ i (σ t.1) * B₁ t.1 j)
          (fun t : Fin n => B₂ i (σ t) * B₁ t j) (fun t ht => ?_) (fun _ => rfl)
        by_cases h1 : i.val / b₂ = (σ t).val / b₂
        · have h2 : t.val / b₁ ≠ j.val / b₁ := fun h2 => ht ⟨⟨t, ha.trans h1, hb.trans h2.symm⟩, rfl⟩
          rw [hb₁ t j h2, mul_zero]
        · rw [hb₂ i (σ t) h1, zero_mul]
      all_goals simp [ha, hb]
    change (blk a b (GS.product2 B₂ (permMatrix σ) B₁)).rank ≤ Fintype.card (Slots a b)
    rw [hUV]
    exact (Matrix.rank_mul_le_left U V).trans (Matrix.rank_le_card_width U)
  · intro h
    choose U V hUV using fun a b => exists_factor_of_rank_le (h a b)
    let L : Mat n := fun i t =>
      if i.val / b₂ = (σ t).val / b₂ then
        U ((σ t).val / b₂) (t.val / b₁) i ⟨t, rfl, rfl⟩ else 0
    let B₁ : Mat n := fun t j =>
      if t.val / b₁ = j.val / b₁ then
        V ((σ t).val / b₂) (t.val / b₁) ⟨t, rfl, rfl⟩ j else 0
    have hterm (a b : ℕ) (i j : Fin n) (ha : a = i.val / b₂) (hb : b = j.val / b₁)
        (t : Slots a b) : U a b i t * V a b t j = L i t.1 * B₁ t.1 j := by
      rcases t with ⟨t, rfl, rfl⟩; simp [L, B₁, ← ha, hb]
    refine ⟨B₁, L * (permMatrix σ)ᵀ, fun t j htj => by simp [B₁, htj], ?_, ?_⟩
    · intro i j hij
      rw [perm_transpose, mul_perm_apply]
      simpa [L, Equiv.apply_symm_apply] using fun h' => absurd h' hij
    · have hLP : L * (permMatrix σ)ᵀ * permMatrix σ = L := by
        rw [Matrix.mul_assoc, (perm_orthogonal σ).1, Matrix.mul_one]
      dsimp [GS.product2]; rw [hLP]
      ext i j
      have hentry := congrFun (congrFun (hUV (i.val / b₂) (j.val / b₁)) i) j
      simp only [Matrix.of_apply, and_self, ↓reduceIte, Matrix.mul_apply] at hentry ⊢
      rw [hentry]
      refine Fintype.sum_of_injective Subtype.val Subtype.val_injective
        (fun t : Slots (i.val / b₂) (j.val / b₁) => U (i.val / b₂) (j.val / b₁) i t * V (i.val / b₂) (j.val / b₁) t j)
        (fun t : Fin n => L i t * B₁ t j) (fun t ht => ?_)
        (hterm (i.val / b₂) (j.val / b₁) i j rfl rfl)
      by_cases h1 : i.val / b₂ = (σ t).val / b₂
      · have h2 : t.val / b₁ ≠ j.val / b₁ := fun h2 => ht ⟨⟨t, h1, h2.symm⟩, rfl⟩
        simp [B₁, h2]
      · simp [L, h1]

/-- With no off-diagonal overlap, the explicit shared block exponentials stay
in the actual image and have normal ambient acceleration and constant speed.
The normality test ranges over the entire tangent image given above. -/
theorem orthogonal_shared_block_geodesic {n : ℕ} (b₁ b₂ : ℕ)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hd₁ : b₁ ∣ n) (hd₂ : b₂ ∣ n)
    (τ₁ τ₂ : ℕ → ℕ) (σ : Equiv.Perm (Fin n))
    (hno : Function.Injective (fun i : Fin n => (i.val / b₁, (σ i).val / b₂)))
    (L R C Ω : Mat n)
    (hL : GS.GlobalGeometry.SharedOrthogonalFactor b₂ τ₂ L)
    (hR : GS.GlobalGeometry.SharedOrthogonalFactor b₁ τ₁ R)
    (hC : BlockDiagonal b₂ C ∧ Cᵀ = -C ∧ GS.GlobalGeometry.TiedEntries b₂ τ₂ C)
    (hΩ : BlockDiagonal b₁ Ω ∧ Ωᵀ = -Ω ∧ GS.GlobalGeometry.TiedEntries b₁ τ₁ Ω) :
    let γ : ℝ → Mat n := fun t =>
      L * NormedSpace.exp (t • C) * permMatrix σ * (NormedSpace.exp (t • Ω) * R)
    ∀ t : ℝ,
      GS.GlobalGeometry.InSharedA2Orth b₁ b₂ τ₁ τ₂ (permMatrix σ) (γ t) ∧
      HasDerivAt γ (deriv γ t) t ∧
      HasDerivAt (deriv γ) (deriv (deriv γ) t) t ∧
      (∀ Z : Mat n, RealDirections b₁ b₂ τ₁ τ₂ (γ t) Z →
        (∑ i, ∑ j, deriv (deriv γ) t i j * Z i j) = 0) ∧
      (∑ i, ∑ j, (deriv γ t i j)^2) =
        (∑ i, ∑ j, (C i j)^2) + (∑ i, ∑ j, (Ω i j)^2) := by
  intro γ
  have hexp_tied {b : ℕ} {τ : ℕ → ℕ} (hb : 0 < b) (hd : b ∣ n) {M : Mat n}
      (hMs : BlockDiagonal b M) (hMt : GS.GlobalGeometry.TiedEntries b τ M) (t : ℝ) :
      GS.GlobalGeometry.TiedEntries b τ (GS.Continuation.expLine M t) := by
    let S := GS.UnitarySharing.sharedMatrixSpace ℝ (n := n) b τ
    have hmem : t • M ∈ S := ⟨Supported.smul t hMs, (show GS.UnitarySharing.KTiedEntries b τ M from hMt).smul t⟩
    have hpow (k : ℕ) : (t • M) ^ k ∈ S := by
      induction k with
      | zero => simpa using GS.UnitarySharing.one_mem_sharedMatrixSpace ℝ (n := n) b τ
      | succ k ih => simpa [pow_succ] using GS.UnitarySharing.mul_mem_sharedMatrixSpace hb hd ih hmem
    have hcl : IsClosed (S : Set (Mat n)) :=
      (GS.UnitaryManifold.closed_supported (𝕂 := ℝ) _).inter (GS.UnitarySharing.isClosed_tiedEntries (𝕂 := ℝ) b τ)
    exact (hcl.mem_of_tendsto (GS.matrixExp_hasSum (t • M))
      (Filter.Eventually.of_forall fun s => S.sum_mem fun k _ => S.smul_mem _ (hpow k))).2
  let P := permMatrix σ
  have hP : Orthogonal P := perm_orthogonal σ
  let K : Mat n := P * Ω * Pᵀ
  let Lt (t : ℝ) : Mat n := L * GS.Continuation.expLine C t
  let Rt (t : ℝ) : Mat n := GS.Continuation.expLine Ω t * R
  let Qt (t : ℝ) : Mat n := P * Rt t
  let v (t : ℝ) : Mat n := Lt t * (C + K) * Qt t
  let accCore : Mat n := C * C + (2 : ℝ) • (C * K) + K * K
  let a (t : ℝ) : Mat n := Lt t * accCore * Qt t
  have hγ_eq (t : ℝ) : γ t = Lt t * Qt t := by
    simp only [γ, Lt, Qt, Rt, P, GS.Continuation.expLine, GS.matrixExp_eq_exp, Matrix.mul_assoc]
  have dLt (t : ℝ) : HasDerivAt Lt (Lt t * C) t := by
    simpa only [Lt, Matrix.zero_mul, zero_add, Matrix.mul_assoc] using
      GS.UnitaryManifold.hasDerivAt_matrix_mul (𝕂 := ℝ) (hasDerivAt_const t L) (GS.Continuation.hasDerivAt_expLine C t)
  have dRt (t : ℝ) : HasDerivAt Rt (Ω * Rt t) t := by
    simpa only [Rt, Matrix.mul_zero, add_zero, Matrix.mul_assoc] using
      GS.UnitaryManifold.hasDerivAt_matrix_mul (𝕂 := ℝ) (GS.Continuation.hasDerivAt_expLine_left Ω t) (hasDerivAt_const t R)
  have dQt (t : ℝ) : HasDerivAt Qt (K * Qt t) t := by
    have he : K * Qt t = P * (Ω * Rt t) := by
      calc K * Qt t = P * Ω * (Pᵀ * P) * Rt t := by simp only [K, Qt, Matrix.mul_assoc]
        _ = P * (Ω * Rt t) := by rw [hP.1]; simp only [Matrix.one_mul, Matrix.mul_assoc]
    rw [he]
    simpa only [Qt, Matrix.zero_mul, zero_add] using
      GS.UnitaryManifold.hasDerivAt_matrix_mul (𝕂 := ℝ) (hasDerivAt_const t P) (dRt t)
  have hv (t : ℝ) : HasDerivAt γ (v t) t := by
    have h := GS.UnitaryManifold.hasDerivAt_matrix_mul (𝕂 := ℝ) (dLt t) (dQt t)
    simpa only [← hγ_eq, v, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc] using h
  have heV : deriv γ = v := funext fun t => (hv t).deriv
  have ha (t : ℝ) : HasDerivAt v (a t) t := by
    have h := GS.UnitaryManifold.hasDerivAt_matrix_mul (𝕂 := ℝ)
      (GS.UnitaryManifold.hasDerivAt_matrix_mul (𝕂 := ℝ) (dLt t) (hasDerivAt_const t (C + K))) (dQt t)
    convert h using 1
    ext i j
    simp only [a, accCore, Matrix.mul_zero, add_zero, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have heA : deriv (deriv γ) = a := by rw [heV]; exact funext fun t => (ha t).deriv
  let a₂ : Fin n → ℕ := (·.val / b₂)
  let b₁' : Fin n → ℕ := (·.val / b₁) ∘ σ.symm
  have hdisj_zero {X Y : Mat n} (hX : Supported a₂ X) (hY : Supported b₁' Y)
      (hd : ∀ i, X i i = 0 ∨ Y i i = 0) : frobInner X Y = 0 :=
    frobInner_eq_zero_of_disjoint X Y fun i j =>
      if ha : a₂ i = a₂ j then
        if hb : b₁' i = b₁' j then
          (σ.symm.injective (hno (Prod.ext hb (by simpa [a₂] using ha)))) ▸ hd i
        else Or.inr (hY i j hb)
      else Or.inl (hX i j ha)
  have hsym_skew {S W : Mat n} (hS : Sᵀ = S) (hW : IsSkew W) : frobInner S W = 0 := by
    have ht := frobInner_transpose S W
    rw [hS, show Wᵀ = -W from hW, frobInner_comm S (-W), frobInner_neg_left, frobInner_comm W S] at ht
    linarith
  have hKs : Supported b₁' K := (supported_perm_conjugate_iff (fun i : Fin n => i.val / b₁) σ Ω).mpr hΩ.1
  have hKskew : IsSkew K := by
    simp only [IsSkew, K, Matrix.transpose_mul, Matrix.transpose_transpose, hΩ.2.1,
      Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  intro t
  have hLt : GS.GlobalGeometry.SharedOrthogonalFactor b₂ τ₂ (Lt t) :=
    ⟨hL.1.mul (GS.Continuation.expLine_supported hC.1 t),
     hL.2.1.mul (GS.Continuation.expLine_orthogonal hC.2.1 t),
     GS.UnitarySharing.KTiedEntries.mul (𝕂 := ℝ) hb₂ hd₂ hL.1 (GS.Continuation.expLine_supported hC.1 t)
       hL.2.2 (hexp_tied hb₂ hd₂ hC.1 hC.2.2 t)⟩
  have hRt : GS.GlobalGeometry.SharedOrthogonalFactor b₁ τ₁ (Rt t) :=
    ⟨(GS.Continuation.expLine_supported hΩ.1 t).mul hR.1,
     (GS.Continuation.expLine_orthogonal hΩ.2.1 t).mul hR.2.1,
     GS.UnitarySharing.KTiedEntries.mul (𝕂 := ℝ) hb₁ hd₁ (GS.Continuation.expLine_supported hΩ.1 t) hR.1
       (hexp_tied hb₁ hd₁ hΩ.1 hΩ.2.2 t) hR.2.2⟩
  refine ⟨⟨Lt t, Rt t, hLt, hRt, by simp [hγ_eq, Qt, P, GS.product2, Matrix.mul_assoc]⟩,
    heV ▸ hv t, by rw [heA, heV]; exact ha t, ?_, ?_⟩
  · rintro Z ⟨A, B, hA, hB, rfl⟩
    rw [heA]
    let D : Mat n := (Lt t)ᵀ * A * Lt t
    let E : Mat n := P * (Rt t * B * (Rt t)ᵀ) * Pᵀ
    have hDs : Supported a₂ D := (hLt.1.transpose.mul hA.1).mul hLt.1
    have hEs : Supported b₁' E :=
      (supported_perm_conjugate_iff (fun i : Fin n => i.val / b₁) σ _).mpr ((hRt.1.mul hB.1).mul hRt.1.transpose)
    have hDskew : IsSkew D := by
      simp only [IsSkew, D, Matrix.transpose_mul, Matrix.transpose_transpose, hA.2.1,
        Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    have hEskew : IsSkew E := by
      simp only [IsSkew, E, Matrix.transpose_mul, Matrix.transpose_transpose, hB.2.1,
        Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    have hDEskew : IsSkew (D + E) := by
      simp only [IsSkew, Matrix.transpose_add, show Dᵀ = -D from hDskew, show Eᵀ = -E from hEskew, neg_add]
    have hZ_eq : A * γ t + γ t * B = Lt t * (D + E) * Qt t := by
      rw [hγ_eq, Matrix.mul_add, Matrix.add_mul]
      have h1 : Lt t * D * Qt t = A * (Lt t * Qt t) := by
        calc Lt t * D * Qt t = (Lt t * (Lt t)ᵀ) * A * (Lt t * Qt t) := by simp only [D, Matrix.mul_assoc]
          _ = A * (Lt t * Qt t) := by rw [hLt.2.1.2, Matrix.one_mul, Matrix.mul_assoc]
      have h2 : Lt t * E * Qt t = (Lt t * Qt t) * B := by
        calc Lt t * E * Qt t = Lt t * P * Rt t * B * (Rt t)ᵀ * (Pᵀ * P) * Rt t := by
              simp only [E, Qt, Matrix.mul_assoc]
          _ = Lt t * (P * Rt t) * B * ((Rt t)ᵀ * Rt t) := by rw [hP.1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = (Lt t * Qt t) * B := by rw [hRt.2.1.1, Matrix.mul_one]
      rw [h1, h2]
    change frobInner (a t) (A * γ t + γ t * B) = 0
    rw [hZ_eq]
    have horth : frobInner (a t) (Lt t * (D + E) * Qt t) = frobInner accCore (D + E) := by
      dsimp only [a]
      rw [frobInner_right_orthogonal (Qt t) (hP.mul hRt.2.1), frobInner_left_orthogonal (Lt t) hLt.2.1]
    rw [horth]
    dsimp only [accCore]
    have hCKD : frobInner (C * K) D = 0 := by
      rw [frobInner_mul_left, frobInner_comm]
      exact hdisj_zero (hC.1.transpose.mul hDs) hKs fun i => Or.inr (isSkew_diagonal_zero hKskew i)
    have hCKE : frobInner (C * K) E = 0 := by
      rw [← frobInner_transpose, Matrix.transpose_mul, frobInner_mul_left, Matrix.transpose_transpose]
      exact hdisj_zero hC.1.transpose (hKs.mul hEs.transpose) fun i =>
        Or.inl (by simp [isSkew_diagonal_zero (show IsSkew C from hC.2.1) i])
    rw [frobInner_add_left, frobInner_add_left, frobInner_smul_left,
      hsym_skew (S := C * C) (by simp [Matrix.transpose_mul, hC.2.1]) hDEskew,
      hsym_skew (S := K * K) (by simp [Matrix.transpose_mul, show Kᵀ = -K from hKskew]) hDEskew,
      frobInner_add_right, hCKD, hCKE]
    ring
  · rw [heV]
    have hvSq : frobSq (v t) = frobSq (C + K) := by
      dsimp only [v]
      unfold frobSq
      rw [frobInner_right_orthogonal (Qt t) (hP.mul hRt.2.1), frobInner_left_orthogonal (Lt t) hLt.2.1]
    have hKSq : frobSq K = frobSq Ω := by
      dsimp only [K]
      unfold frobSq
      rw [frobInner_right_orthogonal Pᵀ hP.transpose, frobInner_left_orthogonal P hP]
    have htot : frobSq (v t) = frobSq C + frobSq Ω := by
      rw [hvSq, frobSq_add, hdisj_zero hC.1 hKs (fun i => Or.inr (isSkew_diagonal_zero hKskew i)), hKSq]
      ring
    simpa only [frobSq, frobInner, sq] using htot

end GSPalomar
