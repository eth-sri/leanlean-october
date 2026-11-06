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
public import Mathlib.Topology.Homeomorph.Lemmas
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
public import GS.Nonmanifold.NormalizationEstimates
public import GS.Nonmanifold.OriginalCompactModel
public import GS.Nonmanifold.OriginalModelCoordinates
public import GS.Nonmanifold.RankOneGeometry
public import GS.Nonmanifold.SkewCoordinates
public import GS.NonmanifoldCompletion.BaseFibreGauges
public import GS.NonmanifoldCompletion.BlockExtraction
public import GS.NonmanifoldCompletion.BlockRealization
public import GS.NonmanifoldCompletion.FactorSpace
public import GS.NonmanifoldCompletion.FullFibreCoverage
public import GS.NonmanifoldCompletion.LocalAngles
public import GS.NonmanifoldCompletion.OriginalCoordinates
public import GS.NonmanifoldCompletion.OriginalMembership
public import GS.NonmanifoldCompletion.SmallLogarithms
public import GS.NonmanifoldCompletion.SpectralTwo
public import GS.OriginalLocalModel
public import GS.Projection
public import GS.Shuffle
public import GS.Specifications
public import GS.ThreeFactor


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A pointed homeomorphism of neighbourhoods of the FULL GS family

The source contains a neighbourhood in localFamily itself. The target contains a neighbourhood in
the independent skew-coordinate cone model. Both neighbourhood claims are
proved using full-fibre coverage and estimates for the g map.

Neighbourhoods are not asserted to be open: the source and target may be the
compact images. A homeomorphism of these neighbourhoods is an equivalence of
the pointed local topological spaces. A final EuclideanAtSubset contradiction
still needs the topological cone obstruction and a restriction/transport lemma.

-/
noncomputable section
open Matrix Filter GS GS.Extensions GS.Continuation GS.Nonmanifold
open scoped Topology
namespace GS.NonmanifoldCompletion

/-- Explicit pointed homeomorphism between neighbourhood subsets. -/
structure PointedNeighbourhoodModel (X Y : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] (x : X) (y : Y) where
  source : Set X
  target : Set Y
  source_nhds : source ∈ 𝓝 x
  target_nhds : target ∈ 𝓝 y
  chart : ↥source ≃ₜ ↥target
  map_point : ∀ hx : x∈source, (chart ⟨x,hx⟩).val = y

def familyBase {q : ℕ} (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀) : ↥(localFamily q) :=
  ⟨basePoint Q₀,basePoint_mem_localFamily Q₀ hQ₀⟩

def compactSourceInFamily {q : ℕ} (Q₀ : Mat q) (η : ℝ) : Set ↥(localFamily q) :=
  {M | M.val ∈ OriginalFImage Q₀ η}

/-- The two presentations of the same F-image have the same induced topology. -/
def compactSourceHomeomorph {q : ℕ} (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀) (η : ℝ) :
    ↥(compactSourceInFamily Q₀ η) ≃ₜ OriginalFImage Q₀ η where
  toFun M := ⟨M.val.val,M.property⟩
  invFun M := ⟨⟨M.val,by
    obtain ⟨p,he⟩ := M.property
    rw [← he]
    exact originalF_mem_of_mem_K Q₀ hQ₀ p.property⟩,M.property⟩
  left_inv M := by apply Subtype.ext; rfl
  right_inv M := by apply Subtype.ext; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The selected F-image is now a neighbourhood in the FULL family subtype. -/
theorem compactSource_mem_nhds {q : ℕ} (hq : 0<q) (Q₀ : Mat q)
    (hQ₀ : Orthogonal Q₀) (hentries : ∀ i j, Q₀ i j≠0) (η : ℝ) (hη : 0<η) :
    compactSourceInFamily Q₀ η ∈ 𝓝 (familyBase Q₀ hQ₀) := by
  obtain ⟨W,hW,hbase,hcover⟩ := exists_open_original_local_coverage hq Q₀ hQ₀ hentries η hη
  let U : Set ↥(localFamily q) := Subtype.val ⁻¹' W
  have hU : IsOpen U := hW.preimage continuous_subtype_val
  have hb : familyBase Q₀ hQ₀ ∈ U := hbase
  apply Filter.mem_of_superset (hU.mem_nhds hb)
  intro M hM
  obtain ⟨p,hp,he⟩ := hcover M.val M.property hM
  exact ⟨⟨p,hp⟩,he⟩

/-- The complete local model, with neither side's neighbourhood claim assumed.
It is still NOT the topological nonmanifold theorem. -/
theorem original_pointed_neighbourhood_model {q : ℕ} (hq : 0<q)
    (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀) (hentries : ∀ i j, Q₀ i j≠0) :
    Nonempty (PointedNeighbourhoodModel ↥(localFamily q) (ModelCoordinates q)
      (familyBase Q₀ hQ₀) (modelCoordinatesZero q)) := by
  obtain ⟨η,hη,h,hcomm,hpoint,U,hU,hzero,hsub⟩ :=
    exists_original_compact_model_homeomorphism hq Q₀ hQ₀ hentries
  refine ⟨{
    source := compactSourceInFamily Q₀ η
    target := Set.range (@independentG q η)
    source_nhds := compactSource_mem_nhds hq Q₀ hQ₀ hentries η hη
    target_nhds := Filter.mem_of_superset (hU.mem_nhds hzero) hsub
    chart := (compactSourceHomeomorph Q₀ hQ₀ η).trans h
    map_point := ?_ }⟩
  intro hx
  have he : compactSourceHomeomorph Q₀ hQ₀ η ⟨familyBase Q₀ hQ₀,hx⟩ =
      originalFImageBase Q₀ η hη.le := by
    apply Subtype.ext
    rfl
  change (h (compactSourceHomeomorph Q₀ hQ₀ η ⟨familyBase Q₀ hQ₀,hx⟩)).val = _
  rw [he]
  exact hpoint

end GS.NonmanifoldCompletion
