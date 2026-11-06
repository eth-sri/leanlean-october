module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
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
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Compact
public import GS.CayleyCharts.Algebra
public import GS.CayleyCharts.BlockCharts
public import GS.CayleyCharts.Model
public import GS.CayleyCharts.OrbitCharts
public import GS.CayleyCharts.Smooth
public import GS.CompactFibres
public import GS.Continuation.AmbientProjection
public import GS.Continuation.ExponentialBasics
public import GS.Continuation.ExponentialCurves
public import GS.Core
public import GS.Extensions.FiniteTopology
public import GS.Extensions.GeodesicNormal
public import GS.Extensions.MatrixCalculus
public import GS.Extensions.OriginalCompact
public import GS.Extensions.ProjectionSmooth
public import GS.Extensions.TransportedProjection
public import GS.Extensions.TwoFactorProjection
public import GS.Fibres
public import GS.Frobenius
public import GS.GeometryAlgebra
public import GS.GlobalGeometry.ExactSharing
public import GS.GlobalGeometry.FrobeniusProjection
public import GS.GlobalGeometry.SharedAlgebra
public import GS.GlobalGeometry.SharedDescent
public import GS.GlobalGeometry.SharedFactorCurves
public import GS.GlobalGeometry.SharedNormalEquations
public import GS.LieAction.Action
public import GS.LieAction.BlockGroup
public import GS.LieAction.Nonoverlap
public import GS.ManifoldCompletion.OrbitDifferential
public import GS.OriginalLocalModel
public import GS.Projection
public import GS.RiemannianCompletion.FrobeniusDual
public import GS.SharedGeometry.Algebra
public import GS.SharedGeometry.Factors
public import GS.Shuffle


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The shared matrix family as a compact homogeneous space

The action is L X R^T, with actual shared orthogonal factors.  Its orbit is
exactly the previously defined `InSharedA2Orth` family.  Compactness gives a
homeomorphism from the genuine stabilizer quotient to the matrix subspace;
the orbit map is an open quotient map, also with continuous stabilizers.

These are topological statements.  They do not identify a smooth quotient or
replace the missing shared-orbit atlas by an assumed manifold structure.
-/

set_option autoImplicit false

noncomputable section
open Matrix GS GS.GlobalGeometry
namespace GS.SharedGeometry
variable {n : ℕ} {right left : Pattern n}

instance factorsMulAction (right left : Pattern n) :
    MulAction (Factors right left) (Mat n) where
  smul g X := Factor.matrix g.1 * X * (Factor.matrix g.2)ᵀ
  one_smul X := by
    change (1 : Mat n) * X * (1 : Mat n)ᵀ = X
    simp
  mul_smul g h X := by
    change (Factor.matrix g.1 * Factor.matrix h.1) * X *
      (Factor.matrix g.2 * Factor.matrix h.2)ᵀ =
      Factor.matrix g.1 * (Factor.matrix h.1 * X * (Factor.matrix h.2)ᵀ) *
        (Factor.matrix g.2)ᵀ
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]

@[simp] theorem action_apply (g : Factors right left) (X : Mat n) :
    g • X = Factor.matrix g.1 * X * (Factor.matrix g.2)ᵀ := rfl

instance factorsContinuousSMul (right left : Pattern n) :
    ContinuousSMul (Factors right left) (Mat n) where
  continuous_smul := by
    change Continuous (fun p : Factors right left × Mat n =>
      Factor.matrix p.1.1 * p.2 * (Factor.matrix p.1.2)ᵀ)
    exact GS.LieAction.continuous_matrix_product
      (GS.LieAction.continuous_matrix_product
        (Factor.continuous_matrix.comp (continuous_fst.comp continuous_fst)) continuous_snd)
      (GS.LieAction.continuous_matrix_transpose
        (Factor.continuous_matrix.comp (continuous_snd.comp continuous_fst)))

def orbitMap (right left : Pattern n) (P : Mat n) : Factors right left → Mat n :=
  fun g => g • P

abbrev MatrixOrbit (right left : Pattern n) (P : Mat n) :=
  ↥(MulAction.orbit (Factors right left) P)

abbrev PointStabilizer (right left : Pattern n) (P : Mat n) :=
  MulAction.stabilizer (Factors right left) P

abbrev OrbitCosets (right left : Pattern n) (P : Mat n) :=
  Factors right left ⧸ PointStabilizer right left P

theorem continuous_orbitMap (P : Mat n) : Continuous (orbitMap right left P) :=
  continuous_id.smul continuous_const

theorem orbit_iff_inShared (P X : Mat n) :
    X ∈ MulAction.orbit (Factors right left) P ↔
      InSharedA2Orth right.size left.size right.label left.label P X := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨Factor.matrix g.1, (Factor.matrix g.2)ᵀ, Factor.matrix_shared g.1,
      shared_factor_transpose (Factor.matrix_shared g.2), hg.symm⟩
  · rintro ⟨L, R, hL, hR, hX⟩
    refine ⟨(Factor.ofMatrix L hL, Factor.ofMatrix Rᵀ (shared_factor_transpose hR)), ?_⟩
    simpa only [action_apply, Factor.matrix_ofMatrix, Matrix.transpose_transpose,
      product2] using hX.symm

theorem orbit_set_eq_inShared (P : Mat n) :
    MulAction.orbit (Factors right left) P =
      {X | InSharedA2Orth right.size left.size right.label left.label P X} := by
  ext X
  exact orbit_iff_inShared P X

def orbitMapToOrbit (right left : Pattern n) (P : Mat n) :
    Factors right left → MatrixOrbit right left P :=
  fun g => ⟨g • P, ⟨g, rfl⟩⟩

theorem continuous_orbitMapToOrbit (P : Mat n) :
    Continuous (orbitMapToOrbit right left P) :=
  (continuous_orbitMap P).subtype_mk _

theorem surjective_orbitMapToOrbit (P : Mat n) :
    Function.Surjective (orbitMapToOrbit right left P) := by
  rintro ⟨X, g, hg⟩
  exact ⟨g, Subtype.ext hg⟩

theorem action_frobInner (g : Factors right left) (X Y : Mat n) :
    frobInner (g • X) (g • Y) = frobInner X Y :=
  GS.LieAction.action_frobInner (g.1.val, g.2.val) X Y

/-- The same ambient linear isometry as for independent factors, restricted
to the actual shared subgroup. -/
def actionLinearEquiv (g : Factors right left) : Mat n ≃ₗ[ℝ] Mat n :=
  GS.LieAction.actionLinearEquiv (g.1.val, g.2.val)

theorem orbit_fibre_iff (P : Mat n) (g h : Factors right left) :
    orbitMap right left P g = orbitMap right left P h ↔
      g⁻¹ * h ∈ PointStabilizer right left P := by
  change g • P = h • P ↔ (g⁻¹ * h) • P = P
  constructor
  · intro he
    rw [mul_smul, ← he, inv_smul_smul]
  · intro he
    have he' := congrArg (fun X : Mat n => g • X) he
    have hh : h • P = g • P := by
      simpa only [mul_smul, smul_inv_smul] using he'
    exact hh.symm

theorem closed_of_orbit_preimage_closed (P : Mat n)
    (s : Set (MatrixOrbit right left P))
    (hs : IsClosed (orbitMapToOrbit right left P ⁻¹' s)) : IsClosed s := by
  have he : s = orbitMapToOrbit right left P '' (orbitMapToOrbit right left P ⁻¹' s) := by
    ext x
    constructor
    · intro hx
      obtain ⟨g, rfl⟩ := surjective_orbitMapToOrbit P x
      exact ⟨g, hx, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact hg
  rw [he]
  exact (hs.isCompact.image (continuous_orbitMapToOrbit P)).isClosed

theorem orbit_saturation (P : Mat n) (s : Set (Factors right left)) :
    orbitMapToOrbit right left P ⁻¹' (orbitMapToOrbit right left P '' s) =
      ⋃ h : PointStabilizer right left P,
        (fun g : Factors right left => g * h.val) ⁻¹' s := by
  ext g
  constructor
  · rintro ⟨h, hh, he⟩
    have hf : orbitMap right left P g = orbitMap right left P h :=
      (congrArg Subtype.val he).symm
    let k : PointStabilizer right left P := ⟨g⁻¹ * h, (orbit_fibre_iff P g h).mp hf⟩
    apply Set.mem_iUnion.mpr
    refine ⟨k, ?_⟩
    change g * (g⁻¹ * h) ∈ s
    simpa only [mul_inv_cancel_left] using hh
  · intro hg
    obtain ⟨h, hh⟩ := Set.mem_iUnion.mp hg
    refine ⟨g * h.val, hh, ?_⟩
    apply Subtype.ext
    change (g * h.val) • P = g • P
    rw [mul_smul, show h.val • P = P from h.property]

/-- Images of factor neighbourhoods are orbit neighbourhoods.  No continuous
or smooth section of the orbit map is asserted by this openness result. -/
theorem orbitMapToOrbit_isOpenMap (P : Mat n) :
    IsOpenMap (orbitMapToOrbit right left P) := by
  intro s hs
  have ho : IsOpen (orbitMapToOrbit right left P ⁻¹'
      (orbitMapToOrbit right left P '' s)) := by
    rw [orbit_saturation]
    exact isOpen_iUnion (fun h => hs.preimage (continuous_id.mul continuous_const))
  have hc := closed_of_orbit_preimage_closed P
    (orbitMapToOrbit right left P '' s)ᶜ (by simpa using ho.isClosed_compl)
  simpa using hc.isOpen_compl

end GS.SharedGeometry
