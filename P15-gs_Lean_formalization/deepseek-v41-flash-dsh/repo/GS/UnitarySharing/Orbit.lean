module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
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
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
public import Mathlib.Topology.Order.Compact
public import GS.CompactFibres
public import GS.ComplexAlgebra
public import GS.Continuation.AmbientProjection
public import GS.Continuation.ExponentialBasics
public import GS.Core
public import GS.Extensions.FiniteTopology
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
public import GS.LieAction.Action
public import GS.LieAction.BlockGroup
public import GS.OriginalLocalModel
public import GS.Projection
public import GS.Shuffle
public import GS.Unitary.CholeskySupport
public import GS.Unitary.Factorization
public import GS.Unitary.Frobenius
public import GS.Unitary.FrobeniusProjection
public import GS.Unitary.GeometryAlgebra
public import GS.Unitary.OrdinaryQR
public import GS.Unitary.Permutations
public import GS.Unitary.Projection
public import GS.Unitary.StructuredQR
public import GS.Unitary.Support
public import GS.UnitaryManifold.Action
public import GS.UnitaryManifold.BlockGroup
public import GS.UnitaryManifold.CayleyAlgebra
public import GS.UnitaryManifold.CayleyModel
public import GS.UnitaryManifold.CayleySmooth
public import GS.UnitarySharing.Algebra
public import GS.UnitarySharing.Factors


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The shared matrix family as a compact homogeneous space

The action is L X R*, with actual shared unitary factors and conjugate transpose R*.
Its orbit is
exactly the previously defined `InSharedA2Unitary` family.  Compactness gives a
homeomorphism from the genuine stabilizer quotient to the matrix subspace;
the orbit map is an open quotient map, also with continuous stabilizers.

These are topological statements.  They do not identify a smooth quotient or
replace the missing shared-orbit atlas by an assumed manifold structure.
-/

set_option autoImplicit false

noncomputable section
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold
namespace GS.UnitarySharing
variable {n : ℕ} {right left : Pattern n}

/-- Actual two-layer family with full within-layer unitary block sharing. -/
def InSharedA2Unitary (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P X : CMat n) : Prop :=
  ∃ L R : CMat n, SharedUnitaryFactor b₂ τ₂ L ∧
    SharedUnitaryFactor b₁ τ₁ R ∧ X = GS.UnitaryGeometry.product2 L P R

instance factorsMulAction (right left : Pattern n) :
    MulAction (Factors right left) (CMat n) where
  smul g X := Factor.matrix g.1 * X * (Factor.matrix g.2)ᴴ
  one_smul X := by
    change (1 : CMat n) * X * (1 : CMat n)ᴴ = X
    simp
  mul_smul g h X := by
    change (Factor.matrix g.1 * Factor.matrix h.1) * X *
      (Factor.matrix g.2 * Factor.matrix h.2)ᴴ =
      Factor.matrix g.1 * (Factor.matrix h.1 * X * (Factor.matrix h.2)ᴴ) *
        (Factor.matrix g.2)ᴴ
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

@[simp] theorem action_apply (g : Factors right left) (X : CMat n) :
    g • X = Factor.matrix g.1 * X * (Factor.matrix g.2)ᴴ := rfl

instance factorsContinuousSMul (right left : Pattern n) :
    ContinuousSMul (Factors right left) (CMat n) where
  continuous_smul := by
    change Continuous (fun p : Factors right left × CMat n =>
      Factor.matrix p.1.1 * p.2 * (Factor.matrix p.1.2)ᴴ)
    exact GS.UnitaryManifold.continuous_matrix_product
      (GS.UnitaryManifold.continuous_matrix_product
        (Factor.continuous_matrix.comp (continuous_fst.comp continuous_fst)) continuous_snd)
      (GS.UnitaryManifold.continuous_matrix_conjTranspose
        (Factor.continuous_matrix.comp (continuous_snd.comp continuous_fst)))

def orbitMap (right left : Pattern n) (P : CMat n) : Factors right left → CMat n :=
  fun g => g • P

abbrev MatrixOrbit (right left : Pattern n) (P : CMat n) :=
  ↥(MulAction.orbit (Factors right left) P)

abbrev PointStabilizer (right left : Pattern n) (P : CMat n) :=
  MulAction.stabilizer (Factors right left) P

abbrev OrbitCosets (right left : Pattern n) (P : CMat n) :=
  Factors right left ⧸ PointStabilizer right left P

theorem continuous_orbitMap (P : CMat n) : Continuous (orbitMap right left P) :=
  continuous_id.smul continuous_const

theorem orbit_iff_inShared (P X : CMat n) :
    X ∈ MulAction.orbit (Factors right left) P ↔
      InSharedA2Unitary right.size left.size right.label left.label P X := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨Factor.matrix g.1, (Factor.matrix g.2)ᴴ, Factor.matrix_shared g.1,
      shared_factor_conjTranspose (Factor.matrix_shared g.2), hg.symm⟩
  · rintro ⟨L, R, hL, hR, hX⟩
    refine ⟨(Factor.ofMatrix L hL, Factor.ofMatrix Rᴴ (shared_factor_conjTranspose hR)), ?_⟩
    simpa only [action_apply, Factor.matrix_ofMatrix, Matrix.conjTranspose_conjTranspose,
      GS.UnitaryGeometry.product2] using hX.symm

theorem orbit_set_eq_inShared (P : CMat n) :
    MulAction.orbit (Factors right left) P =
      {X | InSharedA2Unitary right.size left.size right.label left.label P X} := by
  ext X
  exact orbit_iff_inShared P X

def orbitMapToOrbit (right left : Pattern n) (P : CMat n) :
    Factors right left → MatrixOrbit right left P :=
  fun g => ⟨g • P, ⟨g, rfl⟩⟩

theorem continuous_orbitMapToOrbit (P : CMat n) :
    Continuous (orbitMapToOrbit right left P) :=
  (continuous_orbitMap P).subtype_mk _

theorem surjective_orbitMapToOrbit (P : CMat n) :
    Function.Surjective (orbitMapToOrbit right left P) := by
  rintro ⟨X, g, hg⟩
  exact ⟨g, Subtype.ext hg⟩

theorem action_cFrobInner (g : Factors right left) (X Y : CMat n) :
    cFrobInner (g • X) (g • Y) = cFrobInner X Y :=
  GS.UnitaryManifold.action_cFrobInner (g.1.val, g.2.val) X Y

/-- The same ambient linear isometry as for independent factors, restricted
to the actual shared subgroup. -/
def actionLinearEquiv (g : Factors right left) : CMat n ≃ₗ[ℝ] CMat n :=
  GS.UnitaryManifold.actionLinearEquiv (g.1.val, g.2.val)

theorem orbit_fibre_iff (P : CMat n) (g h : Factors right left) :
    orbitMap right left P g = orbitMap right left P h ↔
      g⁻¹ * h ∈ PointStabilizer right left P := by
  change g • P = h • P ↔ (g⁻¹ * h) • P = P
  constructor
  · intro he
    rw [mul_smul, ← he, inv_smul_smul]
  · intro he
    have he' := congrArg (fun X : CMat n => g • X) he
    have hh : h • P = g • P := by
      simpa only [mul_smul, smul_inv_smul] using he'
    exact hh.symm

theorem closed_of_orbit_preimage_closed (P : CMat n)
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

theorem orbit_saturation (P : CMat n) (s : Set (Factors right left)) :
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
theorem orbitMapToOrbit_isOpenMap (P : CMat n) :
    IsOpenMap (orbitMapToOrbit right left P) := by
  intro s hs
  have ho : IsOpen (orbitMapToOrbit right left P ⁻¹'
      (orbitMapToOrbit right left P '' s)) := by
    rw [orbit_saturation]
    exact isOpen_iUnion (fun h => hs.preimage (continuous_id.mul continuous_const))
  have hc := closed_of_orbit_preimage_closed P
    (orbitMapToOrbit right left P '' s)ᶜ (by simpa using ho.isClosed_compl)
  simpa using hc.isOpen_compl

end GS.UnitarySharing
