module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Star
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
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.IsManifold.Basic
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
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
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
public import GS.UnitaryManifold.CayleyCharts
public import GS.UnitaryManifold.CayleyDifferential
public import GS.UnitaryManifold.CayleyModel
public import GS.UnitaryManifold.CayleySmooth
public import GS.UnitaryManifold.Factors
public import GS.UnitaryManifold.KernelCayley
public import GS.UnitaryManifold.MatrixCalculus
public import GS.UnitarySharing.Algebra
public import GS.UnitarySharing.Directions
public import GS.UnitarySharing.FactorCharts
public import GS.UnitarySharing.Factors
public import GS.UnitarySharing.Orbit


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The actual shared orbit differential and its stabilizer kernel

Differentiate the concrete Cayley factor parametrization, retaining the -2
and +2 coefficients of the existing Cayley convention.  Its range is exactly
the point-based shared direction space.  At the identity, its entire kernel
integrates to the actual shared stabilizer; conversely every stabilizer element
in this Cayley chart comes from that kernel.

These are coordinate differentials of an actual smooth factor map.  No atlas
or manifold tangent space on its orbit image is introduced in this module.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold
open scoped Topology Manifold
namespace GS.UnitarySharing
variable {n : ℕ} {right left : Pattern n}

/-- Total reconstruction in the genuine shared product group. -/
def factorLift (g : Factors right left) (v : PairGenerator right left) :
    Factors right left := (reconstruct g.1 v.1, reconstruct g.2 v.2)

@[simp] theorem factorLift_zero (g : Factors right left) : factorLift g 0 = g := by
  exact Prod.ext (reconstruct_zero g.1) (reconstruct_zero g.2)

theorem continuous_factorLift (g : Factors right left) : Continuous (factorLift g) :=
  ((continuous_reconstruct g.1).comp continuous_fst).prodMk
    ((continuous_reconstruct g.2).comp continuous_snd)

/-- Matrix formula on the whole shared coordinate model. -/
def orbitParam (g : Factors right left) (P : CMat n) (v : PairGenerator right left) :
    CMat n := factorLift g v • P

@[simp] theorem orbitParam_zero (g : Factors right left) (P : CMat n) :
    orbitParam g P 0 = g • P := by simp only [orbitParam, factorLift_zero]

theorem orbitParam_smooth (g : Factors right left) (P : CMat n) :
    ContDiff ℝ ⊤ (orbitParam g P) := by
  apply contDiff_iff_contDiffAt.mpr
  intro v
  change ContDiffAt ℝ ⊤ (fun w : PairGenerator right left =>
    Factor.matrix (reconstruct g.1 w.1) * P *
      (Factor.matrix (reconstruct g.2 w.2))ᴴ) v
  exact smooth_mul_at
    (smooth_mul_at ((reconstruct_matrix_smooth g.1).contDiffAt.comp v contDiffAt_fst)
      contDiffAt_const)
    (smooth_conjTranspose_at ((reconstruct_matrix_smooth g.2).contDiffAt.comp v contDiffAt_snd))

/-- Reuse the checked ambient Cayley derivative without changing its proof. -/
theorem reconstruct_line_hasDerivAt_zero {s : Pattern n} (Q : Factor s)
    (v : Generator s) :
    HasDerivAt (fun t : ℝ => Factor.matrix (reconstruct Q (t • v)))
      ((-2 : ℝ) • (Factor.matrix Q * v.val)) 0 :=
  GS.UnitaryManifold.chartInv_line_hasDerivAt_zero Q.val
    ⟨v.val, v.property.1, v.property.2.1⟩

/-- True Frechet derivative at the centre, not a definition of a differential. -/
theorem orbitParam_fderiv_zero (g : Factors right left) (P : CMat n)
    (v : PairGenerator right left) :
    fderiv ℝ (orbitParam g P) 0 v =
      GS.UnitaryGeometry.tangentParam (Factor.matrix g.1) P (Factor.matrix g.2)ᴴ
        ((-2 : ℝ) • v.1.val) ((2 : ℝ) • v.2.val) := by
  have hdL := reconstruct_line_hasDerivAt_zero g.1 v.1
  have hdR := GS.UnitaryManifold.hasDerivAt_matrix_conjTranspose (reconstruct_line_hasDerivAt_zero g.2 v.2)
  have ht : ((-2 : ℝ) • (Factor.matrix g.2 * v.2.val))ᴴ =
      (2 : ℝ) • (v.2.val * (Factor.matrix g.2)ᴴ) := by
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_mul, v.2.property.2.1,
      Matrix.neg_mul, smul_neg, ← neg_smul]
    norm_num
  rw [ht] at hdR
  have hactual := hasDerivAt_product2 P hdL hdR
  have hi := ((orbitParam_smooth g P).differentiable (by simp) 0).hasFDerivAt
  have hcomputed := hi.comp_hasDerivAt_of_eq 0
    ((hasDerivAt_id (0 : ℝ)).smul_const v) (by simp)
  have ha : HasDerivAt (fun t : ℝ => orbitParam g P (t • v))
      (GS.UnitaryGeometry.tangentParam (Factor.matrix g.1) P (Factor.matrix g.2)ᴴ
        ((-2 : ℝ) • v.1.val) ((2 : ℝ) • v.2.val)) 0 := by
    simpa only [orbitParam, factorLift, action_apply, GS.UnitaryGeometry.product2, zero_smul,
      reconstruct_zero, GS.UnitaryGeometry.tangentParam, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_assoc, Prod.smul_fst, Prod.smul_snd] using hactual
  simpa only [one_smul] using hcomputed.unique ha

/-- The actual coordinate differential has the full tied generator range. -/
theorem orbitParam_fderiv_zero_range (g : Factors right left) (P Y : CMat n) :
    (∃ v : PairGenerator right left, fderiv ℝ (orbitParam g P) 0 v = Y) ↔
      Y ∈ pointDirections right left (g • P) := by
  change (∃ v : PairGenerator right left, fderiv ℝ (orbitParam g P) 0 v = Y) ↔
    Y ∈ pointDirections right left (GS.UnitaryGeometry.product2 (Factor.matrix g.1) P (Factor.matrix g.2)ᴴ)
  rw [← sharedDirection_iff_pointDirections P (Factor.matrix g.1)
    (Factor.matrix g.2)ᴴ Y (Factor.matrix_shared g.1)
    (shared_factor_conjTranspose (Factor.matrix_shared g.2))]
  constructor
  · rintro ⟨v, rfl⟩
    rw [orbitParam_fderiv_zero]
    let C : Generator left := (-2 : ℝ) • v.1
    let Ω : Generator right := (2 : ℝ) • v.2
    exact ⟨C.val, C.property, Ω.val, Ω.property, rfl⟩
  · rintro ⟨C, hC, Ω, hΩ, hY⟩
    let c : Generator left := ⟨C, hC⟩
    let w : Generator right := ⟨Ω, hΩ⟩
    refine ⟨((-1 / 2 : ℝ) • c, (1 / 2 : ℝ) • w), ?_⟩
    rw [orbitParam_fderiv_zero, hY]
    change GS.UnitaryGeometry.tangentParam (Factor.matrix g.1) P (Factor.matrix g.2)ᴴ
      ((-2 : ℝ) • ((-1 / 2 : ℝ) • C)) ((2 : ℝ) • ((1 / 2 : ℝ) • Ω)) = _
    norm_num [smul_smul, GS.UnitaryGeometry.tangentParam]

theorem orbitParam_kernel_iff_intertwine (P : CMat n) (v : PairGenerator right left) :
    fderiv ℝ (orbitParam (1 : Factors right left) P) 0 v = 0 ↔
      v.1.val * P = P * v.2.val := by
  rw [orbitParam_fderiv_zero]
  change GS.UnitaryGeometry.tangentParam (1 : CMat n) P (1 : CMat n)ᴴ
    ((-2 : ℝ) • v.1.val) ((2 : ℝ) • v.2.val) = 0 ↔ _
  simp only [GS.UnitaryGeometry.tangentParam, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul]
  constructor
  · intro h
    have hz : (-2 : ℝ) • (v.1.val * P - P * v.2.val) = 0 := by
      simpa only [smul_sub, sub_eq_add_neg, smul_add, smul_neg,
        neg_smul, neg_add_rev, neg_neg] using h
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (by norm_num))
  · intro h
    rw [h, ← add_smul]
    norm_num

/-- Both implications hold for the entire Cayley parameter domain.  Thus the
continuous shared stabilizer is handled by its true linear kernel in this chart. -/
theorem factorLift_stabilizes_iff_kernel (P : CMat n) (v : PairGenerator right left) :
    factorLift (1 : Factors right left) v • P = P ↔
      fderiv ℝ (orbitParam (1 : Factors right left) P) 0 v = 0 := by
  rw [orbitParam_kernel_iff_intertwine]
  have hA := admissible_of_isSkew v.1.val v.1.property.2.1
  have hB := admissible_of_isSkew v.2.val v.2.property.2.1
  have ho := cayley_unitary v.2.val v.2.property.2.1 hB
  simp only [factorLift, action_apply, reconstruct_matrix, Prod.fst_one, Prod.snd_one, Factor.matrix_one,
    Matrix.one_mul]
  change cayley v.1.val * P * (cayley v.2.val)ᴴ = P ↔ _
  constructor
  · intro h
    have he := congrArg (fun Y : CMat n => Y * cayley v.2.val) h
    have hi : cayley v.1.val * P = P * cayley v.2.val := by
      simpa only [Matrix.mul_assoc, ho.1, Matrix.mul_one] using he
    have hc := GS.UnitaryManifold.cayley_intertwine
      (cayley v.1.val) (cayley v.2.val) P
      (admissible_cayley v.1.val hA) (admissible_cayley v.2.val hB) hi
    simpa only [cayley_involutive v.1.val hA, cayley_involutive v.2.val hB] using hc
  · intro h
    rw [GS.UnitaryManifold.cayley_intertwine v.1.val v.2.val P hA hB h,
      Matrix.mul_assoc, ho.2, Matrix.mul_one]

end GS.UnitarySharing
