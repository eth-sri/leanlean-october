module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
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
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Real.Lemmas
public import GS.CayleyCharts.Algebra
public import GS.CayleyCharts.Model
public import GS.CayleyCharts.Smooth
public import GS.CompactFibres
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
public import GS.GlobalGeometry.BalancedLift
public import GS.OriginalLocalModel
public import GS.Projection
public import GS.Shuffle


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A globally defined, factorization-independent Cayley update with overlap

This file works in the original matrix type and the original InA2Orth set.
The update is defined from X and Z themselves, not a chosen pair of factors.
Its velocity is the already checked exact pointProjection. For tangent Z this
is Z. All denominators are invertible for ALL real step lengths, not only locally.
The map has a jointly smooth ambient extension. No manifold structure with
positive-dimensional stabilizer is silently assumed.

-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation GS.CayleyCharts
open scoped Topology
namespace GS.GlobalGeometry
variable {n : ℕ}

/-- This normalization has derivative +id at zero. -/
def unitCayley (A : Mat n) : Mat n := cayley ((-1/2 : ℝ) • A)

@[simp] theorem unitCayley_zero : unitCayley (0 : Mat n) = 1 := by
  simp [unitCayley]

theorem unitCayley_smooth_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E → Mat n) (hs : ContDiff ℝ ⊤ A) (hk : ∀ x, IsSkew (A x)) :
    ContDiff ℝ ⊤ (fun x => unitCayley (A x)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  change ContDiffAt ℝ ⊤ (fun y => cayley ((-1 / 2 : ℝ) • A y)) x
  apply smooth_cayley_comp_at (hs.contDiffAt.const_smul (-1 / 2 : ℝ))
  exact admissible_of_isSkew _ (isSkew_smul _ (hk x))

/-- Differentiate c(tA)(I+tA)=I-tA. No derivative of inverse is postulated. -/
theorem cayley_line_derivative (A : Mat n) (hk : IsSkew A) :
    HasDerivAt (fun t : ℝ => cayley (t • A)) ((-2 : ℝ) • A) 0 := by
  let f : ℝ → Mat n := fun t => cayley (t • A)
  have hsm : ContDiffAt ℝ ⊤ f 0 := by
    apply smooth_cayley_comp_at ((contDiffAt_id).smul contDiffAt_const)
    simpa using (admissible_zero : admissible (0 : Mat n))
  let V := deriv f 0
  have hd : HasDerivAt f V 0 := (hsm.differentiableAt (by simp)).hasDerivAt
  have hp : HasDerivAt (fun t : ℝ => (1 : Mat n) + t • A) A 0 := by
    simpa only [Pi.add_def, Pi.sub_def, zero_add, zero_sub, id_eq, one_smul] using (hasDerivAt_const (0 : ℝ) (1 : Mat n)).add
      ((hasDerivAt_id (0 : ℝ)).smul_const A)
  have hm : HasDerivAt (fun t : ℝ => (1 : Mat n) - t • A) (-A) 0 := by
    simpa only [Pi.add_def, Pi.sub_def, zero_add, zero_sub, id_eq, one_smul] using (hasDerivAt_const (0 : ℝ) (1 : Mat n)).sub
      ((hasDerivAt_id (0 : ℝ)).smul_const A)
  have he : (fun t : ℝ => f t * (1 + t • A)) =
      (fun t : ℝ => (1 : Mat n) - t • A) := by
    funext t
    exact cayley_mul _ (admissible_of_isSkew _ (isSkew_smul t hk))
  have hz := hasDerivAt_matrix_mul hd hp
  rw [he] at hz
  have hv : V + A = -A := by
    simpa [f] using hz.unique hm
  have hv' : V = (-2 : ℝ) • A := by
    ext i j
    have hh := congrFun (congrFun hv i) j
    change V i j = (-2 : ℝ) * A i j
    change V i j + A i j = -A i j at hh
    linarith
  simpa only [f, hv'] using hd

theorem unitCayley_line_derivative (A : Mat n) (hk : IsSkew A) :
    HasDerivAt (fun t : ℝ => unitCayley (t • A)) A 0 := by
  have hd := cayley_line_derivative ((-1/2 : ℝ) • A) (isSkew_smul _ hk)
  have hf : (fun t : ℝ => unitCayley (t • A)) =
      (fun t : ℝ => cayley (t • ((-1/2 : ℝ) • A))) := by
    funext t
    unfold unitCayley
    rw [smul_comm]
  rw [hf]
  simpa only [smul_smul, show (-2 : ℝ) * (-1/2) = 1 by norm_num, one_smul] using hd

end GS.GlobalGeometry
