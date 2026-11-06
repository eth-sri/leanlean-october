module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Basic.Real.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
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
public import Mathlib.Topology.Order.Compact
public import GS.CayleyCharts.Algebra
public import GS.CayleyCharts.BlockCharts
public import GS.CayleyCharts.Model
public import GS.CayleyCharts.OrbitCharts
public import GS.CayleyCharts.Smooth
public import GS.CompactFibres
public import GS.Continuation.AmbientProjection
public import GS.Core
public import GS.Extensions.GeodesicNormal
public import GS.Extensions.MatrixCalculus
public import GS.Extensions.ProjectionSmooth
public import GS.Extensions.TransportedProjection
public import GS.Extensions.TwoFactorProjection
public import GS.Frobenius
public import GS.GeometryAlgebra
public import GS.LieAction.Action
public import GS.LieAction.BlockGroup
public import GS.LieAction.Nonoverlap
public import GS.Projection
public import GS.Shuffle


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Coordinate differential of the orbit inclusion

We differentiate the actual Cayley formula. Its derivative is not defined by
fiat. At the centre, the derivative of cayley is -2 times the identity; the
right transpose changes that sign. In the no-overlap case the Frobenius
identity gives an injective differential. The exact range equals the checked
TwoFactorDirection predicate.

This is a coordinate fderiv theorem. The mfderiv/TangentSpace bridge is in
TangentBridge.lean. No IsImmersion predicate is redefined here.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.LieAction GS.CayleyCharts GS.Extensions Filter Set
open scoped Topology Manifold
namespace GS.ManifoldCompletion
variable {n : ℕ} {block block₁ block₂ : Fin n → ℕ}

/-- Obtain the derivative from the identity c(A)(1+A)=1-A, rather than using
an unverified formula for differentiation of matrix inverse. -/
theorem chartInv_line_hasDerivAt_zero (Q : BlockO block) (v : Model block) :
    HasDerivAt (fun t : ℝ => chartInv Q (t • v)) ((-2 : ℝ) • (Q.val * v.val)) 0 := by
  let V := fderiv ℝ (chartInv Q) 0 v
  have hd : HasDerivAt (fun t : ℝ => chartInv Q (t • v)) V 0 := by
    have hi := ((chartInv_smooth Q).differentiable (by simp) 0).hasFDerivAt
    have hl : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    exact hi.comp_hasDerivAt_of_eq 0 hl (by simp)
  have hp : HasDerivAt (fun t : ℝ => (1 : Mat n) + t • v.val) v.val 0 := by
    simpa only [Pi.add_def, id_eq, zero_add, one_smul] using (hasDerivAt_const (0 : ℝ) (1 : Mat n)).add
      ((hasDerivAt_id (0 : ℝ)).smul_const v.val)
  have hm : HasDerivAt (fun t : ℝ => (1 : Mat n) - t • v.val) (-v.val) 0 := by
    simpa only [Pi.sub_def, id_eq, zero_sub, one_smul] using (hasDerivAt_const (0 : ℝ) (1 : Mat n)).sub
      ((hasDerivAt_id (0 : ℝ)).smul_const v.val)
  have hleft := hasDerivAt_matrix_mul hd hp
  have hright := hasDerivAt_matrix_mul (hasDerivAt_const (0 : ℝ) Q.val) hm
  have hid : (fun t : ℝ => chartInv Q (t • v) * (1 + t • v.val)) =
      (fun t : ℝ => Q.val * (1 - t • v.val)) := by
    funext t
    change Q.val * cayley ((t • v).val) * (1 + (t • v).val) = _
    rw [Matrix.mul_assoc, cayley_mul _ (admissible_model (t • v))]
    rfl
  rw [hid] at hleft
  have hv : V + Q.val * v.val = -(Q.val * v.val) := by
    simpa only [zero_smul, add_zero, sub_zero, chartInv_zero, Matrix.mul_one,
      Matrix.zero_mul, zero_add, Matrix.mul_neg] using hleft.unique hright
  have he : V = (-2 : ℝ) • (Q.val * v.val) := by
    ext i j
    have hh := congrFun (congrFun hv i) j
    change V i j + (Q.val * v.val) i j = -(Q.val * v.val) i j at hh
    change V i j = (-2 : ℝ) * (Q.val * v.val) i j
    linarith
  rwa [he] at hd

/-- Translate the factor-side injectivity condition into the original
left-coordinate disjoint-support condition. -/
theorem noOverlap_offDiagonalDisjoint (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) :
    OffDiagonalDisjoint block₂ (block₁ ∘ σ.symm) := by
  intro i j h₂ h₁
  apply σ.symm.injective
  apply hn
  apply Prod.ext
  · exact h₁
  · simpa only [Equiv.apply_symm_apply] using h₂

end GS.ManifoldCompletion
