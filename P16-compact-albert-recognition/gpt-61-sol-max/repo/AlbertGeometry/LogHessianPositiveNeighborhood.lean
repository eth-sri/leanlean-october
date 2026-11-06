/-
Continuity of the actual log-Hessian CLM and
finite-dimensional continuation of an explicitly positive base-point form.
No positivity is inferred merely from N > 0. Arbitrary homogeneous-polynomial
representation and the native norm dictionary remain separate obligations.
-/
module
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.GRewrite
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Aesop

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import AlbertGeometry.CubicHessian
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Normed.Operator.Bilinear

@[expose] public section

open scoped Topology
open Filter

namespace AlbertGeometry.Cubic
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def positiveDualEquiv [FiniteDimensional ℝ E] (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hp : ∀ u, u ≠ 0 → 0 < B u u) : E ≃L[ℝ] (E →L[ℝ] ℝ) := by
  have hinj : Function.Injective B := by
    refine (injective_iff_map_eq_zero B).2 ?_
    intro u hu
    by_contra hn
    have := hp u hn
    simp [hu] at this
  let d : Module.Dual ℝ E ≃ₗ[ℝ] (E →L[ℝ] ℝ) := LinearMap.toContinuousLinearMap
  exact (LinearEquiv.ofInjectiveOfFinrankEq B.toLinearMap hinj
    ((Subspace.dual_finrank_eq (K := ℝ) (V := E)).symm.trans d.finrank_eq)).toContinuousLinearEquiv

end
end AlbertGeometry.Cubic
