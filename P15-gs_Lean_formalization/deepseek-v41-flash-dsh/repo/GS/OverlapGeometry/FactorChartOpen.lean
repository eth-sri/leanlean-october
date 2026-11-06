module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Basic.Real.Basic
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
public import GS.Core
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
# Openness of factor charts and horizontal slice images

The inverse Cayley chart is an open map on the whole supported-skew model.
The final lemma transfers openness through a local product chart whenever its
second coordinate leaves the projected image unchanged. It is used for the
horizontal/stabilizer decomposition of an orbit with overlap.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.LieAction GS.CayleyCharts Set

namespace GS.OverlapGeometry

variable {n : ℕ} {block block₁ block₂ : Fin n → ℕ}

/-- A local product chart descends to open slice images when the projection is
constant in the second coordinate. Only a representative above every point of
the first-coordinate domain is needed. -/
theorem isOpen_slice_image_of_productChart
    {H K M X : Type*} [TopologicalSpace H] [TopologicalSpace K]
    [TopologicalSpace M] [TopologicalSpace X]
    (e : OpenPartialHomeomorph (H × K) M) (q : M → X) (p : H → X)
    (hq : IsOpenMap q)
    (heq : ∀ z ∈ e.source, q (e z) = p z.1)
    (U : Set H) (hU : IsOpen U)
    (hcover : ∀ h ∈ U, ∃ k : K, (h, k) ∈ e.source) :
    IsOpen (p '' U) := by
  let V : Set (H × K) := e.source ∩ Prod.fst ⁻¹' U
  have hV : IsOpen V := e.open_source.inter (hU.preimage continuous_fst)
  have hopen : IsOpen (q '' (e '' V)) :=
    hq _ (e.isOpen_image_of_subset_source hV inter_subset_left)
  have himage : q '' (e '' V) = p '' U := by
    ext x
    constructor
    · rintro ⟨m, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z.1, hz.2, (heq z hz.1).symm⟩
    · rintro ⟨h, hh, rfl⟩
      obtain ⟨k, hk⟩ := hcover h hh
      exact ⟨e (h, k), ⟨(h, k), ⟨hk, hh⟩, rfl⟩, heq (h, k) hk⟩
  rwa [himage] at hopen

end GS.OverlapGeometry
