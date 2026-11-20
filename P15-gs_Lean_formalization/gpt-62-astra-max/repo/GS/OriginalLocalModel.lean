module

public import GS.CompactFibres
public import GS.Core
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic.FunProp
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Original local parameterization (definitions and elementary identities)

This file follows the manuscript's original variables ell, r, c, z, u.
No claim of a smooth manifold structure is used to define the maps. The hard
analytic statements about normalization, fibres, and local coverage remain
explicit goals in Specifications.lean.

-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS

/-- Perfect shuffle with the scalar row-major convention of the manuscript. -/
def scalarShuffle (k b : ℕ) : Equiv.Perm (Fin (k*b)) :=
  (finProdFinEquiv.symm.trans (Equiv.prodComm (Fin k) (Fin b))).trans
    (finProdFinEquiv.trans (Equiv.cast (congrArg Fin (Nat.mul_comm b k))))

def localFamily (q : ℕ) : Set (Mat (q*2)) :=
  let P := permMatrix (scalarShuffle q 2)
  {M | InA3Orth 2 q 2 P Pᵀ M}

def basePoint {q : ℕ} (Q₀ : Mat q) : Mat (q*2) := fun i j =>
  let ri : Fin q × Fin 2 := finProdFinEquiv.symm i
  let rj : Fin q × Fin 2 := finProdFinEquiv.symm j
  Q₀ ri.1 rj.1 * (1 : Mat 2) ri.2 rj.2

/-- Exact local Euclidean-chart property in the induced topology.
The target may be any open Euclidean set; it is not restricted to round balls. -/
def EuclideanAtSubset {X : Type*} [TopologicalSpace X] (S : Set X) (x : X) : Prop :=
  x ∈ S ∧ ∃ (U : Set X), IsOpen U ∧ x ∈ U ∧
    ∃ (d : ℕ) (V : Set (EuclideanSpace ℝ (Fin d))), IsOpen V ∧
      Nonempty (↥(S ∩ U) ≃ₜ ↥V)

end GS
