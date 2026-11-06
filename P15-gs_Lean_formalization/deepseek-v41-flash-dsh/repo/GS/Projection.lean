module
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import GS.Core
public import GS.Frobenius


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Frobenius projections in the two-factor calculation

Theorems concern the explicit linear spaces of supported skew matrices. The
identification of these spaces with a manifold tangent bundle is a SEPARATE
obligation in `Specifications.lean`.

-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def IsSkew (A : Matrix ι ι ℝ) : Prop := Aᵀ = -A

def skew (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => (A i j - A j i) / 2

/-- Support masks are predicates on ordered pairs, not matrix inverses. -/
def mask (p : ι → ι → Prop) [DecidableRel p] (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => if p i j then A i j else 0

theorem isSkew_diagonal_zero {A : Matrix ι ι ℝ} (hA : IsSkew A) (i : ι) :
    A i i = 0 := by
  have he : A i i = -A i i := congrFun (congrFun hA i) i
  linarith

end GS
