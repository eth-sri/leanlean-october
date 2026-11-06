module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Matrix
public import GS.Unitary.Support
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace.Real

@[expose] public section


/-!
# The actual group of unitary block matrices

The topology is the ordinary subspace topology on complex matrices.
No manifold structure is assumed.
-/

noncomputable section
open Matrix
namespace GS.UnitaryManifold
open GS.UnitaryGeometry
variable {n : ℕ}

/-- Unitary matrices with the manuscript's exact zero pattern. -/
abbrev BlockU (block : Fin n → ℕ) :=
  {A : CMat n // CSupported block A ∧ Unitary A}

instance blockUGroup (block : Fin n → ℕ) : Group (BlockU block) where
  one := ⟨1, CSupported.one, GS.Unitary.one⟩
  mul A B := ⟨A.val * B.val, A.property.1.mul B.property.1,
    A.property.2.mul B.property.2⟩
  inv A := ⟨A.valᴴ, A.property.1.conjTranspose, A.property.2.conjTranspose⟩
  mul_assoc A B C := Subtype.ext (Matrix.mul_assoc A.val B.val C.val)
  one_mul A := Subtype.ext (Matrix.one_mul A.val)
  mul_one A := Subtype.ext (Matrix.mul_one A.val)
  inv_mul_cancel A := Subtype.ext A.property.2.1

@[simp] theorem blockU_one_val (block : Fin n → ℕ) :
    ((1 : BlockU block) : CMat n) = 1 := rfl



instance blockUCompactSpace (block : Fin n → ℕ) : CompactSpace (BlockU block) :=
  (isCompact_iff_compactSpace (s := {A : CMat n | CSupported block A ∧ Unitary A})).1 <| by
  refine (isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset
    ?_ fun A hA i j => by simpa using entry_norm_bound_of_unitary (Matrix.mem_unitaryGroup_iff.2 hA.2.2) i j
  simp only [CSupported, Unitary, Set.setOf_and, Set.setOf_forall]
  repeat' first | apply IsClosed.inter | apply isClosed_iInter; intro
  all_goals exact isClosed_eq (by fun_prop) (by fun_prop)


end GS.UnitaryManifold
