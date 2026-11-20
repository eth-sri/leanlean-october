module
public import Glennie.Compact.ExactCoordinates
public import Glennie.Compact.Rank20Reduction
public import Glennie.Compact.FlatBase
public import Mathlib.Algebra.QuadraticAlgebra.Basic
meta import Mathlib.Algebra.QuadraticAlgebra.Basic
meta import Glennie.Compact.FlowFamily
meta import Glennie.Compact.ExactCoordinates
meta import Glennie.Compact.FlatBase

/-! Evaluate the derivative in the exact ring ℚ[√3]. All operations used in the
Jacobian commute with its real realization. A single matrix multiplication in
this ring certifies all twenty columns at once. -/
@[expose] public section
namespace Glennie.Compact.NativeFlatRank20
open Glennie.Exact FlatBase FlowFamily

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 2000

private theorem axis_real : realize φ axis = realize (RingHom.id ℝ) axis := by
  ext <;> simp [axis, realize, mapQ, mapO]
private theorem partner_real (n : Fin 20) : realize φ (partner n) = realize (RingHom.id ℝ) (partner n) := by
  ext <;> simp [partner, realize, mapQ, mapO, apply_ite φ]

def differential (n : Fin 20) (i : Fin 3) :=
  let t := axis; let b := partner n; let v := atoms (contextIndex n) i
  j t (j b v) - j b (j t v)
def speeds (n : Fin 20) (i : Fin 3) : A K := ((eval% Array.ofFn fun k => Array.ofFn (differential k))[n.val]!)[i.val]!
private theorem check_speeds : speeds = differential := by
  funext a i; fin_cases a <;> fin_cases i <;> decide +kernel

def velocity (n : Fin 20) (a i : Fin 3) := if a = contextIndex n then speeds n i else 0
private theorem velocity_real (n : Fin 20) (a i : Fin 3) :
    realize φ (velocity n a i) = atomTangent T n a i := by
  by_cases h : a = contextIndex n <;> simp [velocity, atomTangent, step, h, direction, check_speeds,
    differential, innerDerLinear_apply, innerDer, realize_prod _ _ cast_half, atoms_real, axis_real, partner_real, j]

def entry (r n : Fin 20) : K :=
  let (i,k,l) := rowIndex r
  pairing (velocity n 0 i) (pairs 0 k l) + pairing (velocity n 1 k) (pairs 1 l i) +
    pairing (velocity n 2 l) (pairs 2 i k)

theorem jacobian_exact : Matrix.of (jacobianEntry T) = (Matrix.of entry).map φ := by
  ext r n
  have h (x y : Albert) : trace (jordan x y) = inner x y := rfl
  simp only [Matrix.map_apply, Matrix.of_apply, jacobianEntry, trace_add, h, entry,
    map_add, cast_pairing, check_pairs, pairAt, j, realize_prod _ _ cast_half, atoms_real, velocity_real]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (inner_jordan_associative ..) ?_) (inner_comm ..)
  rw [jordan_comm (T 0 _), inner_jordan_associative, jordan_comm (T 0 _)]; rfl

def reciprocal (x : K) : K :=
  let d := x.re^2 - 3*x.im^2
  ⟨x.re/d, -x.im/d⟩

def jac : Matrix (Fin 20) (Fin 20) K := unpack (eval% pack (Matrix.of entry))
def invJac : Matrix (Fin 20) (Fin 20) K := unpack (eval% pack (inverseCandidate reciprocal jac))

end Glennie.Compact.NativeFlatRank20
