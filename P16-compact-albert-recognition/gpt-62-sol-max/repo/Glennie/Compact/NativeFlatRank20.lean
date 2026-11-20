module
public import Glennie.Compact.Rank20Reduction
meta import Glennie.Compact.FlowFamily
meta import Glennie.Compact.FlatBase
public import Glennie.Compact.FlatBase
public import Mathlib.Data.ZMod.Basic
meta import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Glennie.ExactCoordinates
meta import Glennie.ExactCoordinates
public import Glennie.MatrixCertificate
meta import Glennie.MatrixCertificate
import Mathlib.Tactic.Eval
@[expose] public section
namespace Glennie.Compact.NativeFlatRank20
attribute [local ext] ExactCoordinates.Coords
open ExactCoordinates FlatBase FlowFamily NativeDictionary
open scoped QuadraticAlgebra Quaternion

private theorem lift_injective : Function.Injective sqrt3Map := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  change x.re • (1 : ℝ) + x.im • Real.sqrt 3 = 0 at hx
  simp only [zsmul_eq_mul, mul_one] at hx
  have hi : x.im = 0 := by
    by_contra hn
    apply Nat.prime_three.irrational_sqrt
    refine ⟨-(x.re : ℚ) / (x.im : ℚ), ?_⟩
    push_cast
    apply (div_eq_iff (by exact_mod_cast hn)).2
    linarith
  simp [hi] at hx
  exact QuadraticAlgebra.ext (by exact_mod_cast hx) hi

variable {R S : Type*} [CommRing R] [CommRing S]

-- Left multiplication by diag(1, −1, 0) in the doubled product.
private def ld (x : Coords R) : Coords R :=
  ⟨2*x.d0, -2*x.d1, 0, 0, x.o02, (-1 : R) • x.o12⟩

private theorem product_diag (x : Coords R) : doubled (basisVector 1) x = ld x := by
  ext <;> simp [product, ld, basisVector, extUnit, unflatten, dot, mulOct, conjOct, smul_eq_mul] 

private def tangent (s : R) (n : Fin 20) (i : Fin 3) : Coords R :=
  let b := basisVector (partnerIndex n)
  let x := scaledFrame s (contextIndex n) i
  ld (doubled b x) - doubled b (ld x)

@[simp] private theorem realize_tangent (n : Fin 20) (i : Fin 3) :
    realize sqrt3Map (tangent ω n i) = (144 : ℝ) •
      direction n (flatBase (contextIndex n) i) := by
  norm_num [tangent, ← product_diag, direction, innerDerLinear_apply, innerDer,
    jordan_smul_right, smul_smul, smul_sub]

private def pairing (x y : Coords R) : R := tr (doubled x y)

private def entries (s : R) : Matrix (Fin 20) (Fin 20) R :=
  ledgerColumn pairing doubled (tangent s) (scaledFrame s)

private theorem realize_entries :
    (entries (ω : FlatScalar)).map sqrt3Map = (746496 : ℝ) • Matrix.of (jacobianEntry flatBase) := by
  ext r n
  rw [Matrix.map_apply]
  rcases h : rowIndex r with ⟨i,j,k⟩
  rcases context_cases n with hn | hn <;>
    norm_num [entries, jacobianEntry, ledgerColumn, hn, h, pairing, inner, trace_smul,
      jordan_smul_right, jordan_smul_left, inner_smul_left, inner_smul_right, smul_smul] 

section Naturality
variable (f : R →+* S)

@[simp] private theorem map_ld (x : Coords R) : coeffMap f (ld x) = ld (coeffMap f x) := by
  ext <;> simp [coeffMap, rq, ro, ld, map_ofNat]

@[simp] private theorem map_tangent (s : R) (n : Fin 20) (i : Fin 3) :
    coeffMap f (tangent s n i) = tangent (f s) n i := by
  simp [tangent]

private theorem map_entries (s : R) : (entries s).map f = entries (f s) := by
  ext r n
  rw [Matrix.map_apply]
  rcases h : rowIndex r with ⟨i,j,k⟩
  by_cases hn : contextIndex n = 0 <;> simp [entries, ledgerColumn, pairing, map_tr, h, hn]
end Naturality

private def modLift : FlatScalar →+* ZMod 11 :=
  (QuadraticAlgebra.lift ⟨5, by decide +kernel⟩).toRingHom

private def modEntries := entries (5 : ZMod 11)

private def fromData (data : Array (Array ℕ)) : Matrix (Fin 20) (Fin 20) (ZMod 11) :=
  fun i j => (MatrixCertificate.ofRows data i j : ℕ)

private def entries' : Matrix (Fin 20) (Fin 20) (ZMod 11) := fromData
  (eval% (Array.ofFn fun i => Array.ofFn fun j => (modEntries i j).val))

private def invEntries : Matrix (Fin 20) (Fin 20) (ZMod 11) := fromData
  (eval% ((MatrixCertificate.inverseCandidateRows Inv.inv entries').map (·.map ZMod.val)))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in

private theorem entries_inv : modEntries * invEntries = 1 := by
  have h : modEntries = entries' := MatrixCertificate.eq_of_check _ _ (by
    apply List.all_eq_true.mpr
    intro i _
    fin_cases i <;> decide +kernel)
  rw [h]
  exact MatrixCertificate.eq_of_check _ _ (by decide +kernel)

local instance : Fact (1 < 11) := ⟨by decide⟩

theorem det_ne_zero_flatBase :
    (Matrix.of (jacobianEntry flatBase)).det ≠ 0 := by
  intro h
  have he : sqrt3Map (entries (ω : FlatScalar)).det = 0 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, realize_entries, Matrix.det_smul, h, mul_zero]
  have hz := lift_injective (he.trans (map_zero sqrt3Map).symm)
  apply MatrixCertificate.det_ne_zero_of_inverse entries_inv
  change ((entries (modLift (ω : FlatScalar))).det = 0)
  rw [← map_entries modLift, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hz, map_zero]

end Glennie.Compact.NativeFlatRank20
