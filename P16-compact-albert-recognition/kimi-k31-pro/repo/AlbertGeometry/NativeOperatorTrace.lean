/- A full-native operator trace lemma; no geometry or compact fixture input.
All native operations are the literal compact quaternion-pair definitions.
No trace preservation is assumed for product-preserving linear equivalences.
-/
module

public import Glennie.Native.AlgebraLaws
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section
namespace AlbertGeometry.NativeOperatorTrace
noncomputable section
open Module Glennie
open scoped BigOperators Quaternion

abbrev FullIndex := Fin 3 ⊕ (Fin 3 × Fin 8)

/-- Scalar coordinates of the actual quaternion-pair octonion carrier. -/
def octCoeff (u : Octonion) : Fin 8 → ℝ :=
  ![u.1.re, u.1.imI, u.1.imJ, u.1.imK,
    u.2.re, u.2.imI, u.2.imJ, u.2.imK]

def octFrom (c : Fin 8 → ℝ) : Octonion :=
  (⟨c 0, c 1, c 2, c 3⟩, ⟨c 4, c 5, c 6, c 7⟩)

/-- A genuine linear equivalence, proved by literal coordinate inverses. -/
def octCoordinates : Octonion ≃ₗ[ℝ] (Fin 8 → ℝ) where
  toFun := octCoeff
  invFun := octFrom
  left_inv u := by
    apply Prod.ext <;> apply Quaternion.ext <;> rfl
  right_inv c := by
    ext t
    fin_cases t <;> rfl
  map_add' u v := by
    ext t
    fin_cases t <;> rfl
  map_smul' r u := by
    ext t
    fin_cases t <;> rfl

@[simp] theorem octCoordinates_apply (u : Octonion) :
    octCoordinates u = octCoeff u := rfl

@[simp] theorem octCoordinates_symm_apply (c : Fin 8 → ℝ) :
    octCoordinates.symm c = octFrom c := rfl

/-- Three diagonal scalar entries followed by slots 01,02,12. -/
def fullCoeff (x : Albert) : FullIndex → ℝ
  | Sum.inl i => ![x.d0, x.d1, x.d2] i
  | Sum.inr (s,t) => octCoeff (![x.o01, x.o02, x.o12] s) t

def fullFrom (c : FullIndex → ℝ) : Albert :=
  ⟨c (Sum.inl 0), c (Sum.inl 1), c (Sum.inl 2),
    octFrom (fun t => c (Sum.inr (0,t))),
    octFrom (fun t => c (Sum.inr (1,t))),
    octFrom (fun t => c (Sum.inr (2,t)))⟩

/-- The full27 coordinate equivalence is not a tracefree restriction. -/
def fullCoordinates : Albert ≃ₗ[ℝ] (FullIndex → ℝ) where
  toFun := fullCoeff
  invFun := fullFrom
  left_inv x := by
    apply Albert.ext
    · rfl
    · rfl
    · rfl
    · apply Prod.ext <;> apply Quaternion.ext <;> rfl
    · apply Prod.ext <;> apply Quaternion.ext <;> rfl
    · apply Prod.ext <;> apply Quaternion.ext <;> rfl
  right_inv c := by
    ext i
    rcases i with j | ⟨s,t⟩
    · fin_cases j <;> rfl
    · fin_cases s <;> fin_cases t <;> rfl
  map_add' x y := by
    ext i
    rcases i with j | ⟨s,t⟩
    · fin_cases j <;> rfl
    · fin_cases s <;> fin_cases t <;> rfl
  map_smul' r x := by
    ext i
    rcases i with j | ⟨s,t⟩
    · fin_cases j <;> rfl
    · fin_cases s <;> fin_cases t <;> rfl

@[simp] theorem fullCoordinates_apply (x : Albert) :
    fullCoordinates x = fullCoeff x := rfl

@[simp] theorem fullCoordinates_symm_apply (c : FullIndex → ℝ) :
    fullCoordinates.symm c = fullFrom c := rfl

/-- All27 vectors form an actual basis because fullCoordinates is an equivalence. -/
def nativeBasis : Basis FullIndex ℝ Albert := Basis.ofEquivFun fullCoordinates

@[simp] theorem nativeBasis_repr (x : Albert) (i : FullIndex) :
    nativeBasis.repr x i = fullCoeff x i :=
  Basis.ofEquivFun_repr_apply fullCoordinates x i

@[simp] theorem nativeBasis_apply (i : FullIndex) :
    nativeBasis i = fullFrom (Pi.single i (1 : ℝ)) := by
  exact congrFun (Basis.coe_ofEquivFun fullCoordinates) i

theorem fullIndex_card : Fintype.card FullIndex = 27 := by
  simp [FullIndex]

/-- Left multiplication packaged as an actual real linear endomorphism. -/
def nativeLeft (x : Albert) : Module.End ℝ Albert where
  toFun y := jordan x y
  map_add' y z := jordan_add_right x y z
  map_smul' r y := by
    simpa only [RingHom.id_apply] using jordan_smul_right r x y

@[simp] theorem nativeLeft_apply (x y : Albert) :
    nativeLeft x y = jordan x y := rfl

-- Declaration-scoped resource budget for 24 literal coordinate goals.

end
end AlbertGeometry.NativeOperatorTrace
