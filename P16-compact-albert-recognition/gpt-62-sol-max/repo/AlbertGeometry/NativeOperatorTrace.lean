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
def octCoeff {R : Type*} [CommRing R] (u : Quaternion R × Quaternion R) : Fin 8 → R :=
  ![u.1.re, u.1.imI, u.1.imJ, u.1.imK,
    u.2.re, u.2.imI, u.2.imJ, u.2.imK]

def octFrom (c : Fin 8 → ℝ) : Octonion :=
  (⟨c 0, c 1, c 2, c 3⟩, ⟨c 4, c 5, c 6, c 7⟩)

/-- Three diagonal scalar entries followed by slots 01,02,12. -/
def fullCoeff (x : Albert) : FullIndex → ℝ
  | Sum.inl i => ![x.d0, x.d1, x.d2] i
  | Sum.inr (s,t) => octCoeff (![x.o01, x.o02, x.o12] s) t

def fullFrom (c : FullIndex → ℝ) : Albert :=
  ⟨c (Sum.inl 0), c (Sum.inl 1), c (Sum.inl 2),
    octFrom (fun t => c (Sum.inr (0,t))),
    octFrom (fun t => c (Sum.inr (1,t))),
    octFrom (fun t => c (Sum.inr (2,t)))⟩

local macro "coeff_ext" : tactic => `(tactic| (
  ext i
  rcases i with j | ⟨s,t⟩
  · fin_cases j <;> rfl
  · fin_cases s <;> fin_cases t <;> rfl))

/-- The full27 coordinate equivalence is not a tracefree restriction. -/
def fullCoordinates : Albert ≃ₗ[ℝ] (FullIndex → ℝ) where
  toFun := fullCoeff
  invFun := fullFrom
  left_inv x := by cases x; rfl
  right_inv c := by coeff_ext
  map_add' x y := by coeff_ext
  map_smul' r x := by coeff_ext

end
end AlbertGeometry.NativeOperatorTrace
