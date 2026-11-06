/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import CCDN.ForMathlib.Polynomial

/-! The eliminant for a ratio g(beta)/f'(beta).
For f,g in F[t][z], coefficients are lifted into F[u][t], and z is
eliminated from f and u*f'-g. The resulting polynomial has outer t-degree
at most (2*deg_z(f)-1) times the coefficient t-degree bound. -/

namespace CCDN
noncomputable section
open Polynomial

section
variable {F : Type*} [CommRing F]

/-- The embedding `F[t] → F[u][t]` of polynomials in `t` as polynomials with constant coefficients
in the new parameter `u`. -/
def residueParameterLift : F[X] →+* F[X][X] :=
  mapRingHom (C : F →+* F[X])

/-- The specialization `F[u][t] → F[t]` at `u = 0`. -/
def residueParameterZero : F[X][X] →+* F[X] :=
  mapRingHom (evalRingHom (0 : F))

/-- Specializing `u = 0` after lifting a polynomial in `t` to `F[u][t]` recovers it. -/
@[simp] lemma residueParameterZero_lift (a : F[X]) :
    residueParameterZero (residueParameterLift a) = a := by
  ext i
  simp [residueParameterZero, residueParameterLift]

/-- Applying `residueParameterLift` and then `residueParameterZero` to the coefficients of a
polynomial over `F[t]` recovers it. -/
@[simp] lemma residueParameterZero_map_lift (f : F[X][X]) :
    (f.map residueParameterLift).map residueParameterZero = f := by
  ext i
  simp

end

section
variable {F : Type*} [CommRing F] (f g : F[X][X])

/-- The polynomial `u · ∂f/∂z - g` in `z`, with coefficients in `F[u][t]`, whose common roots with
`f` are the values `u = g(β) / f'(β)`. -/
def residueEliminationEquation : F[X][X][X] :=
  C (C X) * (f.map residueParameterLift).derivative - g.map residueParameterLift

/-- The resultant in `z` of `f` and `u · ∂f/∂z - g`, a polynomial in `t` with coefficients in `F[u]`
that vanishes at every ratio `u = g(β) / f'(β)` at a simple root `β` of `f`. -/
def residueEliminant : F[X][X] :=
  (f.map residueParameterLift).resultant (residueEliminationEquation f g)
    f.natDegree (f.natDegree - 1)

/-- At `u = 0`, `residueEliminationEquation f g` specializes to `-g`. -/
@[simp] lemma residueEliminationEquation_zero :
    (residueEliminationEquation f g).map residueParameterZero = -g := by
  simp only [residueEliminationEquation, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C]
  rw [show residueParameterZero (C X : F[X][X]) = 0 by simp [residueParameterZero],
    C_0, zero_mul, zero_sub, residueParameterZero_map_lift]

lemma residueEliminant_zero :
    residueParameterZero (residueEliminant f g) =
      f.resultant (-g) f.natDegree (f.natDegree - 1) := by
  rw [residueEliminant, ← resultant_map_map, residueParameterZero_map_lift, residueEliminationEquation_zero]

end

lemma coefficient_derivative_natDegree_le {R : Type*} [CommRing R]
    (f : R[X][X]) (D : ℕ) (hf : ∀ i, (f.coeff i).natDegree ≤ D) (i : ℕ) :
    (f.derivative.coeff i).natDegree ≤ D := by
  have he : f.derivative.coeff i = (i + 1) • f.coeff (i + 1) := by
    rw [coeff_derivative]
    grind
  rw [he]
  exact (natDegree_smul_le _ _).trans (hf _)

variable {F : Type*}

