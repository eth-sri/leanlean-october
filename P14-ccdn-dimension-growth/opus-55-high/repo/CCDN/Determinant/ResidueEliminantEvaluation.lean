/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Determinant.ResidueEliminant

/-! Evaluation of the residue eliminant. The Sylvester Bezout identity
proves its vanishing at every ratio g(beta)/f'(beta) at a simple root. -/

namespace CCDN
noncomputable section
open Polynomial

section
variable {F L : Type*} [Field F] [Field L] [Algebra F L] (t u : L)

/-- The evaluation `F[u][t] → L` at `u` and `t`, for elements `t, u` of an `F`-algebra `L`. -/
def residueParameterEval
    : F[X][X] →+* L := eval₂RingHom (aeval u).toRingHom t

/-- Evaluating the lift of a polynomial `a ∈ F[t]` at `(t, u)` gives `a(t)`. -/
@[simp] lemma residueParameterEval_lift
    (a : F[X]) :
    residueParameterEval t u (residueParameterLift a) = aeval t a := by
  induction a using Polynomial.induction_on' with
  | add a b ha hb => simp [map_add, ha, hb]
  | monomial n c => simp [residueParameterEval, residueParameterLift]

/-- The parameter `u ∈ F[u][t]` evaluates to `u`. -/
@[simp] lemma residueParameterEval_C_X
    : residueParameterEval (F := F) t u (C X) = u := by
  simp [residueParameterEval]

/-- Applying `residueParameterLift` and then evaluation at `(t, u)` to the coefficients of a
polynomial over `F[t]` is evaluating its coefficients at `t`. -/
@[simp] lemma residueParameterEval_map_lift
    (f : F[X][X]) :
    (f.map residueParameterLift).map (residueParameterEval t u) = f.map (aeval t).toRingHom := by
  ext i
  simp

lemma residueEliminationEquation_map_eval
    (f g : F[X][X]) :
    (residueEliminationEquation f g).map (residueParameterEval t u) =
      C u * (f.map (aeval t).toRingHom).derivative - g.map (aeval t).toRingHom := by
  simp [residueEliminationEquation, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_C, residueParameterEval_C_X, ← derivative_map, residueParameterEval_map_lift]

end

/-- If `β` is a simple root of `f(t, ·)` and `g` has smaller `z`-degree than `f`, then the residue
eliminant vanishes at `t` and `u = g(t, β) / f'(t, β)`. -/
theorem residueEliminant_eval_ratio_eq_zero
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (t β : L) (f g : F[X][X]) (hdeg : g.natDegree < f.natDegree)
    (hroot : (f.map (aeval t).toRingHom).eval β = 0)
    (hsimple : (f.map (aeval t).toRingHom).derivative.eval β ≠ 0) :
    let u := (g.map (aeval t).toRingHom).eval β /
      (f.map (aeval t).toRingHom).derivative.eval β
    ((residueEliminant f g).map (aeval u).toRingHom).eval t = 0 := by
  dsimp
  let u := (g.map (aeval t).toRingHom).eval β /
    (f.map (aeval t).toRingHom).derivative.eval β
  let ψ := residueParameterEval (F := F) t u
  have hF : ((f.map residueParameterLift).map ψ).eval β = 0 := by aesop
  have hG : ((residueEliminationEquation f g).map ψ).eval β = 0 := by
    rw [show ψ = residueParameterEval t u from rfl, residueEliminationEquation_map_eval]
    simp only [eval_sub, eval_mul, eval_C]
    grind
  obtain ⟨a, b, _, _, hab⟩ := exists_mul_add_mul_eq_C_resultant
   
    (f.map residueParameterLift) (residueEliminationEquation f g)
    natDegree_map_le (show (residueEliminationEquation f g).natDegree ≤ f.natDegree - 1 by
        apply (natDegree_sub_le _ _).trans
        apply max_le
        · exact (natDegree_C_mul_le _ _).trans
            ((natDegree_derivative_le _).trans (Nat.sub_le_sub_right natDegree_map_le 1))
        · exact natDegree_map_le.trans (by omega)) (Or.inl (by omega))
  have h := congrArg (fun P => (P.map ψ).eval β) hab
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    eval_add, eval_mul, eval_C, hF, hG, zero_mul, zero_add] at h
  rw [eval_map]
  exact h.symm

