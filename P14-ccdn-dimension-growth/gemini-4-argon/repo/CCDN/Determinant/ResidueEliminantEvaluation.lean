/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Determinant.ResidueEliminant

/-! Evaluation of the residue eliminant. The Sylvester Bezout identity
proves its vanishing at every ratio g(beta)/f'(beta) at a simple root. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

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
  /- The evaluation `F[u][t] → L` at `u` and `t`, for elements `t, u` of an `F`-algebra `L`. -/
  /- Evaluating the lift of a polynomial `a ∈ F[t]` at `(t, u)` gives `a(t)`. -/
  /- The parameter `u ∈ F[u][t]` evaluates to `u`. -/
  /- Applying `residueParameterLift` and then evaluation at `(t, u)` to the coefficients of a
  polynomial over `F[t]` is evaluating its coefficients at `t`. -/
  dsimp only
  let u := (g.map (aeval t).toRingHom).eval β /
    (f.map (aeval t).toRingHom).derivative.eval β
  let ψ : F[X][X] →+* L := eval₂RingHom (aeval u).toRingHom t
  have hlift (P : F[X][X]) : (P.map residueParameterLift).map ψ = P.map (aeval t).toRingHom := by
    ext i
    simp only [coeff_map]
    induction P.coeff i using Polynomial.induction_on' with
    | add a b ha hb => simp only [map_add, ha, hb]
    | monomial n c => simp [ψ, residueParameterLift]
  have hF : ((f.map residueParameterLift).map ψ).eval β = 0 := by
    simpa only [hlift] using hroot
  have hG : ((residueEliminationEquation f g).map ψ).eval β = 0 := by
    have hCX : ψ (C X) = u := by simp [ψ]
    simp only [residueEliminationEquation, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_C, hCX, ← derivative_map, hlift, eval_sub, eval_mul, eval_C]
    exact sub_eq_zero.mpr (div_mul_cancel₀ _ hsimple)
  obtain ⟨a, b, _, _, hab⟩ := exists_mul_add_mul_eq_C_resultant
    (m := f.natDegree) (n := f.natDegree - 1)
    (f.map residueParameterLift) (residueEliminationEquation f g)
    natDegree_map_le (residueEliminationEquation_natDegree_le f g hdeg) (Or.inl (by omega))
  have h := congrArg (fun P => (P.map ψ).eval β) hab
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    eval_add, eval_mul, eval_C, hF, hG, zero_mul, zero_add] at h
  rw [eval_map]
  exact h.symm

end
end CCDN
