/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredIntersection
public import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.Algebraic.Basic

/-! Hilbert degree controls function-field rank over a transcendental linear
coordinate. Independent functions over the parameter field produce independent
blocks over the constant field, whose filtered growth bounds their number. -/

@[expose] public section
namespace CCDN
noncomputable section

variable {K R F ι κ : Type*} [Field K]

/-- In a tower `K → R → F`, the products `u k • v i` of a family `v` independent over `R` and a
family `u` independent over `K` are independent over `K`. -/
lemma tower_smul_independent [Field R] [Field F]
    [Algebra K R] [Algebra R F] [Algebra K F] [IsScalarTower K R F]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (v : ι → F) (hv : LinearIndependent R v)
    (u : κ → R) (hu : LinearIndependent K u) :
    LinearIndependent K (fun t : ι × κ => u t.2 • v t.1) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc t
  have he : ∑ i, (∑ k, c (i, k) • u k) • v i = 0 := by
    simpa [Fintype.sum_prod_type, Finset.sum_smul] using hc
  exact Fintype.linearIndependent_iff.mp hu (fun k => c (t.1, k)) (Fintype.linearIndependent_iff.mp hv _ he t.1) t.2

/-- The powers `1, u, …, u ^ (N - 1)` of a transcendental element `u` are linearly independent. -/
lemma transcendental_powers_independent [CommRing R] [Algebra K R]
    (u : R) (hu : Transcendental K u) (N : ℕ) :
    LinearIndependent K (fun i : Fin N => u ^ i.val) := by
  have hb := (Polynomial.basisMonomials K).linearIndependent.map'
    (Polynomial.aeval u).toLinearMap
    (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp hu))
  simpa [Function.comp_def] using (hb.comp (fun i : Fin N => i.val) Fin.val_injective)

end
end CCDN
