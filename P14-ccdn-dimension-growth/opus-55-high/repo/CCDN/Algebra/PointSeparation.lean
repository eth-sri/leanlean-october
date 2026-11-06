/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.Ring

/-!
# Point separation for polynomial sections

Powers of any nonzero element vanishing at the selected points give
independent classes.
-/

namespace CCDN
section

/-- Explicit polynomial interpolation at a finite family of distinct affine points. -/
theorem exists_point_separators {K σ ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (z : ι → σ → K) (hz : Function.Injective z) :
    ∃ h : ι → MvPolynomial σ K, ∀ i j,
      MvPolynomial.eval (z i) (h j) = if i = j then 1 else 0 := by
  have hex (i : ι) : ∃ h : MvPolynomial σ K,
      MvPolynomial.eval (z i) h = 1 ∧
      ∀ j, j ≠ i → MvPolynomial.eval (z j) h = 0 := by
    have hcoords (j : {j : ι // j ≠ i}) : ∃ k, z i k ≠ z j.val k :=
      Function.ne_iff.mp (fun he => j.property (hz he).symm)
    choose k hk using hcoords
    let factor (j : {j : ι // j ≠ i}) : MvPolynomial σ K :=
      MvPolynomial.C ((z i (k j) - z j.val (k j))⁻¹) *
        (MvPolynomial.X (k j) - MvPolynomial.C (z j.val (k j)))
    refine ⟨∏ j, factor j, ?_, ?_⟩
    · rw [MvPolynomial.eval_prod]
      apply Finset.prod_eq_one
      simp [factor, MvPolynomial.eval_mul, MvPolynomial.eval_C,
        MvPolynomial.eval_sub, MvPolynomial.eval_X]
      grind
    · intro j hji
      rw [MvPolynomial.eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ (⟨j, hji⟩ : {j : ι // j ≠ i}))
      simp [factor]
  choose h hon hoff using hex
  refine ⟨h, ?_⟩
  intro i j
  by_cases he : i = j
  · grind
  · grind

