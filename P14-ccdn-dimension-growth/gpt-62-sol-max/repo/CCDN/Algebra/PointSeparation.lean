/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Point separation for polynomial sections

Polynomial interpolation at finitely many distinct affine points.
-/

@[expose] public section
namespace CCDN
noncomputable section

/-- Explicit polynomial interpolation at a finite family of distinct affine points. -/
theorem exists_point_separators {K σ ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (z : ι → σ → K) (hz : Function.Injective z) :
    ∃ h : ι → MvPolynomial σ K, ∀ i j,
      MvPolynomial.eval (z i) (h j) = if i = j then 1 else 0 := by
  classical
  have hex (i : ι) : ∃ h : MvPolynomial σ K,
      MvPolynomial.eval (z i) h = 1 ∧
      ∀ j, j ≠ i → MvPolynomial.eval (z j) h = 0 := by
    have hcoords (j : {j : ι // j ≠ i}) :=
      Function.ne_iff.mp (fun he => j.property (hz he).symm)
    choose k hk using hcoords
    let factor (j : {j : ι // j ≠ i}) :=
      MvPolynomial.C ((z i (k j) - z j.val (k j))⁻¹) *
        (MvPolynomial.X (k j) - MvPolynomial.C (z j.val (k j)))
    refine ⟨∏ j, factor j, ?_, ?_⟩
    · rw [MvPolynomial.eval_prod]
      apply Finset.prod_eq_one
      intro j _
      simp only [factor, MvPolynomial.eval_mul, MvPolynomial.eval_C,
        MvPolynomial.eval_sub, MvPolynomial.eval_X]
      grind
    · intro j hji
      rw [MvPolynomial.eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ (⟨j, hji⟩ : {j : ι // j ≠ i}))
      aesop
  choose h hon hoff using hex
  refine ⟨h, ?_⟩
  intro i j
  by_cases he : i = j
  · subst j
    simpa using hon i
  · simpa [he] using hoff j i he

end
end CCDN
