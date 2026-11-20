/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.Ring

/-!
# Point separation for polynomial sections

Powers of any nonzero element vanishing at the selected points give
independent classes.
-/

@[expose] public section
namespace CCDN
noncomputable section

variable {K σ A ι : Type*} [Field K]

/-- Powers of a nonzero element times point separators are jointly independent
when that element vanishes under all point evaluations. -/
theorem separator_powers_independent [CommRing A]
    [IsDomain A] [Algebra K A] [Fintype ι] [DecidableEq ι]
    (φ : ι → A →ₐ[K] K) (h : ι → A) (l : A) (hl : l ≠ 0)
    (hzero : ∀ i, φ i l = 0)
    (hsep : ∀ i j, φ i (h j) = if i = j then 1 else 0) (N : ℕ) :
    LinearIndependent K (fun t : ι × Fin N => h t.1 * l ^ t.2.val) := by
  classical
  induction N with
  | zero => exact linearIndependent_empty_type
  | succ N ih =>
    rw [Fintype.linearIndependent_iff]
    intro a ha t
    have hconst (i : ι) : a (i, 0) = 0 := by
      simpa [Fintype.sum_prod_type, Fin.sum_univ_succ, hzero, hsep, eq_comm] using (congrArg (φ i) ha)
    have htail : ∑ t : ι × Fin N, a (t.1, t.2.succ) • (h t.1 * l ^ t.2.val) = 0 := by
      apply (mul_left_cancel₀ hl)
      rw [mul_zero, Finset.mul_sum]
      have he : (∑ t : ι × Fin (N + 1), a t • (h t.1 * l ^ t.2.val)) =
          ∑ t : ι × Fin N, l * (a (t.1, t.2.succ) • (h t.1 * l ^ t.2.val)) := by
        simp only [Fintype.sum_prod_type, Fin.sum_univ_succ, hconst, zero_smul, zero_add]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro k _
        simp only [Fin.val_succ, pow_succ, Algebra.smul_def]
        ring
      grind
    have hcoeff := Fintype.linearIndependent_iff.mp ih
      (fun t => a _) htail
    obtain ⟨i, k⟩ := t
    refine Fin.cases (hconst i) (fun k => hcoeff (i, k)) k

/-- Explicit polynomial interpolation at a finite family of distinct affine points. -/
theorem exists_point_separators [Fintype ι] [DecidableEq ι]
    (z : ι → σ → K) (hz : Function.Injective z) :
    ∃ h : ι → MvPolynomial σ K, ∀ i j,
      MvPolynomial.eval (z i) (h j) = if i = j then 1 else 0 := by
  classical
  have hex (i : ι) : ∃ h : MvPolynomial σ K,
      MvPolynomial.eval (z i) h = 1 ∧
      ∀ j, j ≠ i → MvPolynomial.eval (z j) h = 0 := by
    have hcoords (j : {j : ι // j ≠ i})  :=
      Function.ne_iff.mp (fun he => j.property (hz he).symm)
    choose k hk using hcoords
    let factor (j : {j : ι // j ≠ i})  :=
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
      apply Finset.prod_eq_zero (Finset.mem_univ (⟨j, hji⟩))
      simp [factor]
  choose h hon hoff using hex
  refine ⟨h, ?_⟩
  grind

end
end CCDN
