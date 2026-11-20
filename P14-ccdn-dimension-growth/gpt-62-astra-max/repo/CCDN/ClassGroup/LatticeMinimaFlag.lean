/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! An orthonormal flag adapted to greedy lattice vectors. A small
coordinate box in this flag contains no nonzero lattice vector. -/

@[expose] public section
namespace CCDN
noncomputable section
open Module Submodule InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Every basis `b` of a finite-dimensional real inner product space has an orthonormal basis `c`
(its Gram–Schmidt orthonormalisation) spanning the same flag: for each `i`, the vectors with
index `< i` of `c` and of `b` span the same subspace. -/
theorem exists_orthonormal_basis_with_same_flag {n : ℕ}
    (b : Basis (Fin n) ℝ E) :
    ∃ c : OrthonormalBasis (Fin n) ℝ E, ∀ i,
      Submodule.span ℝ (c '' Set.Iio i) = Submodule.span ℝ (b '' Set.Iio i) := by
  let c := gramSchmidtOrthonormalBasis (Module.finrank_eq_card_basis b) b
  have hc : (c : Fin n → E) = gramSchmidtNormed ℝ b := by
    funext i
    apply gramSchmidtOrthonormalBasis_apply
    intro he
    have hn := gramSchmidtNormed_unit_length i b.linearIndependent
    aesop
  refine ⟨c, fun i => ?_⟩
  rw [hc, span_gramSchmidtNormed, span_gramSchmidt_Iio]

omit [FiniteDimensional ℝ E] in
/-- With side lengths equal to the flag minima divided by dimension,
the open symmetric coordinate box has no nonzero lattice vector. -/
theorem lattice_flag_coordinate_box_zero
    {n : ℕ} (hn : 0 < n) (L : Submodule ℤ E)
    (c : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ)
    (hpos : ∀ i, 0 < a i) (hmono : Monotone a)
    (hminimum : ∀ i x, x ∈ L → x ∉ Submodule.span ℝ (c '' Set.Iio i) → a i ≤ ‖x‖)
    {x : E} (hx : x ∈ L)
    (hbox : ∀ i, |c.toBasis.repr x i| < a i / n) : x = 0 := by
  classical
  by_contra hx0
  let S := (c.toBasis.repr x).support
  have hS : S.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    exact hx0 (c.toBasis.repr.injective (by simpa using (Finsupp.support_eq_empty.mp he)))
  let j := S.max' hS
  have hnot : x ∉ Submodule.span ℝ (c '' Set.Iio j) := by
    intro h
    exact (lt_irrefl j) ((c.toBasis.repr_support_subset_of_mem_span (Set.Iio j) h) (Finset.max'_mem _ hS))
  have hmin := hminimum j x hx hnot
  have hnj := hpos j
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hterm (i : Fin n) : ‖c.toBasis.repr x i • c i‖ < a j / n := by
    rw [norm_smul, c.orthonormal.1 i, mul_one, Real.norm_eq_abs]
    by_cases hi : i ≤ j
    exact (hbox i).trans_le (by bound)
    · have hz : c.toBasis.repr x i = 0 := by
        grind [Finsupp.notMem_support_iff.mp, Finset.le_max']
      rw [hz, abs_zero]
      positivity
  have hstrict := by
    have hsum := Finset.sum_lt_sum_of_nonempty
      (⟨⟨0, hn⟩, Finset.mem_univ _⟩)
      (fun i _ => hterm i)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_div_cancel₀ _ (ne_of_gt hnR)] using hsum
  have hnorm := by
    calc
      ‖x‖ = ‖∑ i : Fin n, c.toBasis.repr x i • c i‖ := by
        congr 1
        exact c.toBasis.sum_repr x |>.symm
      _ ≤ _ := norm_sum_le _ _
  linarith

end
end CCDN
