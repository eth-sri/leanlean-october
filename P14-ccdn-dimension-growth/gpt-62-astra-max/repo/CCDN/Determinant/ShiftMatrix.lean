/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Algebra.Equations
public import CCDN.Determinant.ComplementaryMinor
public import CCDN.Algebra.HomogeneousMonomials
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import CCDN.Algebra.HomogeneousEvaluation
import CCDN.Algebra.RowSelection
import CCDN.Hilbert.HomogeneousHilbert
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

/-- Number of degree-`M` monomials in `n+1` variables. -/
abbrev formDim (n M : ℕ) := (n + M).choose M

variable {n d M t : ℕ}
local notation "mons" => homogeneousMonomials n
local notation "Forms" => IntegerPolynomial (n+1)

/-- Multiplication by `f` from degree `r` to degree `M`, in monomial coordinates. -/
private def shifts (f : Forms) (M r : ℕ) : Matrix (Fin (formDim n M)) (Fin (formDim n r)) ℤ :=
  of fun i j => (f * monomial (mons r j) 1).coeff (mons M i)

private lemma shifts_mulVec (f : Forms) (M r : ℕ) (w : Fin (formDim n r) → ℤ) :
    shifts f M r *ᵥ w = fun i => (f * polynomialOfCoefficients (mons r) w).coeff (mons M i) := by
  classical
  ext i
  simp [shifts, polynomialOfCoefficients, Finset.mul_sum, mulVec, dotProduct,
    coeff_mul_monomial', ite_mul]

/-- On the rows indexed by multiples of the leading monomial, the shift matrix is triangular,
with constant diagonal the leading coefficient. In equal degrees there is only one column
and any nonzero coefficient gives such a minor. -/
private theorem shifts_minor (order : MonomialOrder (Fin (n+1))) (f : Forms)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hdM : d ≤ M) (m : Fin (n+1) →₀ ℕ)
    (hm : f.coeff m ≠ 0) (hlead : m = order.degree f ∨ M = d) :
    ∃ u : Fin (formDim n (M-d)) → Fin (formDim n M), Function.Injective u ∧
      ((shifts f M (M-d)).submatrix u id).det = f.coeff m ^ formDim n (M-d) := by
  classical
  let Y := mons (M-d)
  have hy j : (m + Y j).degree = M := by
    rw [map_add, homogeneousMonomials_degree, show m.degree = d by rw [Finsupp.degree_eq_weight_one]; exact hf hm]; omega
  choose u hu using fun j => homogeneousMonomials_surjective n M _ (hy j)
  refine ⟨u, fun i j h => (homogeneousMonomials_injective n _)
    (add_left_cancel ((hu i).symm.trans ((congrArg (mons M) h).trans (hu j)))), ?_⟩
  let : LinearOrder (Fin (formDim n (M-d))) := LinearOrder.lift' (order.toSyn ∘ Y)
    (order.toSyn.injective.comp (homogeneousMonomials_injective n _))
  rw [det_of_isUpperTriangular]
  · simp [shifts, hu, coeff_mul_monomial, Y]
  intro i j hij
  change (f * monomial (Y j) 1).coeff (mons M (u i)) = 0
  rw [hu]
  change order.toSyn (Y j) < order.toSyn (Y i) at hij
  rcases hlead with rfl | rfl
  · apply order.coeff_eq_zero_of_lt
    rw [order.degree_mul hf0 (by simp), order.degree_monomial]
    simpa [map_add] using (show order.toSyn (order.degree f) + order.toSyn (Y j) <
      order.toSyn (order.degree f) + order.toSyn (Y i) from add_lt_add_right hij _)
  · have : Subsingleton (Fin (formDim n (M-M))) := by simp [formDim]; infer_instance
    simp [Subsingleton.elim j i] at hij

/-- Exact-rank determinant comparison in the absence of an auxiliary. The integral kernel
is spanned by monomial shifts of `f`; their triangular minor supplies the height saving. -/
theorem homogeneous_coefficient_minor_bound (order : MonomialOrder (Fin (n+1))) (f : Forms)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hdM : d ≤ M)
    (z : Fin t → IntPoint (n+1)) (hz : ∀ i, eval (z i) f = 0)
    {B : ℝ} (hB : 1 ≤ B) (hbox : ∀ i, InBox (z i) B)
    (hrel : ∀ g : Forms, g.IsHomogeneous M → (∀ i, eval (z i) g = 0) → f ∣ g)
    (m : Fin (n+1) →₀ ℕ) (hm : f.coeff m ≠ 0) (hlead : m = order.degree f ∨ M = d) :
    ∃ (s : ℕ) (a : Fin s → Fin t), Function.Injective a ∧ s < formDim n M ∧
      s + formDim n (M-d) = formDim n M ∧
      let A := evaluationMatrix (mons M) (z ∘ a)
      LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row ∧
      (Int.Matrix.minorGcd A : ℝ) * |(f.coeff m : ℝ)| ^ formDim n (M-d) ≤
        s.factorial * (B ^ M) ^ s := by
  classical
  let X := mons M
  let Y := mons (M-d)
  obtain ⟨s,a,ha,hi,hsp,-⟩ := exists_independent_spanning_rows ((evaluationMatrix X z).map ((↑) : ℤ → ℚ))
  let A := evaluationMatrix X (z ∘ a)
  let C := shifts f M (M-d)
  have hAC : A * C = 0 := by
    ext i j
    change (A *ᵥ C.col j) i = 0
    have hhom := by
      simpa [Nat.add_sub_of_le hdM] using hf.mul (isHomogeneous_monomial 1 (homogeneousMonomials_degree n (M-d) j))
    rw [← eval_polynomialOfCoefficients, show polynomialOfCoefficients X (C.col j) = _ from
      (homogeneous_eq_sum_coeff _ hhom).symm, eval_mul, Function.comp_apply, hz, zero_mul]
  have hker (v) (hv : A *ᵥ v = 0) : ∃ w, C *ᵥ w = v := by
    let g := polynomialOfCoefficients X v
    have hg : g.IsHomogeneous M := polynomialOfCoefficients_homogeneous n M v
    obtain ⟨q,hq⟩ := hrel g hg fun i => vanishes_of_evaluation_row_mem_span X _ v hv (z i) (by
      rw [show Submodule.span ℚ (Set.range (A.map ((↑) : ℤ → ℚ)).row) = _ from hsp]
      exact Submodule.subset_span ⟨i,rfl⟩)
    refine ⟨fun j => q.coeff (Y j), ?_⟩
    rw [show C = C from rfl, shifts_mulVec,
      show polynomialOfCoefficients Y _ = q from (homogeneous_eq_sum_coeff q (homogeneous_multiplier hf hf0 (hq ▸ hg) hdM)).symm, ← hq]
    exact funext (by solve_by_elim [coefficient_polynomialOfCoefficients, homogeneousMonomials_injective])
  obtain ⟨u,hu,hd⟩ := shifts_minor order f hf hf0 hdM m hm hlead
  obtain ⟨hr, j, hj⟩ := complementary_minor_bound A C hi hAC hker u hu (hd ▸ pow_ne_zero _ hm)
  have hk : 0 < formDim n (M-d) := Nat.choose_pos (by omega)
  change s + formDim n (M-d) = formDim n M at hr
  refine ⟨s,a,ha,by omega,hr,hi,?_⟩
  rw [hd, abs_pow] at hj
  let T := A.submatrix id j
  have hentry (i l)  :=
    abs_monomial_value_le _ _ hB (hbox (a i)) (homogeneousMonomials_degree n M (j l)).le
  have hdet := Matrix.det_le (A := T.map ((↑) : ℤ → ℝ)) (abv := AbsoluteValue.abs) hentry
  change |((Int.castRingHom ℝ).mapMatrix T).det| ≤ _ at hdet
  rw [← RingHom.map_det] at hdet
  exact (show _ ≤ |(T.det : ℝ)| by exact_mod_cast hj).trans (by simpa using hdet)

end
end CCDN
