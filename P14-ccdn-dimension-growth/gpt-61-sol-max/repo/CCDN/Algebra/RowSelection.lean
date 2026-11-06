/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib.Tactic

public import CCDN.Algebra.MonomialEvaluationMatrix
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import CCDN.ForMathlib.Matrix

/-!
Independent rows can be selected from the finite evaluation matrix.
A nonzero annihilator gives the strict rank deficiency required by Bombieri--Vaaler.

The determinant argument selects independent evaluation rows. This module justifies why a
coefficient vector annihilating those rows vanishes on every point whose row they span.
-/

public section

namespace CCDN

open Matrix

variable {s N : ℕ}

private theorem dotProduct_eq_zero_of_mem_span 
    (A : Matrix (Fin s) (Fin N) ℚ) (v : CCDN.RatPoint N) (hAv : A *ᵥ v = 0)
    {r : CCDN.RatPoint N} (hr : r ∈ Submodule.span ℚ (Set.range A.row)) : r ⬝ᵥ v = 0 := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨i, rfl⟩ := hr
    exact congrFun hAv i
  | zero => simp
  | add x y hx hy ihx ihy => simp [add_dotProduct, ihx, ihy]
  | smul a x hx ih => simp [smul_dotProduct, ih]


/-- If an integer coefficient vector `v` annihilates the evaluation matrix of the monomials
`mon` at the points `points`, then the polynomial with coefficients `v` vanishes at every
integer point `x` whose monomial evaluation row lies in the `ℚ`-span of the matrix rows. -/
theorem vanishes_of_evaluation_row_mem_span {n N s : ℕ}
    (mon : Fin N → (Fin n →₀ ℕ)) (points : Fin s → (CCDN.IntPoint n))
    (v : CCDN.IntPoint N) (hAv : evaluationMatrix mon points *ᵥ v = 0)
    (x : CCDN.IntPoint n)
    (hx : (fun j => (((mon j).prod (fun k e => x k ^ e) : ℤ) : ℚ)) ∈
      Submodule.span ℚ (Set.range ((evaluationMatrix mon points).map ((↑) : ℤ → ℚ)).row)) :
    MvPolynomial.eval x (polynomialOfCoefficients mon v) = 0 := by
  have h := (by
              let inline_A := evaluationMatrix mon points
              have hAvQ : inline_A.map ((↑) : ℤ → ℚ) *ᵥ (fun j => (v j : ℚ)) = 0 := by
                ext i
                have hi := congrFun hAv i
                change ∑ j, (inline_A i j : ℚ) * (v j : ℚ) = 0
                exact_mod_cast hi
              have h := dotProduct_eq_zero_of_mem_span _ _ hAvQ hx
              simp only [dotProduct] at h ⊢
              exact_mod_cast h)
  simpa [polynomialOfCoefficients, MvPolynomial.eval_monomial, dotProduct, mul_comm] using h

end CCDN

namespace CCDN
open Matrix


/-- A nonzero relation on all columns forces every independent row family
to contain strictly fewer rows than columns. -/
private theorem independent_rows_lt_of_kernel {s N : ℕ} (A : Matrix (Fin s) (Fin N) ℚ)
    (hA : LinearIndependent ℚ A.row) (v : CCDN.RatPoint N) (hv : v ≠ 0)
    (hker : A *ᵥ v = 0) : s < N := by
  have hle : s ≤ N := by simpa using hA.fintype_card_le_finrank
  by_contra h
  have he : s = N := by omega
  subst s
  exact hv ((mulVec_injective_iff_isUnit.mpr (linearIndependent_row_iff_isUnit.mp hA))
    (hker.trans (mulVec_zero A).symm))

/-- If a rational matrix with `N` columns has a nonzero kernel vector, then some injectively
indexed family of `s < N` linearly independent rows spans its row space. -/
theorem exists_independent_spanning_rows_lt {t N : ℕ}
    (A : Matrix (Fin t) (Fin N) ℚ) (v : CCDN.RatPoint N) (hv : v ≠ 0)
    (hker : A *ᵥ v = 0) :
    ∃ (s : ℕ) (a : Fin s → Fin t), LinearIndependent ℚ (A.submatrix a id).row ∧
      Submodule.span ℚ (Set.range (A.submatrix a id).row) =
        Submodule.span ℚ (Set.range A.row) ∧ s < N := by
  obtain ⟨s, a, _, hi, hs⟩ := Matrix.exists_fin_linearIndependent_row_span_eq A
  refine ⟨s, a, hi, hs, independent_rows_lt_of_kernel _ hi v hv ?_⟩
  ext i
  exact congrFun hker (a i)

end CCDN
