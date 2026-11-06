/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.MonomialEvaluationMatrix
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import CCDN.ForMathlib.Matrix

/-!
Independent rows can be selected from the finite evaluation matrix.
A nonzero annihilator gives the strict rank deficiency required by Bombieri--Vaaler.

The determinant argument selects independent evaluation rows. This module justifies why a
coefficient vector annihilating those rows vanishes on every point whose row they span.
-/

@[expose] public section

namespace CCDN

open Matrix

private theorem dotProduct_eq_zero_of_mem_span {s N : ℕ}
    (A : Matrix (Fin s) (Fin N) ℚ) (v : Fin N → ℚ) (hAv : A *ᵥ v = 0)
    {r : Fin N → ℚ} (hr : r ∈ Submodule.span ℚ (Set.range A.row)) : r ⬝ᵥ v = 0 := by
  induction hr using Submodule.span_induction with
  | mem r hr => obtain ⟨i, rfl⟩ := hr; exact congrFun hAv i
  | zero => simp
  | add x y hx hy ihx ihy => simp [add_dotProduct, ihx, ihy]
  | smul a x hx ih => simp [smul_dotProduct, ih]

/-- If an integer coefficient vector `v` annihilates the evaluation matrix of the monomials
`mon` at the points `points`, then the polynomial with coefficients `v` vanishes at every
integer point `x` whose monomial evaluation row lies in the `ℚ`-span of the matrix rows. -/
theorem vanishes_of_evaluation_row_mem_span {n N s : ℕ}
    (mon : Fin N → (Fin n →₀ ℕ)) (points : Fin s → (Fin n → ℤ))
    (v : Fin N → ℤ) (hAv : evaluationMatrix mon points *ᵥ v = 0)
    (x : Fin n → ℤ)
    (hx : (fun j => (((mon j).prod (fun k e => x k ^ e) : ℤ) : ℚ)) ∈
      Submodule.span ℚ (Set.range ((evaluationMatrix mon points).map ((↑) : ℤ → ℚ)).row)) :
    MvPolynomial.eval x (polynomialOfCoefficients mon v) = 0 := by
  have hAvQ : (evaluationMatrix mon points).map ((↑) : ℤ → ℚ) *ᵥ (fun j => (v j : ℚ)) = 0 := by
    ext i
    change ∑ j, (evaluationMatrix mon points i j : ℚ) * (v j : ℚ) = 0
    exact_mod_cast congrFun hAv i
  have h : (fun j => (mon j).prod fun k e => x k ^ e) ⬝ᵥ v = 0 := by
    have h0 := dotProduct_eq_zero_of_mem_span _ _ hAvQ hx
    simp only [dotProduct] at h0 ⊢
    exact_mod_cast h0
  simpa [polynomialOfCoefficients, MvPolynomial.eval_monomial, dotProduct, mul_comm] using h

/-- Every matrix with `N` columns has an injectively indexed family of `s ≤ N` linearly
independent rows spanning its row space. -/
theorem exists_independent_spanning_rows {F ι : Type*} [Field F] {N : ℕ}
    (A : Matrix ι (Fin N) F) :
    ∃ (s : ℕ) (a : Fin s → ι), Function.Injective a ∧
      LinearIndependent F (A.submatrix a id).row ∧
      Submodule.span F (Set.range (A.submatrix a id).row) =
        Submodule.span F (Set.range A.row) ∧ s ≤ N := by
  obtain ⟨s, a, ha, hli, hs⟩ := Matrix.exists_fin_linearIndependent_row_span_eq A
  exact ⟨s, a, ha, hli, hs, by simpa using hli.fintype_card_le_finrank⟩

/-- If a rational matrix with `N` columns has a nonzero kernel vector, then some injectively
indexed family of `s < N` linearly independent rows spans its row space. -/
theorem exists_independent_spanning_rows_lt {t N : ℕ}
    (A : Matrix (Fin t) (Fin N) ℚ) (v : Fin N → ℚ) (hv : v ≠ 0)
    (hker : A *ᵥ v = 0) :
    ∃ (s : ℕ) (a : Fin s → Fin t), Function.Injective a ∧
      LinearIndependent ℚ (A.submatrix a id).row ∧
      Submodule.span ℚ (Set.range (A.submatrix a id).row) =
        Submodule.span ℚ (Set.range A.row) ∧ s < N := by
  obtain ⟨s, a, ha, hi, hs, hle⟩ := exists_independent_spanning_rows A
  refine ⟨s, a, ha, hi, hs, ?_⟩
  by_contra h
  have he : s = N := by omega
  by_cases hs0 : s = 0
  · exact hv (funext fun j => by have := j.isLt; omega)
  let : Nonempty (Fin s) := ⟨⟨0, by omega⟩⟩
  have hspan : Submodule.span ℚ (Set.range (A.submatrix a id).row) = ⊤ :=
    hi.span_eq_top_of_card_eq_finrank (by simpa using he)
  exact hv <| funext fun j => by
    simpa using dotProduct_eq_zero_of_mem_span (A.submatrix a id) v
      (funext fun i => congrFun hker (a i)) (r := Pi.single j 1) (by rw [hspan]; trivial)

end CCDN
