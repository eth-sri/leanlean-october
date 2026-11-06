/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.RankNumerics

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Determinant.HypersurfaceHeightDeterminant
import CCDN.Determinant.HomogeneousDeterminantComparison

/-! Exact-rank Bombieri--Vaaler comparison for higher-dimensional hypersurfaces.
Absence of an auxiliary polynomial forces the explicit numerical inequality. -/

public section
namespace CCDN
open MvPolynomial

/-- The Hilbert function `s` of a degree-`d` hypersurface in `n + 3` variables, defined by
`s + C(n + 2 + (M - d), M - d) = C(n + 2 + M, M)`, is positive in every degree `M ≥ d`. -/
lemma hypersurface_homogeneous_rank_pos {n d M s : ℕ} (hd : 0 < d) (hdM : d ≤ M)
    (hr : s + (n + 2 + (M - d)).choose (M - d) = (n + 2 + M).choose M) : 0 < s := by
  rw [← Nat.choose_symm_add  ,
    ← Nat.choose_symm_add  ] at hr
  have hmon := Nat.choose_le_choose (n + 2)
    (show n + 2 + (M - d) ≤ n + 1 + M by omega)
  have hpascal : (n + 2 + M).choose (n + 2) =
      (n + 1 + M).choose (n + 1) + (n + 1 + M).choose (n + 2) := by
    grind
  have hp : 0 < (n + 1 + M).choose (n + 1) := Nat.choose_pos (by omega)
  omega

/-- With no auxiliary nonmultiple of degree M, the exact homogeneous Hilbert
rank satisfies the archimedean/nonarchimedean determinant comparison. -/
theorem hypersurface_no_auxiliary_height_comparison
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n d M t : ℕ}
    (order : MonomialOrder (Fin (n + 3))) (f : CCDN.IntegerPolynomial (n + 3))
    (hf : f.IsHomogeneous d) (hd : 0 < d) (hdM : d ≤ M)
    (hir : Irreducible (map (Int.castRingHom K) f))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : CoefficientHeightLE f H)
    {B : ℝ} {z : Fin t → IntPoint (n + 3)} (hzB : IsPrimitiveBoxZeroFamily f B z)
    (hrel : ∀ g : CCDN.IntegerPolynomial (n + 3), g.IsHomogeneous M →
      (∀ i, eval (z i) g = 0) → f ∣ g) :
    ∃ s : ℕ, 0 < s ∧ s + (n + 2 + (M - d)).choose (M - d) = (n + 2 + M).choose M ∧
      factorialRoot n / (n + 2 : ℝ) *
        ↑s ^ (1 + 1 / (n + 1 : ℝ)) *
          (Real.log s - (n + 1 : ℝ) * (4 * Real.log d + Real.log (1 + Real.log H / ↑d ^ 2)) -
            hypersurfaceHeightDeterminantError n) ≤
        Real.log ↑s.factorial / 2 + ↑s / 2 * Real.log ((n + 2 + M).choose M) +
          s * M * Real.log B - (((n + 2 + M).choose M : ℝ) - s) *
            Real.log |((order.leadingCoeff f : ℤ) : ℝ)| := by
  have hf0 : f ≠ 0 := by aesop
  obtain ⟨s, a, hr, hi, hupper⟩ :=
    homogeneous_no_auxiliary_box_comparison order f hf hf0 hdM z hzB.eval_eq_zero
      hzB.one_le_radius hzB.abs_le hrel
  have hs := hypersurface_homogeneous_rank_pos hd hdM hr
  refine ⟨s, hs, hr, ?_⟩
  let F := fun j => (monomial (homogeneousMonomials (n + 2) M j) 1 : CCDN.IntegerPolynomial (n + 3))
  have hF : ∀ j, (F j).IsHomogeneous M := fun j =>
    isHomogeneous_monomial _ (homogeneousMonomials_degree (n + 2) M j)
  have he : (Matrix.of fun i j => eval ((z ∘ a) i) (F j)) =
      evaluationMatrix (homogeneousMonomials (n + 2) M) (z ∘ a) := by
    ext i j
    simp [F, evaluationMatrix, eval_monomial]
  have hi' : LinearIndependent ℚ
      ((Matrix.of fun i j => eval ((z ∘ a) i) (F j)).map ((↑) : ℤ → ℚ)).row := by
    rw [he]
    exact hi
  have hlower := hypersurface_determinant_log_lower_height (z := z ∘ a) hs f hf hd hir H hH
    hcoeff ⟨hF, fun i => hzB.primitive (a i), fun i => hzB.eval_eq_zero (a i), hi'⟩
  rw [he] at hlower
  exact hlower.trans hupper

end CCDN
