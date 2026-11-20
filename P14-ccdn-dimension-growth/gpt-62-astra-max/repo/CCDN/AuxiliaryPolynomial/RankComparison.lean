/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Algebra.Equations
public import CCDN.Determinant.HypersurfaceDeterminantRank
public import CCDN.AuxiliaryPolynomial.Nonmultiple
public import CCDN.Determinant.HomogeneousDeterminantComparison
public import CCDN.AuxiliaryPolynomial.HypersurfaceSmallHeightDegree
import CCDN.AuxiliaryPolynomial.HypersurfaceNormalizedComparison
import CCDN.AuxiliaryPolynomial.HypersurfaceRankArchimedean
import CCDN.AuxiliaryPolynomial.HypersurfaceKernelRatio
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {n s M t d : ℕ}

/-- An arithmetic lower bound furnished by the ordinary good primes and, optionally,
by primes with prescribed smooth residues. `Q` accounts for the linear error at the latter. -/
def EvaluationLower (z : Fin t → IntPoint (n+3)) (d : ℕ) (A Q : ℝ) : Prop :=
  ∀ {s N M : ℕ} (a : Fin s → Fin t) (F : Fin N → IntegerPolynomial (n+3)), 0 < s →
    (∀ j, (F j).IsHomogeneous M) →
    let T := Matrix.of fun i j => eval (z (a i)) (F j)
    LinearIndependent ℚ (T.map ((↑) : ℤ → ℚ)).row →
    hypersurfaceRankLowerBound n s d (Real.log A) ≤ Real.log (Int.Matrix.minorGcd T) + (n+2 : ℝ)*s*Q

section

variable (n : ℕ)

abbrev normalizedError := hypersurfaceDeterminantError n + (n+2 : ℝ)*(n+1 : ℝ) / factorialRoot n
abbrev thresholdCost := Real.exp (hypersurfaceSmallHeightError (n+1) (normalizedError n))

end

/-- The archimedean upper bound cannot be negative. For `M ≥ 2(r+1)d`
this forces the leading coefficient into the small-height range. -/
private lemma rank_height_cap (hd : 0 < d) (hM : 2*(n+2)*d ≤ M)
    (hr : s + formDim (n+2) (M-d) = formDim (n+2) M) {B L : ℝ} (hB : 1 ≤ B) (hL : 1 ≤ L)
    (h : 0 ≤ Real.log s.factorial + s*M*Real.log B - ((formDim (n+2) M : ℝ)-s)*Real.log L) :
    Real.log L ≤ 2*d*(n+2 : ℝ)*Real.log (4*B) := by
  let N := formDim (n+2) M
  let K := formDim (n+2) (M-d)
  have hdM : d ≤ M := by nlinarith
  have hsN := Nat.le.intro hr
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (hd.trans_le hdM).trans_le (hypersurface_rank_ge_degree_parameter (r := n+1) (by omega) hd hdM hr)
  have hM0 : (0 : ℝ) < M := by bound
  have hMr : 2*(n+2 : ℝ)*d ≤ M := by exact_mod_cast hM
  have hk := hypersurface_kernel_ratio_lower (r := n+1) hd hdM hr
  push_cast at hk
  have hK : (M : ℝ)*s ≤ (2*(n+2 : ℝ)*d)*K := by
    field_simp at hk
    nlinarith only [hk, mul_le_mul_of_nonneg_right hMr hs0.le]
  have hN : N ≤ 4^M := calc
    _ ≤ 2^(n+2+M) := Nat.choose_le_two_pow _ _
    _ ≤ 2^(2*M) := Nat.pow_le_pow_right (by decide) (by nlinarith)
    _ = _ := by rw [pow_mul]; norm_num
  have hf := by
    have hh : (s.factorial : ℝ) ≤ ((4 : ℝ)^M)^s := by
      exact_mod_cast (Nat.factorial_le_pow s).trans (Nat.pow_le_pow_left (hsN.trans hN) _)
    simpa using Real.log_le_log (by positivity) hh
  have he : (s : ℝ) + K = N := by exact_mod_cast hr
  change 0 ≤ _ + _ - (N-s)*Real.log L at h
  rw [show (N:ℝ)-s = K by linarith] at h
  have h₁ : (K : ℝ)*Real.log L ≤ s*M*Real.log (4*B) := by rw [Real.log_mul (by norm_num) (by linarith)]; linarith
  apply le_of_mul_le_mul_left (a := (M:ℝ)*s) _ (mul_pos hM0 hs0)
  nlinarith only [mul_le_mul_of_nonneg_right hK (Real.log_nonneg hL), mul_le_mul_of_nonneg_left h₁ (show 0 ≤ 2*(n+2 : ℝ)*d by positivity)]

/-- Compare the same maximal minors, for either projective points or a lifted affine residue class. -/
theorem auxiliary_at_degree {M : ℕ} (order : MonomialOrder (Fin (n+3)))
    (f : IntegerPolynomial (n+3)) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d)
    (z : Fin t → IntPoint (n+3)) (hz : ∀ i, eval (z i) f = 0)
    {B R A Q : ℝ} (hB : 1 ≤ B) (hbox : ∀ i, InBox (z i) B) (hR : 4*B ≤ R) (hA : 0 < A)
    (hdet : EvaluationLower z d A Q) (hM : 2*(n+2)*d ≤ M) (hQ : (n+2 : ℝ)*Q ≤ M)
    (hscale : (d : ℝ)*Real.log R ≤ degreeRoot n d * M)
    (hth : thresholdCost n * auxMainTerm n d R A |((order.leadingCoeff f : ℤ) : ℝ)| < M) :
    ∃ g, IsPointAuxiliary f g M z := by
  classical
  by_contra hnone
  have hdM : d ≤ M := by nlinarith
  let L := |((order.leadingCoeff f : ℤ) : ℝ)|
  have hL : 1 ≤ L := by dsimp only [L]; exact_mod_cast Int.one_le_abs (order.leadingCoeff_ne_zero_iff.mpr hf0)
  have hR1 : 1 ≤ R := by linarith
  obtain ⟨s,a,-,-,hr,hi,hu⟩ := homogeneous_no_auxiliary_box_comparison order f hf hf0 hdM z hz hB hbox
    (dvd_of_not_exists_isPointAuxiliary hnone)
  have hs := (hd.trans_le hdM).trans_le (hypersurface_rank_ge_degree_parameter (r := n+1) (by omega) hd hdM hr)
  let T := evaluationMatrix (homogeneousMonomials (n+2) M) (z ∘ a)
  let F := fun j => (monomial (homogeneousMonomials (n+2) M j) 1 : IntegerPolynomial (n+3))
  have he : (Matrix.of fun i j => eval (z (a i)) (F j)) = T := by ext; simp [F,T,evaluationMatrix,eval_monomial]
  have hl := hdet a F hs (fun j => isHomogeneous_monomial _ (homogeneousMonomials_degree (n+2) M j)) (he ▸ hi)
  rw [he] at hl
  have hcap := rank_height_cap hd hM hr hB hL ((Real.log_nonneg (show (1:ℝ) ≤ Int.Matrix.minorGcd T by exact_mod_cast Int.Matrix.one_le_minorGcd hi)).trans hu)
  have hlog := Real.log_le_log (by positivity : 0 < 4*B) hR
  rw [Real.log_mul (by norm_num) (by linarith)] at hlog
  have hone : (1 : ℝ) ≤ Real.log 4 := (Real.le_log_iff_exp_le (by norm_num)).mpr (by linarith [Real.exp_one_lt_d9])
  have hnR : (n:ℝ)+1+1=n+2 := by ring
  have hcomp := hypersurface_rank_comparison_normalized (r := n+1) (by omega) hd hdM hr R L A (hypersurfaceDeterminantError n) (by
    simp only [Nat.cast_add,Nat.cast_one,hnR]
    change hypersurfaceRankLowerBound n s d (Real.log A) ≤ _
    nlinarith only [hl, hu, mul_le_mul_of_nonneg_right hQ (Nat.cast_nonneg (α := ℝ) s),
      mul_le_mul_of_nonneg_left (show Real.log B+1 ≤ Real.log R by linarith) (show 0 ≤ (s:ℝ)*M by positivity)])
  have hh := hypersurface_small_height_log_degree_bound (r := n+1) (by omega) hd (show 2*d ≤ M by nlinarith) hr
    R L A (normalizedError n) hR1 hL (by
      push_cast; rw [hnR]; exact hcap.trans (by gcongr)) (by simpa only [Nat.cast_add, Nat.cast_one] using hscale) (by simpa only [Nat.cast_add, Nat.cast_one, hnR, normalizedError] using hcomp)
  have hb := hypersurface_degree_bound_of_log_bound hd ((hd.trans_le hdM)) (by linarith : 0 < R) (by linarith : 0 < L) hA hh
  have hcontra : (M : ℝ) ≤ thresholdCost n * auxMainTerm n d R A L := by
    simp only [Nat.cast_add,Nat.cast_one,hnR] at hb
    convert hb using 1; unfold auxMainTerm thresholdCost; ring
  exact hth.not_ge hcontra

end
end CCDN
