/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Surface.ResidueCover
import CCDN.Analysis.SmallDegreeSurfaceNumerics

/-! The number of primes is fixed. A modulus of up to 18 primes of size
`O(B^(1/40))` costs at most `O(B^(9/20))`; the deletion edge counts are still sublinear. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- Uniform coefficient for the logarithmic budget of the prime window. -/
abbrev residueLogScale (N : ℕ) (U : ℝ) : ℝ := 1 + N * (Real.log U + 1)

lemma surfaceResidueLogBudget_le {B U : ℝ} (hB : 1 ≤ B) (hU : 1 ≤ U)
    (W : Finset ℕ) (hW : ∀ p ∈ W, p.Prime) (hupper : ∀ p ∈ W, (p : ℝ) ≤ U * B ^ (1 / 40 : ℝ)) :
    surfaceResidueLogBudget B W ≤ residueLogScale W.card U * (Real.log B + 1) := by
  have hlogB := Real.log_nonneg hB
  have hlogU := Real.log_nonneg hU
  have h (p) (hp : p ∈ W) : Real.log p ≤ (Real.log U + 1) * (Real.log B + 1) := by
    have hi := Real.log_le_log (by exact_mod_cast (hW p hp).pos) (hupper p hp)
    rw [Real.log_mul (by linarith) (by positivity), Real.log_rpow (by linarith)] at hi
    nlinarith
  have hh := sum_le_sum h
  simp only [sum_const, nsmul_eq_mul] at hh
  unfold surfaceResidueLogBudget residueLogScale
  linarith

/-- A window with a bounded number of such primes gives a uniform linear
bound for the residual locus. -/
theorem surface_residue_linear_count (d : ℕ) (hd : 5 ≤ d)
    (A U : ℝ) (hA : 0 ≤ A) (hU : 1 ≤ U) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : MvPolynomial (Fin 3) ℤ), f.totalDegree = d →
      ∀ B : ℝ, 1 ≤ B → ∀ W : Finset ℕ, W.card = N →
      ∀ hW : ∀ p ∈ W, p.Prime,
      (∀ p ∈ W, (p : ℝ) ≤ U * B ^ (1 / 40 : ℝ)) →
      ∀ F : SurfaceCongruenceFamily f B A,
      Irreducible (map (Int.castRingHom ℚ) f) →
      ∀ (S : Finset (Ideal (CoordinatePolynomial 3))) (δ : Ideal (CoordinatePolynomial 3) → ℕ),
      (∀ I ∈ S, IsSurfaceCurve (map (Int.castRingHom ℚ) f) I (δ I)) →
      (count (surfaceResidueResidualLocus F S W hW) B : ℝ) ≤ C * B := by
  let T := residueLogScale N U
  let E := logarithmicBoxConstant 2 (3 / 40)
  let L := (N : ℝ) * (2 * (d : ℝ)) ^ N * (2 * d * A ^ 2)
  let C := L * T ^ 2 * (U + 1) * U ^ 36
  have hT : 0 ≤ T := by dsimp [T, residueLogScale]; have := Real.log_nonneg hU; positivity
  have hC : 0 ≤ C := by positivity
  refine ⟨C * E + 1, by positivity, ?_⟩
  intro f hfd B hB W hcard hW hupper F hir S δ hS
  have hB0 : 0 < B := by linarith
  let Y := B ^ (1 / 40 : ℝ)
  let U' := U * Y
  let X := U' ^ 18
  have hY : 1 ≤ Y := Real.one_le_rpow hB (by norm_num)
  have hU' : 1 ≤ U' := one_le_mul_of_one_le_of_one_le hU hY
  have hy (k : ℕ) : Y ^ k = B ^ ((1 / 40 : ℝ) * k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB0.le]
  have hX : B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) ≤ X := calc
    _ ≤ B ^ (9 / 20 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB
      (surface_inverse_sqrt_le_nine_twentieths (hfd ▸ hd))
    _ = Y ^ 18 := by rw [hy]; norm_num
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (le_mul_of_one_le_left (by positivity) hU) _
  have hprod (R : Finset ℕ) (hR : R ⊆ W) (hRc : R.card ≤ 18) :
      (∏ p ∈ R, (p : ℝ)) ≤ X := calc
    _ ≤ ∏ _p ∈ R, U' := prod_le_prod₀ (fun _ _ => by positivity) (fun p hp => hupper p (hR hp))
    _ = U' ^ R.card := prod_const _
    _ ≤ _ := pow_le_pow_right₀ hU' hRc
  have hpoly := surface_residue_residual_count_le F hA hB (by omega) (zero_le_one.trans hU')
    hX hir S δ hS W hW hupper hprod
  have hlog := surfaceResidueLogBudget_le hB hU W hW hupper
  rw [hcard] at hlog
  have hlogB := Real.log_nonneg hB
  have hXe : (U' + 1) * X ^ 2 ≤ (U + 1) * U ^ 36 * B ^ (37 / 40 : ℝ) := calc
    _ ≤ ((U + 1) * Y) * X ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg X)
      dsimp [U']; linarith
    _ = (U + 1) * U ^ 36 * Y ^ 37 := by dsimp [X, U']; ring
    _ = _ := by rw [hy]; norm_num
  have hweight := box_polylog_weight 2 (by norm_num : (0 : ℝ) < 3 / 40) hB
    (t := 37 / 40) (by norm_num)
  have hT0 : 0 ≤ surfaceResidueLogBudget B W := by unfold surfaceResidueLogBudget; positivity
  apply hpoly.trans
  rw [hcard, hfd]
  calc
    _ = L * (surfaceResidueLogBudget B W) ^ 2 * ((U' + 1) * X ^ 2) := by
      dsimp only [L, residueEdgeBudget]; ring
    _ ≤ L * (T * (Real.log B + 1)) ^ 2 * ((U + 1) * U ^ 36 * B ^ (37 / 40 : ℝ)) := by gcongr
    _ = C * (B ^ (37 / 40 : ℝ) * (Real.log B + 1) ^ 2) := by dsimp only [C]; ring
    _ ≤ C * (E * B) := mul_le_mul_of_nonneg_left hweight hC
    _ ≤ _ := by linarith

end
end CCDN
