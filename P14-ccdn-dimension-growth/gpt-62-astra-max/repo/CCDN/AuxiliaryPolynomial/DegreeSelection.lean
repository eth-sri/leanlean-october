/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.AuxiliaryPolynomial.RankComparison
import CCDN.AuxiliaryPolynomial.HypersurfacePositionHeight

@[expose] public section
namespace CCDN
noncomputable section

section

variable (n : ℕ)

abbrev shearPrice := Real.exp ((n+2 : ℝ)^2 / (n+1 : ℝ))

def hypersurfaceAbsoluteAuxiliaryConstant : ℝ := 5*(n+2 : ℝ) + 2 + thresholdCost n * (shearPrice n)^5

lemma hypersurfaceAbsoluteAuxiliaryConstant_one_le : 1 ≤ hypersurfaceAbsoluteAuxiliaryConstant n := by
  unfold hypersurfaceAbsoluteAuxiliaryConstant
  linarith [show 0 ≤ thresholdCost n * shearPrice n ^ 5 by positivity, Nat.cast_nonneg (α := ℝ) n]

end

/-- Choose the single degree at which the large auxiliary minor and the archimedean
bound are to be compared. The coarse `(d+1)^O(d)` shear cost is raised only to
`O(1/(d*degreeRoot))`, and so contributes a dimension constant. -/
theorem select_auxiliary_degree {n d : ℕ} (hd : 0 < d) {B A L H Q : ℝ}
    (hB : 1 ≤ B) (hA : 0 < A) (hL : 0 < L) (hH : 0 < H) (hQ : 0 ≤ Q)
    (hHL : H ≤ (d+1 : ℝ)^((n+2)*(d+1))*L) :
    let R := (d+1 : ℝ)^3*B
    ∃ M : ℕ, 2*(n+2)*d ≤ M ∧ (n+2 : ℝ)*Q ≤ M ∧ (d : ℝ)*Real.log R ≤ degreeRoot n d*M ∧
      thresholdCost n * auxMainTerm n d R A L < M ∧
      (M : ℝ) ≤ hypersurfaceAbsoluteAuxiliaryConstant n * auxDegreeBound n d B A H + (n+2 : ℝ)*Q := by
  let X := degreeRoot n d
  let E := shearPrice n
  let α := boxExponent n d
  let q := heightExponent n d
  let U := (d+1 : ℝ)
  let R := U^3*B
  let D := (d : ℝ)^(4 - 1/(n+1 : ℝ))
  let V := (d : ℝ)^(1 - 1/(n+1 : ℝ))
  let T := auxMainTerm n d B A H
  let C := hypersurfaceAbsoluteAuxiliaryConstant n
  have hB0 := zero_lt_one.trans_le hB
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hU : 1 ≤ U := by dsimp [U]; linarith
  have hUpos := zero_lt_one.trans_le hU
  have hR := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hU (n := 3)) hB
  have hX : 0 < X := by dsimp [X, degreeRoot]; positivity
  have hlogU : Real.log U ≤ (n+2 : ℝ)*X := by
    simpa only [Nat.cast_add, Nat.cast_one, show (n:ℝ)+1+1=n+2 by ring] using log_nat_add_one_le_root (r := n+1) (by omega) hd
  have hE : U^α ≤ E := by
    rw [Real.rpow_def_of_pos hUpos]; apply Real.exp_le_exp.mpr
    change _ ≤ (n+2 : ℝ)^2/(n+1 : ℝ)
    unfold α boxExponent; field_simp; nlinarith only [mul_le_mul_of_nonneg_right hlogU (show 0 ≤ (n+2:ℝ) by positivity)]
  have hV : V*X = d := by dsimp [V,X,degreeRoot]; rw [← Real.rpow_add hd0, sub_add_cancel, Real.rpow_one]
  have hVR : V*Real.log R ≤ V*Real.log B + 3*(n+2 : ℝ)*d := by
    dsimp only [R]; rw [Real.log_mul (by positivity) hB0.ne', Real.log_pow]
    linear_combination 3*V*hlogU + 3*(n+2 : ℝ)*hV
  have hT : 0 ≤ T := by dsimp [T,auxMainTerm]; positivity
  have hpow : H^q ≤ E^2 * L^q := by
    refine (Real.rpow_le_rpow hH.le hHL (by dsimp [q]; positivity)).trans ?_
    rw [Real.mul_rpow (by positivity) hL.le, ← Real.rpow_natCast_mul hUpos.le]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hL.le _)
    apply le_trans _ (pow_le_pow_left₀ (Real.rpow_nonneg hUpos.le _) hE 2)
    rw [← Real.rpow_mul_natCast hUpos.le]; apply Real.rpow_le_rpow_of_exponent_le hU
    dsimp only [q,α,heightExponent,boxExponent]; push_cast; field_simp
    nlinarith [mul_le_mul_of_nonneg_right hd1 (show 0 ≤ (n+2:ℝ) by positivity)]
  have hrpow : R^α ≤ E^3*B^α := by
    dsimp only [R]; rw [Real.mul_rpow (by positivity) hB0.le, ← Real.rpow_natCast_mul hUpos.le,
      mul_comm (↑(3:ℕ):ℝ) α, Real.rpow_mul_natCast hUpos.le]; gcongr
  have hmain : auxMainTerm n d R A L ≤ E^5*T := by
    change D * A * R^α / L^q ≤ E^5*(D*A*B^α/H^q)
    field_simp
    have hh := mul_le_mul hrpow hpow (Real.rpow_nonneg hH.le _) (by positivity)
    linear_combination D*hh
  have hV0 : 0 ≤ V := by dsimp [V]; positivity
  have hVR0 : 0 ≤ V*Real.log R := mul_nonneg hV0 (Real.log_nonneg hR)
  have hq0 : 0 ≤ (n+2 : ℝ)*Q := by positivity
  obtain ⟨M,hM,hl,ht,hb⟩ := auxiliary_integer_degree_selection (2*(n+2)*d) (add_nonneg hVR0 hq0)
    (show 0 ≤ thresholdCost n * auxMainTerm n d R A L by dsimp [auxMainTerm]; positivity)
  refine ⟨M,hM,by linarith,?_,ht,?_⟩
  · change (d:ℝ)*Real.log R ≤ X*M
    nlinarith only [mul_le_mul_of_nonneg_left (show V*Real.log R ≤ M by linarith) hX.le, congrArg (· * Real.log R) hV]
  have hdD : (d:ℝ) ≤ D := le_rpow_four_sub_inv hd
  have hcD : 5*(n+2 : ℝ)+2 ≤ C := le_add_of_nonneg_right (by positivity : 0 ≤ thresholdCost n * shearPrice n^5)
  have hcT : thresholdCost n * E^5 ≤ C := le_add_of_nonneg_left (by positivity : 0 ≤ 5*(n+2 : ℝ)+2)
  have hc := hypersurfaceAbsoluteAuxiliaryConstant_one_le n
  push_cast at hb
  change (M:ℝ) ≤ C*(T+V*Real.log B+D) + _
  nlinarith only [hb,hVR, mul_le_mul_of_nonneg_left hmain (show 0 ≤ thresholdCost n from (Real.exp_pos _).le),
    mul_le_mul_of_nonneg_right hcT hT, mul_le_mul_of_nonneg_right hc (mul_nonneg hV0 (Real.log_nonneg hB)),
    mul_le_mul_of_nonneg_right hcD (zero_le_one.trans (hd1.trans hdD)), hd1.trans hdD,
    mul_le_mul_of_nonneg_left hdD (show 0 ≤ 5*(n+2:ℝ) by positivity)]

end
end CCDN
