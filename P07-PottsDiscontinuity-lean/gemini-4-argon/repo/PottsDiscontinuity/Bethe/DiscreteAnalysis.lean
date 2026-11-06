module

public import Mathlib
public import PottsDiscontinuity.Bethe.ThetaK

/-!
# Discrete Bethe matrix estimates independent of `ρ`

This file isolates the sign and calculus estimates for the phase difference used
in the discrete diagonal-dominance argument.  It does not include the later
Riemann-sum estimates involving `ρ`.
-/

@[expose] public section

open scoped BigOperators
open Set

namespace PottsDiscontinuity.Bethe

/-- The phase difference used to control the off-diagonal entries. -/
noncomputable def discreteBetheG (Δ x y : ℝ) : ℝ :=
  theta Δ x y - theta Δ (-x) y

/-- If the cosine argument is larger, the corresponding `Xi` kernel is larger. -/
theorem Xi_le_of_cos_le {μ a b : ℝ} (hμ : 0 < μ)
    (hcos : Real.cos b ≤ Real.cos a) : Xi μ b ≤ Xi μ a := by
  have hs : 0 < Real.sinh μ := Real.sinh_pos_iff.mpr hμ
  have hc : 1 < Real.cosh μ := Real.one_lt_cosh.mpr hμ.ne'
  have hda : 0 < Real.cosh μ - Real.cos a := by linarith [Real.cos_le_one a]
  have hdb : 0 < Real.cosh μ - Real.cos b := by linarith [Real.cos_le_one b]
  exact (div_le_div_iff₀ hdb hda).2 (mul_le_mul_of_nonneg_left (by linarith) hs.le)

/-- The derivative of `G(k(α),k(β))` in `β`, written as a difference of two `Xi` kernels. -/
theorem hasDerivAt_discreteBetheG_kMap {Δ : ℝ} (hΔ : Δ < -1)
    (α β : ℝ) :
    HasDerivAt (fun t => discreteBetheG Δ (kMap (lamOf Δ) α) (kMap (lamOf Δ) t))
      (Xi (2 * lamOf Δ) (α - β) - Xi (2 * lamOf Δ) (-α - β)) β := by
  let lam := lamOf Δ
  have hlam : 0 < 2 * lam := by linarith [lamOf_pos hΔ]
  rw [show (fun t => discreteBetheG Δ (kMap lam α) (kMap lam t)) =
      fun t => kMap (2 * lam) (-α - t) - kMap (2 * lam) (α - t) by
    funext t; unfold discreteBetheG
    rw [← kMap_neg lam α, theta_kMap_lamOf hΔ α t, theta_kMap_lamOf hΔ (-α) t]; ring]
  convert ((hasDerivAt_kMap hlam (-α - β)).comp_const_sub (-α) β).sub
    ((hasDerivAt_kMap hlam (α - β)).comp_const_sub α β) using 1
  simp only [lam]; ring

/-- The endpoint difference of `G` has a one-arctangent closed form. -/
theorem discreteBetheG_endpoint_formula {Δ : ℝ} (hΔ : Δ < -1)
    {x : ℝ} (hx : x ∈ Icc (-Real.pi) 0) :
     discreteBetheG Δ x 0 - discreteBetheG Δ x (-Real.pi) =
      4 * Real.arctan ((-Real.sin x) /
        (2 * (-Δ) * (Real.cos x - Δ))) := by
  let t := -Real.sin x
  let dm := Real.cos x - 1 - 2 * Δ
  let dp := Real.cos x + 1 - 2 * Δ
  have ht : 0 ≤ t := by dsimp [t]; linarith [Real.sin_nonpos_of_nonpos_of_neg_pi_le hx.2 hx.1]
  have hdm : 0 < dm := by dsimp [dm]; linarith [Real.neg_one_le_cos x]
  have hdp : 0 < dp := by dsimp [dp]; linarith [Real.neg_one_le_cos x]
  have hraw' : discreteBetheG Δ x 0 - discreteBetheG Δ x (-Real.pi) =
      4 * (Real.arctan (t / dm) + Real.arctan (-t / dp)) := by
    rw [show discreteBetheG Δ x 0 - discreteBetheG Δ x (-Real.pi) =
        4 * (Real.arctan (Real.sin x / dp) - Real.arctan (Real.sin x / dm)) by
      unfold discreteBetheG theta
      simp only [Real.sin_zero, Real.cos_zero, Real.sin_neg, Real.cos_neg,
        Real.sin_pi, Real.cos_pi, sub_zero, neg_zero, neg_div, Real.arctan_neg]
      dsimp [dp, dm]; ring_nf,
      show Real.sin x = -t by dsimp [t]; ring]
    simp only [neg_div, Real.arctan_neg]; ring
  have hprod : (t / dm) * (-t / dp) < 1 := by
    linarith [mul_nonpos_of_nonneg_of_nonpos (div_nonneg ht hdm.le)
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hdp.le)]
  rw [hraw', Real.arctan_add hprod]
  refine congrArg (fun u : ℝ => 4 * Real.arctan u) ?_
  have hcos : 0 < Real.cos x - Δ := by linarith [Real.neg_one_le_cos x]
  have hden : 2 * (-Δ) * (Real.cos x - Δ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by linarith)) hcos.ne'
  have hden2 : dm * dp + t ^ 2 ≠ 0 := by positivity
  field_simp [hdm.ne', hdp.ne', hden, hden2]
  rw [show dm * dp - -t ^ 2 = 4 * (-Δ) * (Real.cos x - Δ) by
    dsimp [dm, dp, t]; nlinarith [Real.sin_sq_add_cos_sq x]]
  field_simp [(by linarith : Δ ≠ 0), hcos.ne']; ring

/-- The calculus bound in Lemma 2.5.  Its constant is valid as printed when
`Δ ≤ Δ₀ < -1`; the source line stating only `Δ₀ < 1` is insufficient. -/
theorem discreteBetheG_endpoint_bound {Δ Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1)
    (hΔ : Δ ≤ Δ₀) {x : ℝ} (hx : x ∈ Icc (-Real.pi) 0) :
    discreteBetheG Δ x 0 - discreteBetheG Δ x (-Real.pi) ≤
      4 * Real.arctan (1 / (2 * |Δ₀| * Real.sqrt (Δ₀ ^ 2 - 1))) ∧
    4 * Real.arctan (1 / (2 * |Δ₀| * Real.sqrt (Δ₀ ^ 2 - 1))) < 2 * Real.pi := by
  have hΔ' : Δ < -1 := lt_of_le_of_lt hΔ hΔ₀
  rw [discreteBetheG_endpoint_formula hΔ' hx]
  let d := -Δ
  let d₀ := -Δ₀
  let c := Real.cos x
  let t := -Real.sin x
  have hd₀ : 1 < d₀ := by dsimp [d₀]; linarith
  have hd : d₀ ≤ d := by dsimp [d, d₀]; linarith
  have hc : -1 ≤ c := Real.neg_one_le_cos x
  have ht : 0 ≤ t := neg_nonneg.mpr (Real.sin_nonpos_of_nonpos_of_neg_pi_le hx.2 hx.1)
  have hcd : 0 < c + d := by linarith
  have hs₀ : 0 < d₀ ^ 2 - 1 := by nlinarith
  have hs : 0 < d ^ 2 - 1 := by nlinarith
  let w₀ := Real.sqrt (d₀ ^ 2 - 1)
  let w := Real.sqrt (d ^ 2 - 1)
  have hw₀ : 0 < w₀ := Real.sqrt_pos.mpr hs₀
  have hw : 0 < w := Real.sqrt_pos.mpr hs
  have hwle : w₀ ≤ w := Real.sqrt_le_sqrt (by nlinarith)
  have hsquare : (t * w) ^ 2 ≤ (c + d) ^ 2 := by
    dsimp [t, c, w]; rw [mul_pow, Real.sq_sqrt hs.le]
    nlinarith [sq_nonneg (Real.cos x * d + 1), Real.sin_sq_add_cos_sq x]
  have hroot : t * w ≤ c + d := by nlinarith [mul_nonneg ht hw.le]
  have hdpos : 0 < d := by linarith
  have harg : t / (2 * d * (c + d)) ≤ 1 / (2 * d₀ * w₀) := by
    rw [show t / (2 * d * (c + d)) = (1 / (2 * d)) * (t / (c + d)) by field_simp]
    exact (mul_le_mul_of_nonneg_left ((div_le_div_iff₀ hcd hw).2 (by nlinarith)) (by positivity)).trans
      ((by field_simp : (1 / (2 * d)) * (1 / w) = 1 / (2 * d * w)).le.trans
        (one_div_le_one_div_of_le (by positivity)
          (by nlinarith [mul_le_mul hd hwle hw₀.le hdpos.le])))
  have harg' : (-Real.sin x) / (2 * (-Δ) * (Real.cos x - Δ)) ≤
      1 / (2 * |Δ₀| * Real.sqrt (Δ₀ ^ 2 - 1)) := by
    simpa only [t, d, c, d₀, w₀, abs_of_neg (by linarith : Δ₀ < 0),
      show c + -Δ = Real.cos x - Δ by ring, show (-Δ₀) ^ 2 = Δ₀ ^ 2 by ring] using harg
  exact ⟨mul_le_mul_of_nonneg_left (Real.arctan_le_arctan_iff.2 harg') (by norm_num),
    by nlinarith [Real.arctan_lt_pi_div_two (1 / (2 * |Δ₀| * Real.sqrt (Δ₀ ^ 2 - 1))), Real.pi_pos]⟩

/-- Abstract Levy--Desplanques criterion: strict row diagonal dominance makes a real
square matrix invertible. -/
theorem discrete_strict_row_diagonal_dominance_invertible {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (h : ∀ i, ∑ j ∈ Finset.univ.erase i, |A i j| < |A i i|) : A.det ≠ 0 :=
  det_ne_zero_of_sum_row_lt_diag fun i => by simpa only [Real.norm_eq_abs] using h i

end PottsDiscontinuity.Bethe
