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
  have hs : 0 < Real.sinh μ := by positivity
  have hc : 1 < Real.cosh μ := by aesop
  have hda : 0 < Real.cosh μ - Real.cos a := by
    have := Real.cos_le_one a
    linarith
  have hdb : 0 < Real.cosh μ - Real.cos b := by
    linarith
  exact (div_le_div_iff₀ hdb hda).2 (mul_le_mul_of_nonneg_left (by linarith) hs.le)

section
variable {Δ : ℝ} (hΔ : Δ < -1)
include hΔ
/-- The derivative of `G(k(α),k(β))` in `β`, written as a difference of two `Xi` kernels. -/
theorem hasDerivAt_discreteBetheG_kMap (α β : ℝ) :
    HasDerivAt (fun t => discreteBetheG Δ (kMap (lamOf Δ) α) (kMap (lamOf Δ) t))
      (Xi (2 * lamOf Δ) (α - β) - Xi (2 * lamOf Δ) (-α - β)) β := by
  let lam := lamOf Δ
  have hlam := lamOf_pos hΔ
  have hfun : (fun t => discreteBetheG Δ (kMap lam α) (kMap lam t)) =
      fun t => kMap (2 * lam) (-α - t) - kMap (2 * lam) (α - t) := by
    funext t
    unfold discreteBetheG
    rw [← kMap_neg lam α, theta_kMap_lamOf hΔ α t, theta_kMap_lamOf hΔ (-α) t]
    ring
  rw [hfun]
  have harg₁ : HasDerivAt (fun t : ℝ => -α - t) (-1) β := by
    change HasDerivAt ((fun _ : ℝ => -α) - id) (-1) β
    simpa using (hasDerivAt_const β (-α)).sub (hasDerivAt_id β)
  have harg₂ : HasDerivAt (fun t : ℝ => α - t) (-1) β := by
    change HasDerivAt ((fun _ : ℝ => α) - id) (-1) β
    simpa using (hasDerivAt_const β α).sub (hasDerivAt_id β)
  have h₁ := (hasDerivAt_kMap (by linarith : 0 < 2 * lam) (-α - β)).comp β harg₁
  have h₂ := (hasDerivAt_kMap (by linarith : 0 < 2 * lam) (α - β)).comp β harg₂
  convert (h₁.sub h₂) using 1
  · rfl
  linarith

/-- The endpoint difference of `G` has a one-arctangent closed form. -/
theorem discreteBetheG_endpoint_formula {x : ℝ} (hx : x ∈ Icc (-Real.pi) 0) :
    discreteBetheG Δ x 0 - discreteBetheG Δ x (-Real.pi) =
      4 * Real.arctan ((-Real.sin x) /
        (2 * (-Δ) * (Real.cos x - Δ))) := by
  let t := -Real.sin x
  let dm := Real.cos x - 1 - 2 * Δ
  let dp := Real.cos x + 1 - 2 * Δ
  have hsin := Real.sin_nonpos_of_nonpos_of_neg_pi_le hx.2 hx.1
  have ht : 0 ≤ t := by linarith
  have hdm : 0 < dm := by
    have hc := Real.neg_one_le_cos x
    linarith
  have hdp : 0 < dp := by
    linarith
  have hraw : discreteBetheG Δ x 0 - discreteBetheG Δ x (-Real.pi) =
      4 * (Real.arctan (Real.sin x / dp) - Real.arctan (Real.sin x / dm)) := by
    unfold discreteBetheG theta
    simp
    simp only [neg_div, Real.arctan_neg]
    grind
  have hraw' : discreteBetheG Δ x 0 - discreteBetheG Δ x (-Real.pi) =
      4 * (Real.arctan (t / dm) + Real.arctan (-t / dp)) := by
    rw [hraw, show Real.sin x = -t by linarith]
    simp only [neg_div, Real.arctan_neg]
    ring
  rw [hraw']
  have hprod : (t / dm) * (-t / dp) < 1 := by
    have hleft : 0 ≤ t / dm := by positivity
    have hright := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hdp.le
    nlinarith
  rw [Real.arctan_add hprod]
  have harg_eq : (t / dm + -t / dp) / (1 - (t / dm) * (-t / dp)) =
      t / (2 * (-Δ) * (Real.cos x - Δ)) := by
    have hΔne : Δ ≠ 0 := by linarith
    have hcos : 0 < Real.cos x - Δ := by
      have hc := Real.neg_one_le_cos x
      linarith
    have hden2 : dm * dp + t ^ 2 ≠ 0 := by positivity
    have hdenid : dm * dp + t ^ 2 = 4 * (-Δ) * (Real.cos x - Δ) := by
      nlinarith [Real.sin_sq_add_cos_sq x]
    field_simp
    grind
  grind
end

/-- The calculus bound in Lemma 2.5.  Its constant is valid as printed when
`Δ ≤ Δ₀ < -1`; the source line stating only `Δ₀ < 1` is insufficient. -/
theorem discreteBetheG_endpoint_bound {Δ Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1)
    (hΔ : Δ ≤ Δ₀) {x : ℝ} (hx : x ∈ Icc (-Real.pi) 0) :
    discreteBetheG Δ x 0 - discreteBetheG Δ x (-Real.pi) ≤
      4 * Real.arctan (1 / (2 * |Δ₀| * Real.sqrt (Δ₀ ^ 2 - 1))) ∧
    4 * Real.arctan (1 / (2 * |Δ₀| * Real.sqrt (Δ₀ ^ 2 - 1))) < 2 * Real.pi := by
  rw [discreteBetheG_endpoint_formula (by linarith) hx]
  let d := -Δ
  let d₀ := -Δ₀
  let c := Real.cos x
  let t := -Real.sin x
  have hd₀ : 1 < d₀ := by linarith
  have hc := Real.neg_one_le_cos x
  have hcd : 0 < c + d := by linarith
  have hs₀ : 0 < d₀ ^ 2 - 1 := by nlinarith
  have hs : 0 < d ^ 2 - 1 := by nlinarith
  let w₀ := Real.sqrt (d₀ ^ 2 - 1)
  let w := Real.sqrt (d ^ 2 - 1)
  have hw := Real.sqrt_pos.mpr hs
  have hwle : w₀ ≤ w := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have hsquare : (t * w) ^ 2 ≤ (c + d) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hs.le]
    nlinarith [sq_nonneg (Real.cos x * d + 1), Real.sin_sq_add_cos_sq x]
  have hroot : t * w ≤ c + d := by
    nlinarith
  have harg : t / (2 * d * (c + d)) ≤ 1 / (2 * d₀ * w₀) := by
    have hdpos : 0 < d := by linarith
    have hprod : d₀ * w₀ ≤ d * w :=
      mul_le_mul (by linarith) hwle (le_of_lt (by positivity)) (le_of_lt hdpos)
    calc
      t / (2 * d * (c + d)) = (1 / (2 * d)) * (t / (c + d)) := by field_simp
      _ ≤ (1 / (2 * d)) * (1 / w) := by
        apply mul_le_mul_of_nonneg_left ((div_le_div_iff₀ hcd hw).2 (by linarith))
        positivity
      _ = 1 / (2 * d * w) := by field_simp
      _ ≤ 1 / (2 * d₀ * w₀) := by
        apply one_div_le_one_div_of_le (by positivity)
        linarith
  have harg' : (-Real.sin x) / (2 * (-Δ) * (Real.cos x - Δ)) ≤
      1 / (2 * |Δ₀| * Real.sqrt (Δ₀ ^ 2 - 1)) := by
    grind
  constructor
  · simp_all
  · have := Real.arctan_lt_pi_div_two
      (1 / (2 * |Δ₀| * Real.sqrt (Δ₀ ^ 2 - 1)))
    linarith

/-- Abstract Levy--Desplanques criterion: strict row diagonal dominance makes a real
square matrix invertible. -/
theorem discrete_strict_row_diagonal_dominance_invertible {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (h : ∀ i, ∑ j ∈ Finset.univ.erase i, |A i j| < |A i i|) : A.det ≠ 0 := by
  apply det_ne_zero_of_sum_row_lt_diag
  omega

end PottsDiscontinuity.Bethe
