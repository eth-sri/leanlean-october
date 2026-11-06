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


open Set

namespace PottsDiscontinuity.Bethe

/-- The phase difference used to control the off-diagonal entries. -/
noncomputable def discreteBetheG (Δ x y : ℝ)  :=
  theta Δ x y - theta Δ (-x) y

/-- If the cosine argument is larger, the corresponding `Xi` kernel is larger. -/
theorem Xi_le_of_cos_le {μ a b : ℝ} (hμ : 0 < μ)
    (hcos : Real.cos b ≤ Real.cos a) : Xi μ b ≤ Xi μ a := by
  
  have hc  := Real.one_lt_cosh.mpr hμ.ne'
  
  
  
  
  exact (div_le_div_iff₀ (by
                            have := Real.cos_le_one b
                            linarith) (by
                                have := Real.cos_le_one a
                                linarith)).2 (mul_le_mul_of_nonneg_left (by linarith) (Real.sinh_pos_iff.mpr hμ).le)

/-- The derivative of `G(k(α),k(β))` in `β`, written as a difference of two `Xi` kernels. -/
theorem hasDerivAt_discreteBetheG_kMap {Δ : ℝ} (hΔ : Δ < -1)
    (α β : ℝ) :
    HasDerivAt (fun t => discreteBetheG Δ (kMap (lamOf Δ) α) (kMap (lamOf Δ) t))
      (Xi (2 * lamOf Δ) (α - β) - Xi (2 * lamOf Δ) (-α - β)) β := by
  let lam := lamOf Δ
  have hlam  := lamOf_pos hΔ
  have hfun : (fun t => discreteBetheG Δ (kMap lam α) (kMap lam t)) =
      fun t => kMap (2 * lam) (-α - t) - kMap (2 * lam) (α - t) := by
    funext t
    unfold discreteBetheG
    rw [← kMap_neg lam α]
    rw [theta_kMap_lamOf hΔ α t, theta_kMap_lamOf hΔ (-α) t]
    ring
  rw [hfun]
  
  
  
  
  
  convert  ((hasDerivAt_kMap (by linarith : 0 < 2 * lam) (-α - β)).comp β (by
                                                                                        change HasDerivAt ((fun _ : ℝ => -α) - id) (-1) β
                                                                                        simpa only [zero_sub] using (hasDerivAt_const β (-α)).sub (hasDerivAt_id β))).sub ((hasDerivAt_kMap (by linarith : 0 < 2 * lam) (α - β)).comp β (by
                                                                                              change HasDerivAt ((fun _ : ℝ => α) - id) (-1) β
                                                                                              simpa only [zero_sub] using (hasDerivAt_const β α).sub (hasDerivAt_id β)))  using 1
  · 
    rfl
  · 
    ring

/-- The endpoint difference of `G` has a one-arctangent closed form. -/
theorem discreteBetheG_endpoint_formula {Δ : ℝ} (hΔ : Δ < -1)
    {x : ℝ} (hx : x ∈ Icc (-Real.pi) 0) :
    discreteBetheG Δ x 0 - discreteBetheG Δ x (-Real.pi) =
      4 * Real.arctan ( -Real.sin x  /
        (2 *  -Δ  * (Real.cos x - Δ))) := by
  let t := -Real.sin x
  let dm := Real.cos x - 1 - 2 * Δ
  let dp := Real.cos x + 1 - 2 * Δ
  have hsin  := Real.sin_nonpos_of_nonpos_of_neg_pi_le hx.2 hx.1
  have ht : 0 ≤ t := by  linarith
  have hdm : 0 < dm := by
    
    have hc := Real.neg_one_le_cos x
    linarith
  have hdp : 0 < dp := by
    linarith
  have hraw : discreteBetheG Δ x 0 - discreteBetheG Δ x (-Real.pi) =
      4 * (Real.arctan (Real.sin x / dp) - Real.arctan (Real.sin x / dm)) := by
    unfold discreteBetheG theta
    simp only [Real.sin_zero, Real.cos_zero, Real.sin_neg, Real.cos_neg,
      Real.sin_pi, Real.cos_pi]
    simp only [sub_zero, neg_zero, neg_div, Real.arctan_neg]
    dsimp [dp, dm]
    ring_nf
  have hraw' : discreteBetheG Δ x 0 - discreteBetheG Δ x (-Real.pi) =
      4 * (Real.arctan (t / dm) + Real.arctan (-t / dp)) := by
    rw [hraw, show Real.sin x = -t by  ring]
    simp only [neg_div, Real.arctan_neg]
    ring
  rw [hraw']
  
  rw [Real.arctan_add (by
                         
                         
                         have hmul  := mul_nonpos_of_nonneg_of_nonpos (div_nonneg ht hdm.le) (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hdp.le)
                         linarith)]
  
  exact congrArg (fun u  => 4 * Real.arctan u) (by
                                                     
                                                     
                                                     have hΔne : Δ ≠ 0 := by
                                                                            nlinarith
                                                     have hcos : 0 < Real.cos x - Δ := by
                                                       have hc := Real.neg_one_le_cos x
                                                       linarith
                                                     
                                                     have hden2 : dm * dp + t ^ 2 ≠ 0 := by positivity
                                                     have hdenid : dm * dp + t ^ 2 = 4 *  -Δ  * (Real.cos x - Δ) := by
                                                       
                                                       nlinarith [Real.sin_sq_add_cos_sq x]
                                                     field_simp [ ne_of_gt hdm ,  ne_of_gt hdp , (by
                                                                                                    nlinarith : 2 *  -Δ  * (Real.cos x - Δ) ≠ 0), hden2]
                                                     grind)

/-- The calculus bound in Lemma 2.5.  Its constant is valid as printed when
`Δ ≤ Δ₀ < -1`; the source line stating only `Δ₀ < 1` is insufficient. -/
theorem discreteBetheG_endpoint_bound {Δ Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1)
    (hΔ : Δ ≤ Δ₀) {x : ℝ} (hx : x ∈ Icc (-Real.pi) 0) :
    discreteBetheG Δ x 0 - discreteBetheG Δ x (-Real.pi) ≤
      4 * Real.arctan (1 / (2 * |Δ₀| * Real.sqrt (Δ₀ ^ 2 - 1))) ∧
    4 * Real.arctan (1 / (2 * |Δ₀| * Real.sqrt (Δ₀ ^ 2 - 1))) < 2 * Real.pi := by
  
  rw [discreteBetheG_endpoint_formula (lt_of_le_of_lt hΔ hΔ₀) hx]
  let d := -Δ
  let d₀ := -Δ₀
  let c := Real.cos x
  let t := -Real.sin x
  have hd₀ : 1 < d₀ := by  linarith
  have hd : d₀ ≤ d := by  linarith
  have hc : -1 ≤ c := Real.neg_one_le_cos x
  
  
  
  have hs₀ : 0 < d₀ ^ 2 - 1 := by nlinarith
  have hs : 0 < d ^ 2 - 1 := by nlinarith
  let w₀ := Real.sqrt (d₀ ^ 2 - 1)
  let w := Real.sqrt (d ^ 2 - 1)
  have hw₀  := Real.sqrt_pos.mpr hs₀
  
  
  have htrig := Real.sin_sq_add_cos_sq x
  have hsquare : (t * w) ^ 2 ≤ (c + d) ^ 2 := by
    
    rw [mul_pow, Real.sq_sqrt hs.le]
    nlinarith [sq_nonneg (Real.cos x * d + 1), Real.sin_sq_add_cos_sq x]
  have hroot : t * w ≤ c + d := by
    
    nlinarith
  have harg : t / (2 * d * (c + d)) ≤ 1 / (2 * d₀ * w₀) := by
    
    have hdpos  := lt_of_lt_of_le (by linarith : 0 < d₀) hd
    have hprod : d₀ * w₀ ≤ d * w := by
                                      bound
    
    
    calc
      t / (2 * d * (c + d)) =  1 / (2 * d)  * (t / (c + d)) := by field_simp
      _ ≤  1 / (2 * d)  * (1 / w) := by
        apply mul_le_mul_of_nonneg_left ((div_le_div_iff₀ (by linarith) (Real.sqrt_pos.mpr hs)).2 (by nlinarith ))
        positivity
      _ = 1 / (2 * d * w) := by field_simp
      _ ≤ 1 / (2 * d₀ * w₀) := by
        apply one_div_le_one_div_of_le (by positivity)
        grind
  have harg' :  -Real.sin x  / (2 *  -Δ  * (Real.cos x - Δ)) ≤
      1 / (2 * |Δ₀| * Real.sqrt (Δ₀ ^ 2 - 1)) := by
    grind
  constructor
  · simp_all
  · have := Real.arctan_lt_pi_div_two
      (1 / (2 * |Δ₀| * Real.sqrt (Δ₀ ^ 2 - 1)))
    nlinarith [Real.pi_pos]

/-- Abstract Levy--Desplanques criterion: strict row diagonal dominance makes a real
square matrix invertible. -/
theorem discrete_strict_row_diagonal_dominance_invertible {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (h : ∀ i, ∑ j ∈ Finset.univ.erase i, |A i j| < |A i i|) : A.det ≠ 0 := by
  apply det_ne_zero_of_sum_row_lt_diag
  simp_all

end PottsDiscontinuity.Bethe
