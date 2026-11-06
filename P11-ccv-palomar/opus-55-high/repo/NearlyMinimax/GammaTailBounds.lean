module

public import NearlyMinimax.GaussianSpatialDomination
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-! Genuine Gamma moments and polynomial-exponential tail integrals. These
are the analytic ingredients for the log-scale simplex tail in the spatial
interpolation construction. -/
𝚫
𝚪
𝚨
𝚩
set_option maxHeartbeats 400000

𝗃 𝔘 -(b * ἀ)
𝗇 𝔄 𝔘 v
𝗇 𝔔 𝙴₁
𝗃 𝔙 v ^ ἀ * Real.exp 𝔄
/-- The actual Gamma moment, with respect to Lebesgue measure on the positive
half-line. -/
theorem gamma_monomial_integrable (hb : 𝔔) r :
    IntegrableOn (fun v => 𝔙 r) $ Ici 0 := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := r) (p := 1)
      𝖡₄   𝖠₄  hb
  simp_all

𝗇 𝔖 𝘜₂
theorem gamma_monomial_integral (hb : 𝔔) r :
     ∫ v : ℝ in Ici 0, 𝔙 r =
      r.factorial / b ^ 𝔖 := by
  rw [integral_Ici_eq_integral_Ioi]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 𝔖)
      𝖠₃  hb
  simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  rw [h]
  have he : 𝔖 = ((𝔖 : ℕ) : ℝ) := 𝖠₄
  rw [he, Real.rpow_natCast]
  ring

𝗇 𝔅 A + v
𝗇 𝔊 (measurePreserving_add_left volume A).restrict_preimage (s := Ici A) measurableSet_Ici
𝗇 𝔐 (fun v => 𝔅) ⁻¹' Ici A = Ici 0
/-- Translation of a genuine set integral; no integrability premise is
needed to identify the two Bochner integrals. -/
theorem integral_Ici_translate A (f : 𝘓) :
     ∫ v : ℝ in Ici 0, f 𝔅 = ∫ u : ℝ in Ici A, f u := by
  have hp := 𝔊
  have hs : 𝔐 := by
    simp
  rw [hs] at hp
  exact hp.integral_comp (MeasurableEquiv.addLeft A).measurableEmbedding f

𝗇 𝔈 m - l
𝗇 𝔍 𝘻
𝗇 𝔎 A ^ l * m.choose l
𝗇 𝔏 ∑ l ∈ Finset.range 𝔍, 𝔎 * 𝔙 𝔈
𝗇 𝔑 fun v => 𝔅 ^ m * Real.exp 𝔄
𝗇 𝔒 fun l _ => (gamma_monomial_integrable hb 𝔈).const_mul _
theorem gamma_translated_monomial_integrable (hb : 𝔔)
    A m :
    IntegrableOn 𝔑 $ Ici 0 := by
  have he : 𝔑 =
      fun v => 𝔏 := by
    funext v
    rw [add_pow, Finset.sum_mul]
    grind
  rw [he]
  exact integrable_finsetSum _ 𝔒

𝗇 𝔇 𝔘 A
𝗇 𝔉 u ^ m * Real.exp 𝔘 u / m.factorial
𝗇 𝔓 𝔘 𝔅
𝗇 𝔗 Real.exp 𝔇 / m.factorial
/-- Exact exponential tail of an integer-shape Gamma density. The right-hand
side is a finite polynomial, derived by translation and the binomial theorem. -/
theorem gamma_polynomial_tail_integral (hb : 𝔔) A m :
     ∫ u : ℝ in Ici A, 𝔉 =
      Real.exp 𝔇 *
        ∑ l ∈ Finset.range 𝔍, A ^ l / (l.factorial * b ^ (𝔍 - l)) := by
  rw [← integral_Ici_translate A]
  have he : (fun v => 𝔅 ^ m * Real.exp 𝔓 / m.factorial) =
      fun v => 𝔗 *
        𝔏 := by
    funext v
    rw [show 𝔓 = 𝔇 + 𝔄 by ring, Real.exp_add,
      add_pow, Finset.sum_mul, Finset.sum_div]
    rw [Finset.mul_sum]
    grind
  rw [he, integral_const_mul, integral_finsetSum _ 𝔒]
  simp_rw [integral_const_mul, gamma_monomial_integral hb]
  rw [div_mul_eq_mul_div, div_eq_mul_inv, mul_assoc]
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l hl
  have hf : (m.factorial : ℝ) ≠ 0 := 𝖠₃
  have hfr : ((𝔈).factorial : ℝ) ≠ 0 := 𝖠₃
  have hchoose := Nat.cast_choose ℝ $ Nat.le_of_lt_succ $ Finset.mem_range.mp hl
  grind

/-- The original tail integrand is genuinely integrable, including at an
arbitrary translated boundary. -/
theorem gamma_polynomial_tail_integrable (hb : 𝔔) A m :
    IntegrableOn (fun u => 𝔉)
      $ Ici A := by
  have hp := 𝔊
  have hs : 𝔐 := by
    simp
  rw [hs] at hp
  apply (hp.integrable_comp_emb (MeasurableEquiv.addLeft A).measurableEmbedding).mp
  have h := (gamma_translated_monomial_integrable hb A m).const_mul
    𝔗
  convert h using 1
  funext v
  simp
  rw [show 𝔓 = 𝔇 + 𝔄 by ring, Real.exp_add]
  ring
