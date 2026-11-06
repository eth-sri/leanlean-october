module

public import NearlyMinimax.HighSmoothnessWindows
public import NearlyMinimax.HighFieldRegularity
public import RoughRegime.ComplexDerivativeBridge
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Degree-independent bounds for the manuscript's polynomial chart frame.
The factor 1/8 provides a fixed complex neighborhood at every real chart point. -/
open Set
open scoped BigOperators ContDiff
𝚨
open RoughRegime.ComplexDerivativeBridge
𝚩
𝚭

𝗇 𝔄 𝙣
def frameCoefficientL1 (P : 𝔄) : ℝ :=
  ∑ β ∈ P.support, |P.coeff β|

theorem frameCoefficientL1_nonneg (P : 𝔄) :
    0 ≤ frameCoefficientL1 P := Finset.sum_nonneg 𝖢

def frameScaledPolynomial (P : 𝔄) : 𝔄 :=
  MvPolynomial.bind₁ (fun r => MvPolynomial.C (1 / 8 : ℝ) * MvPolynomial.X r) P

𝗃 𝔑 MvPolynomial.eval ἀ $ frameScaledPolynomial P
theorem frameScaledPolynomial_eval P (x : Covariate d) :
    𝔑 x = MvPolynomial.eval (fun r => x r / 8) P := by
  change 𝚘 x _ = 𝚘 _ P
  rw [frameScaledPolynomial, MvPolynomial.eval₂Hom_bind₁]
  simp
  ring

𝗇 𝔊 fun r => z r / 8
𝗇 𝔎 MvPolynomial.eval z $ complexify $ frameScaledPolynomial P
theorem frameScaledPolynomial_complex_eval P
    (z : Fin d → ℂ) : 𝔎 =
      MvPolynomial.eval₂ Complex.ofRealHom 𝔊 P := by
  rw [complexify, MvPolynomial.eval_map]
  change MvPolynomial.eval₂Hom Complex.ofRealHom z _ =
    MvPolynomial.eval₂Hom Complex.ofRealHom _ P
  rw [frameScaledPolynomial, MvPolynomial.eval₂Hom_bind₁]
  have he : (fun r => 1 / 8 * z r) = 𝔊 := by
    funext r
    ring
  simp_all

theorem frame_complex_eval_norm_le_l1 P
    (z : Fin d → ℂ) (hz : ∀ r, ‖z r‖ ≤ 1) :
    ‖MvPolynomial.eval₂ Complex.ofRealHom z P‖ ≤ frameCoefficientL1 P := by
  apply (norm_sum_le ..).trans
  apply Finset.sum_le_sum
  intro β hβ
  have hp : ‖∏ r, z r ^ β r‖ ≤ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_one₀
    · simp
    · intro r hr
      rw [norm_pow]
      bound
  simp_all

𝗇 𝔇 𝘌₂ ≤ 1
𝗇 𝔍 fun r => (u r : ℂ)
theorem frameScaledPolynomial_complex_bound P
    (u : Covariate d) (hu : 𝔇) z
    (hz : ‖z - 𝔍‖ < 1) :
    ‖𝔎‖ ≤ frameCoefficientL1 P := by
  rw [frameScaledPolynomial_complex_eval]
  apply frame_complex_eval_norm_le_l1
  intro r
  have hcoord : ‖z r - (u r)‖ < 1 := (norm_le_pi_norm
    (z - 𝔍) r).trans_lt hz
  have hucoord : ‖(u r : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real] using (norm_le_pi_norm u r).trans hu
  have hzcoord : ‖z r‖ ≤ 2 := by
    have htri := norm_sub_norm_le (z r) $ u r
    linarith
  norm_num
  linarith

𝗇 𝔅 fun x => 𝔑 x
𝗇 𝔐 ‖iteratedFDeriv ℝ q 𝔅 u‖
𝗃 𝔒 ἀ P u hu
theorem frameScaledPolynomial_derivative_bound P
    (u : Covariate d) (hu : 𝔇) q (hq : 0 < q) :
    𝔐 ≤
      frameCoefficientL1 P * q.factorial * Real.exp 1 ^ q := by
  simpa only [div_one] using real_polynomial_derivative_norm_bound
    (frameScaledPolynomial P) u 1 (frameCoefficientL1 P)  𝖠₄ 
    (frameCoefficientL1_nonneg P) 𝔒 frameScaledPolynomial_complex_bound hq

theorem frameScaledPolynomial_contDiff (P : 𝔄) :
    ContDiff ℝ ∞ 𝔅 :=
  (RoughRegime.PolynomialDerivatives.polynomial_contDiff _).of_le le_top

theorem frameScaledPolynomial_value_bound P
    (u : Covariate d) (hu : 𝔇) :
    |𝔑 u| ≤ frameCoefficientL1 P := by
  have hc := 𝔒 frameScaledPolynomial_complex_bound (fun r => u r ) 𝖢₄
  rw [complexify, MvPolynomial.eval_map] at hc
  change ‖MvPolynomial.eval₂ Complex.ofRealHom (Complex.ofRealHom ∘ u)
    (frameScaledPolynomial P)‖ ≤ frameCoefficientL1 P at hc
  rw [← MvPolynomial.eval₂_comp] at hc
  simp_all

𝗇 𝔈 Real.exp 1 ^ m
/-- A bound for every derivative through a fixed order, independent of the
polynomial degree and the number of frame coefficients. -/
theorem frameScaledPolynomial_derivatives_bound P
    m q (hq : q ≤ m) (u : Covariate d) (hu : 𝔇) :
    𝔐 ≤
      frameCoefficientL1 P * m.factorial * 𝔈 := by
  have hL1 := frameCoefficientL1_nonneg P
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr 𝖠₄
  by_cases hq0 : q = 0
  · subst q
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    apply (𝔒 frameScaledPolynomial_value_bound).trans
    have hmfac : 𝙠 ≤ m.factorial := by exact_mod_cast Nat.factorial_pos m
    have hmexp : 1 ≤ 𝔈 := one_le_pow₀ he
    have hh : 1 ≤ m.factorial * 𝔈 := 𝖥₃
    nlinarith
  · apply (𝔒 frameScaledPolynomial_derivative_bound q $ Nat.pos_of_ne_zero hq0 ).trans
    gcongr

def highFrameProfile (P : 𝔄) (u : Covariate d) : ℝ :=
  highWindowTensor d u * 𝔑 u

theorem highFrameProfile_contDiff (P : 𝔄) :
    ContDiff ℝ ∞ $ highFrameProfile P :=
  (highWindowTensor_contDiff d).mul $ frameScaledPolynomial_contDiff P

theorem highFrameProfile_tsupport_subset P :
    tsupport (highFrameProfile P) ⊆ tsupport (highWindowTensor d) :=
  tsupport_mul_subset_left


𝗇 𝔉 frameCoefficientL1 P * Cp
𝗇 𝔏 iteratedFDeriv ℝ q (highFrameProfile P) u
/-- Fixed-order compact frame derivative bounds are uniform over all
polynomial degrees; only the coefficient ℓ¹ norm occurs. -/
theorem highFrameProfile_derivative_bound d m :
    ∃ K , 0 < K ∧ ∀ P , ∀ q ≤ m, ∀ u : Covariate d,
      ‖𝔏‖ ≤ K * frameCoefficientL1 P := by
  obtain ⟨B, hB0, hB⟩ := highWindowTensor_derivative_bound d m
  let B' := max B 1
  let Cp := m.factorial * 𝔈
  let K := 2 ^ m * B' * Cp
  have hK : 0 < K := 𝖠₃
  refine ⟨K, hK, ?_⟩
  intro P q hq u
  have hL1 := frameCoefficientL1_nonneg P
  by_cases hu : u ∈ tsupport (highWindowTensor d)
  · have hunorm : 𝔇 := by
      apply (pi_norm_le_iff_of_nonneg 𝖠₄ ).mpr
      intro r
      exact (highWindowTensor_tsupport_bound hu r).trans 𝖠₄
    have hder := norm_iteratedFDeriv_mul_le (highWindowTensor_contDiff d)
      (frameScaledPolynomial_contDiff P) u (n := q) 𝖢₄
    calc
      𝖦 := hder
      _ ≤ ∑ j ∈ Finset.range $ q + 1 , q.choose j * B' *
          𝔉 := by
        apply Finset.sum_le_sum
        intro j hj
        have hjq : j ≤ q := by simpa using Finset.mem_range.mp hj
        have hjm := hjq.trans hq
        gcongr
        · exact (hB j hjm u).trans $ le_max_left ..
        · simpa only [Cp, mul_assoc] using
            frameScaledPolynomial_derivatives_bound P m (q - j) ((Nat.sub_le ..).trans hq) u hunorm
      _ = 2 ^ q * B' * 𝔉 := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
      _ ≤ 2 ^ m * B' * 𝔉 := by
        gcongr
        norm_num
      _ = K * frameCoefficientL1 P := 𝖢₃
  · have hzero : 𝔏 = 0 := by
      by_contra hn
      exact hu $ highFrameProfile_tsupport_subset P
        $ (support_iteratedFDeriv_subset q) hn
    rw [hzero, norm_zero]
    exact mul_nonneg hK.le hL1
