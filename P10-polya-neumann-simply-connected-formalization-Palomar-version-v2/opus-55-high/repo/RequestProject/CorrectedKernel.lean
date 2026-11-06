module

public import RequestProject.KernelRows
public import Mathlib.Data.Real.Sign

/-!
# The corrected Volterra kernel (Lemma 6.6, Lipschitz part)

For a transport `W` of a Lipschitz curve with `c_E = (V_E^* - I) e₀ ≠ 0`, the kernel of
`i(T_E - T_E^*) + O_E B_E O_E^* - 2D^{-1}` is (equation (6.3) of the paper)

  `r_E(θ, t) = i sgn(θ - t) (w_E(θ, t) - 1) + i (θ - t)/π + ⟨e₀, W(θ) B_E W(t)^* e₀⟩`,

with `w_E(θ, t) = ⟨e₀, W(θ) W(t)^* e₀⟩` (`correctedKernel`). We prove:

* `norm_correctedKernel_sub_le`: `θ ↦ r_E(θ, t)` is Lipschitz on `[0, L]`, uniformly in `t`
  (the jump of `sgn` is compensated by `w_E(t, t) = 1`);
* `correctedKernel_endpoint`: the opposite edges agree, `r_E(L, t) = r_E(0, t)` (Lemma 6.4 and
  periodicity of `2D^{-1}`);
* `summable_sq_mul_correctedKernelCoeff`: consequently the double Fourier coefficients
  `r_{n m}` of `r_E` on `[0, L]²` satisfy `∑_{n,m} m² |r_{n m}|² < ∞`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real MeasureTheory
open scoped InnerProductSpace ComplexConjugate

lemma measurable_real_sign : Measurable Real.sign := Measurable.ite measurableSet_Iio measurable_const
    (Measurable.ite measurableSet_Ioi measurable_const measurable_const)

lemma abs_real_sign_le (t : ℝ) : |Real.sign t| ≤ 1 := by
  rcases Real.sign_apply_eq t with h | h | h <;> simp [h]

/-- A function vanishing at `t` and `L`-Lipschitz, multiplied by `sgn(· - t)`, stays
`L`-Lipschitz. -/
lemma norm_sign_mul_sub_le {g : ℝ → ℂ} {L t θ θ' : ℝ}
    (hg : ‖g θ - g θ'‖ ≤ L * |θ - θ'|) (hgθ : ‖g θ‖ ≤ L * |θ - t|)
    (hgθ' : ‖g θ'‖ ≤ L * |θ' - t|) :
    ‖Real.sign (θ - t) * g θ - Real.sign (θ' - t) * g θ'‖ ≤ L * |θ - θ'| := by
  have hcross : ∀ a b : ℂ, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → (θ - t) * (θ' - t) ≤ 0 →
      ‖a * g θ - b * g θ'‖ ≤ L * |θ - θ'| := by
    intro a b ha hb hprod
    have habs : |θ - θ'| = |θ - t| + |θ' - t| := by
      have e : θ - θ' = (θ - t) - (θ' - t) := by ring
      rw [e]
      rcases le_total 0 (θ - t) with h1 | h1 <;> rcases le_total 0 (θ' - t) with h2 | h2
      · rcases mul_eq_zero.mp (le_antisymm hprod (mul_nonneg h1 h2)) with h | h <;> rw [h] <;> simp [abs_sub_comm]
      · grind
      · grind
      · rcases mul_eq_zero.mp (le_antisymm hprod (mul_nonneg_of_nonpos_of_nonpos h1 h2)) with h | h <;> rw [h] <;> simp [abs_sub_comm]
    calc ‖a * g θ - b * g θ'‖ ≤ ‖a * g θ‖ + ‖b * g θ'‖ := norm_sub_le _ _
      _ ≤ 1 * ‖g θ‖ + 1 * ‖g θ'‖ := by
          rw [norm_mul, norm_mul]
          gcongr
      _ ≤ L * |θ - t| + L * |θ' - t| := by linarith
      _ = L * |θ - θ'| := by grind
  have hs : ∀ x : ℝ, ‖(Real.sign x : ℂ)‖ ≤ 1 := fun x => by
    rw [Complex.norm_real]; exact abs_real_sign_le x
  rcases lt_trichotomy θ t with h1 | h1 | h1 <;> rcases lt_trichotomy θ' t with h2 | h2 | h2
  · rw [Real.sign_of_neg (by linarith), Real.sign_of_neg (by linarith)]
    simp 
    rw [show -g θ + g θ' = -(g θ - g θ') by ring, norm_neg]; assumption
  all_goals first
    | exact hcross _ _ (hs _) (hs _) (by nlinarith)
    | (rw [Real.sign_of_pos (by linarith), Real.sign_of_pos (by linarith)]
       simp_all)

variable (W : ℝ → Ell2 →L[ℂ] Ell2)

/-- The correction operator `B_E` built from `c_E = (V_E^* - I) e₀` and `d_E = i s_E`. -/
def cutBE : Ell2 →L[ℂ] Ell2 :=
  cutB (cutC (W (2 * π)) (basisVec 0)) (Complex.I • cutS (W (2 * π)) (basisVec 0))

/-- The corrected Volterra kernel `r_E(θ, t)` of equation (6.3). -/
def correctedKernel (θ t : ℝ) : ℂ :=
  Complex.I * Real.sign (θ - t) * (volterraKernel W θ t - 1) + Complex.I * ((θ - t) / π) +
    ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W t) (basisVec 0)))⟫_ℂ

variable {W} {γ : ℝ → ℂ} {K : NNReal} {E : ℝ}

lemma norm_basisVec_zero : ‖basisVec 0‖ = 1 := by simp [basisVec]

lemma norm_adjoint_transport_e0_le (hK : LipschitzWith K γ) (hW : IsTransport γ E W) {t : ℝ}
    (ht : t ∈ Set.Icc 0 (2 * π)) : ‖ContinuousLinearMap.adjoint (W t) (basisVec 0)‖ ≤ 1 := by
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  rw [LinearIsometryEquiv.norm_map, norm_basisVec_zero, mul_one]
  exact norm_transport_le_one hK hW ht

lemma volterraKernel_self (hK : LipschitzWith K γ) (hW : IsTransport γ E W) {t : ℝ}
    (ht : t ∈ Set.Icc 0 (2 * π)) : volterraKernel W t t = 1 := by
  unfold volterraKernel
  simp [← ContinuousLinearMap.mul_apply, transport_mul_adjoint hK hW ht, norm_basisVec_zero]

lemma norm_inner_transport_sub_le (hK : LipschitzWith K γ) (hW : IsTransport γ E W) {θ θ' : ℝ}
    (hθ : θ ∈ Set.Icc 0 (2 * π)) (hθ' : θ' ∈ Set.Icc 0 (2 * π)) (y : Ell2) :
    ‖⟪basisVec 0, W θ y⟫_ℂ - ⟪basisVec 0, W θ' y⟫_ℂ‖ ≤
      Real.sqrt E * shiftConst * K * |θ - θ'| * ‖y‖ := by
  rw [← inner_sub_right, ← ContinuousLinearMap.sub_apply]
  refine (norm_inner_le_norm _ _).trans ?_
  rw [norm_basisVec_zero, one_mul]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  gcongr
  exact norm_transport_sub_le_lip hK hW hθ hθ'

/-- Uniform Lipschitz bound for the rows of the corrected kernel. -/
theorem norm_correctedKernel_sub_le (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    {θ θ' t : ℝ} (hθ : θ ∈ Set.Icc 0 (2 * π)) (hθ' : θ' ∈ Set.Icc 0 (2 * π))
    (ht : t ∈ Set.Icc 0 (2 * π)) :
    ‖correctedKernel W θ t - correctedKernel W θ' t‖ ≤
      (Real.sqrt E * shiftConst * K * (2 + ‖cutBE W‖) + 1 / π) * |θ - θ'| := by
  set L := Real.sqrt E * shiftConst * K with hLdef
  have hL : 0 ≤ L := by have := shiftConst_nonneg; positivity
  set x := ContinuousLinearMap.adjoint (W t) (basisVec 0)
  have hx  := norm_adjoint_transport_e0_le hK hW ht
  set g : ℝ → ℂ := fun u => volterraKernel W u t - 1
  have hg : ∀ u ∈ Set.Icc 0 (2 * π), ∀ u' ∈ Set.Icc 0 (2 * π),
      ‖g u - g u'‖ ≤ L * |u - u'| := by
    intro u hu u' hu'
    simp only [g, sub_sub_sub_cancel_right]
    have := norm_inner_transport_sub_le hK hW hu hu' x
    calc _ ≤ L * |u - u'| * ‖x‖ := this
      _ ≤ L * |u - u'| * 1 := by gcongr
      _ = _ := mul_one _
  have hgt : g t = 0 := by simp [g, volterraKernel_self hK hW ht]
  have hg0  := fun u hu => by
    simpa [hgt] using hg u hu t ht
  have h1  :=
    norm_sign_mul_sub_le (hg θ hθ θ' hθ') (hg0 θ hθ) (hg0 θ' hθ')
  have h2 : ‖⟪basisVec 0, W θ (cutBE W x)⟫_ℂ - ⟪basisVec 0, W θ' (cutBE W x)⟫_ℂ‖ ≤
      L * |θ - θ'| * ‖cutBE W‖ := by
    refine (norm_inner_transport_sub_le hK hW hθ hθ' _).trans ?_
    gcongr
    calc ‖cutBE W x‖ ≤ ‖cutBE W‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖cutBE W‖ * 1 := by gcongr
      _ = _ := mul_one _
  have h3 : ‖Complex.I * ((θ - t) / π : ℝ) - Complex.I * ((θ' - t) / π : ℝ)‖ ≤
      1 / π * |θ - θ'| := by
    rw [← mul_sub, norm_mul, Complex.norm_I, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    rw [show (θ - t) / π - (θ' - t) / π = (θ - θ') / π by ring, abs_div,
      abs_of_pos pi_pos]
    ring_nf; rfl
  have e : correctedKernel W θ t - correctedKernel W θ' t =
      Complex.I * (Real.sign (θ - t) * g θ - Real.sign (θ' - t) * g θ') +
      (Complex.I * ((θ - t) / π : ℝ) - Complex.I * ((θ' - t) / π : ℝ)) +
      (⟪basisVec 0, W θ (cutBE W x)⟫_ℂ - ⟪basisVec 0, W θ' (cutBE W x)⟫_ℂ) := by
    simp only [correctedKernel]
    push_cast
    ring
  rw [e]
  calc _ ≤ ‖Complex.I * (Real.sign (θ - t) * g θ - Real.sign (θ' - t) * g θ')‖ +
        ‖Complex.I * ((θ - t) / π : ℝ) - Complex.I * ((θ' - t) / π : ℝ)‖ +
        ‖⟪basisVec 0, W θ (cutBE W x)⟫_ℂ - ⟪basisVec 0, W θ' (cutBE W x)⟫_ℂ‖ :=
        norm_add₃_le
    _ ≤ L * |θ - θ'| + 1 / π * |θ - θ'| + L * |θ - θ'| * ‖cutBE W‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]
        gcongr
    _ ≤ (L * (2 + ‖cutBE W‖) + 1 / π) * |θ - θ'| := by
        have : 0 ≤ L * |θ - θ'| := by positivity
        nlinarith

/-- **Opposite edges agree** (Lemma 6.6): `r_E(L, t) = r_E(0, t)` for `t ∈ [0, L]`. -/
theorem correctedKernel_endpoint (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0) {t : ℝ} (ht : t ∈ Set.Icc 0 (2 * π)) :
    correctedKernel W (2 * π) t = correctedKernel W 0 t := by
  have h0 : W 0 = 1 := by
    have := hW.2 0 ⟨le_rfl, by positivity⟩
    simp_all
  set V := W (2 * π)
  set x := ContinuousLinearMap.adjoint (W t) (basisVec 0)
  -- the two sign terms
  have hs1 : Real.sign (2 * π - t) * (volterraKernel W (2 * π) t - 1) =
      volterraKernel W (2 * π) t - 1 := by
    rcases eq_or_lt_of_le ht.2 with h | h
    · simp [h, volterraKernel_self hK hW ⟨by positivity, le_rfl⟩]
    · rw [Real.sign_of_pos (by linarith)]; simp
  have hs2 : Real.sign (0 - t) * (volterraKernel W 0 t - 1) =
      -(volterraKernel W 0 t - 1) := by
    rcases eq_or_lt_of_le ht.1 with h | h
    · simp [← h, volterraKernel_self hK hW ⟨le_rfl, by positivity⟩]
    · rw [Real.sign_of_neg (by linarith)]; simp
  have hw0 : volterraKernel W 0 t = ⟪basisVec 0, x⟫_ℂ := by
    simp [volterraKernel, h0, x]
  have hwL : volterraKernel W (2 * π) t = ⟪basisVec 0, V x⟫_ℂ := rfl
  have hBterm : ⟪basisVec 0, V (cutBE W x)⟫_ℂ - ⟪basisVec 0, W 0 (cutBE W x)⟫_ℂ =
      ⟪cutC V (basisVec 0), cutBE W x⟫_ℂ := by
    simp [h0, ← ContinuousLinearMap.adjoint_inner_left, cutC, inner_sub_left]
  have hS : ⟪cutS V (basisVec 0), x⟫_ℂ = ⟪basisVec 0, x⟫_ℂ + ⟪basisVec 0, V x⟫_ℂ := by
    simp [cutS, inner_add_left, ContinuousLinearMap.adjoint_inner_left]
  exact sub_eq_zero.mp (by
    have e : correctedKernel W (2 * π) t - correctedKernel W 0 t =
        Complex.I * (Real.sign (2 * π - t) * (volterraKernel W (2 * π) t - 1)) -
        Complex.I * (Real.sign (0 - t) * (volterraKernel W 0 t - 1)) +
        Complex.I * 2 +
        (⟪basisVec 0, V (cutBE W x)⟫_ℂ - ⟪basisVec 0, W 0 (cutBE W x)⟫_ℂ) := by
      simp only [correctedKernel]
      push_cast
      field_simp
      ring
    rw [e, hs1, hs2, hBterm]
    unfold cutBE
    rw [inner_cutC_cutB (transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩) (basisVec 0) hc x, hS, hw0, hwL]
    ring)

/-- Boundedness of the corrected kernel on the square. -/
lemma norm_correctedKernel_le (hK : LipschitzWith K γ) (hW : IsTransport γ E W) {θ t : ℝ}
    (hθ : θ ∈ Set.Icc 0 (2 * π)) (ht : t ∈ Set.Icc 0 (2 * π)) :
    ‖correctedKernel W θ t‖ ≤ 4 + ‖cutBE W‖ := by
  set x := ContinuousLinearMap.adjoint (W t) (basisVec 0)
  have hx  := norm_adjoint_transport_e0_le hK hW ht
  have hWθ  := norm_transport_le_one hK hW hθ
  have hw : ‖volterraKernel W θ t‖ ≤ 1 := by
    refine (norm_inner_le_norm _ _).trans ?_
    rw [norm_basisVec_zero, one_mul]
    calc ‖W θ x‖ ≤ ‖W θ‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1
  have h1 : ‖Complex.I * Real.sign (θ - t) * (volterraKernel W θ t - 1)‖ ≤ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
    calc |Real.sign (θ - t)| * ‖volterraKernel W θ t - 1‖ ≤ 1 * (1 + 1) := by
          gcongr
          · exact abs_real_sign_le _
          · exact (norm_sub_le _ _).trans (by simp_all)
      _ = 2 := by norm_num
  have h2 : ‖Complex.I * ((θ - t) / π : ℝ)‖ ≤ 2 := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos pi_pos, div_le_iff₀ pi_pos]
    grind
  have h3 : ‖⟪basisVec 0, W θ (cutBE W x)⟫_ℂ‖ ≤ ‖cutBE W‖ := by
    refine (norm_inner_le_norm _ _).trans ?_
    rw [norm_basisVec_zero, one_mul]
    calc ‖W θ (cutBE W x)‖ ≤ ‖W θ‖ * (‖cutBE W‖ * ‖x‖) :=
          (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact ContinuousLinearMap.le_opNorm _ _)
      _ ≤ 1 * (‖cutBE W‖ * 1) := by gcongr
      _ = ‖cutBE W‖ := by ring
  have e : correctedKernel W θ t = Complex.I * Real.sign (θ - t) * (volterraKernel W θ t - 1) +
      Complex.I * ((θ - t) / π : ℝ) + ⟪basisVec 0, W θ (cutBE W x)⟫_ℂ := by
    simp [correctedKernel, x]
  rw [e]
  refine (norm_add₃_le).trans ?_
  linarith

end PolyaNeumann

namespace PolyaNeumann

open Real MeasureTheory
open scoped InnerProductSpace ComplexConjugate

variable {W : ℝ → Ell2 →L[ℂ] Ell2} {γ : ℝ → ℂ} {K : NNReal} {E : ℝ}

/-- The clamp of `t` to `[0, 2π]`. -/
def clampTwoPi (t : ℝ) : ℝ := (Set.projIcc 0 (2 * π) two_pi_pos.le t : ℝ)

lemma continuous_clampTwoPi : Continuous clampTwoPi :=
  continuous_subtype_val.comp continuous_projIcc

lemma clampTwoPi_mem (t : ℝ) : clampTwoPi t ∈ Set.Icc 0 (2 * π) :=
  (Set.projIcc 0 (2 * π) two_pi_pos.le t).2

lemma clampTwoPi_of_mem {t : ℝ} (ht : t ∈ Set.Icc 0 (2 * π)) : clampTwoPi t = t := by
  simp [clampTwoPi, Set.projIcc_of_mem _ ht]

lemma measurable_correctedKernel_clamp (hW : IsTransport γ E W) (θ : ℝ) :
    Measurable fun t => correctedKernel W θ (clampTwoPi t) := by
  have hx : Continuous fun t => ContinuousLinearMap.adjoint (W (clampTwoPi t)) (basisVec 0) :=
    ((ContinuousLinearMap.adjoint.toLinearIsometry.continuous.comp (hW.1.comp_continuous continuous_clampTwoPi clampTwoPi_mem)).clm_apply
      continuous_const)
  exact ((measurable_const.mul (Complex.measurable_ofReal.comp (measurable_real_sign.comp
      (measurable_const.sub continuous_clampTwoPi.measurable)))).mul ((continuous_const.inner ((W θ).continuous.comp hx)).measurable.sub measurable_const)).add
    (continuous_const.mul ((continuous_const.sub
      (Complex.continuous_ofReal.comp continuous_clampTwoPi)).div_const _)).measurable |>.add (continuous_const.inner ((W θ).continuous.comp ((cutBE W).continuous.comp hx))).measurable

end PolyaNeumann
