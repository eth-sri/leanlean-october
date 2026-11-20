module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.CutFourier

public import RequestProject.FractionalInterp
public import RequestProject.CorrectedKernelSymm
public import RequestProject.CorrectedKernelCont
public import RequestProject.PlanarNotation

/-!
# Continuity in the energy of the `H^{1+δ}` bound (Lemma 6.6, last part)

Let `γ` be a closed curve with `γ'` Lipschitz on `[0, L]`, `W_E` its transports and assume
`c_{E₀} ≠ 0`. Write `r_{n m}(E)` for the double Fourier coefficients of the corrected kernel
`r_E`. We show that the difference of coefficients tends to zero in the `H^{1+δ}` seminorms as
`E → E₀`, for `0 ≤ δ < 1/2`:

* `tendsto_correctedKernelCoeff_energy` (frequency `m` in the first variable),
* `tendsto_correctedKernelCoeff_energy_snd` (frequency `n` in the second variable),
* `tendsto_mixed_correctedKernelCoeff_energy` (the mixed weights of Lemma 6.7).

Consequently the normalized remainder `Λ^{1/2} R_E Λ^{1/2} : H^t → H^{t+δ}` depends continuously
on `E` in operator norm (`tendsto_correctedRemainder_energy`).

The proof is the interpolation of `FractionalInterp.lean`: the regularity constants of `r_E`
(Lipschitz constant, Lipschitz constant of `∂_θ r_E` off the cut) stay bounded near `E₀`, and
`r_E → r_{E₀}` uniformly (`tendsto_correctedKernel_energy`); `kernelCoeff_interp` then bounds the
`H^{1+δ}` seminorm of `r_E - r_{E₀}` by a quantity tending to zero with `sup |r_E - r_{E₀}|`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real Filter MeasureTheory Topology Set
open scoped InnerProductSpace ComplexConjugate

/-! ### Fourier coefficients on `[0, 2π]` -/

/-- Fourier coefficients on `[0, 2π]` are additive on integrable functions. -/
lemma fourierCoeffOn_sub_of_intervalIntegrable {f g : ℝ → ℂ}
    (hf : IntervalIntegrable f volume 0 anglePeriod) (hg : IntervalIntegrable g volume 0 anglePeriod)
    (n : ℤ) :
    angleCoeff (fun x => f x - g x) n =
      angleCoeff f n - angleCoeff g n := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral,
    ← smul_sub]
  congr 1
  have hc : ContinuousOn (fun x : ℝ => fourier (-n) (x : AddCircle (anglePeriod - 0))) (uIcc 0 anglePeriod) :=
    ((fourier (-n)).continuous.comp (AddCircle.continuous_mk' _)).continuousOn
  simp_rw [smul_sub]
  exact intervalIntegral.integral_sub (hf.continuousOn_mul hc) (hg.continuousOn_mul hc)

/-- Double Fourier coefficients of a kernel on `[0, 2π]²`. -/
def doubleCoeff (k : ℝ → ℝ → ℂ) (p : ℤ × ℤ) : ℂ :=
  angleCoeff (fun θ => angleCoeff (k θ) p.1) p.2

/-- Double Fourier coefficients are bounded by the sup norm on the square. -/
lemma norm_doubleCoeff_le {k : ℝ → ℝ → ℂ} {M : ℝ}
    (hM : ∀ θ ∈ angleInterval, ∀ t ∈ angleInterval, ‖k θ t‖ ≤ M) (p : ℤ × ℤ) :
    ‖doubleCoeff k p‖ ≤ M :=
  norm_fourierCoeffOn_le (fun θ hθ => norm_fourierCoeffOn_le (hM θ hθ) _) _

/-- Double Fourier coefficients are additive on kernels which are bounded and measurable in `t`
and uniformly Lipschitz in `θ` on the square. -/
lemma doubleCoeff_sub {k l : ℝ → ℝ → ℂ} {M : ℝ} {K : NNReal}
    (hkm : ∀ θ, Measurable (k θ)) (hlm : ∀ θ, Measurable (l θ))
    (hkb : ∀ θ t, ‖k θ t‖ ≤ M) (hlb : ∀ θ t, ‖l θ t‖ ≤ M)
    (hkl : ∀ θ θ' t, ‖k θ t - k θ' t‖ ≤ K * |θ - θ'|)
    (hll : ∀ θ θ' t, ‖l θ t - l θ' t‖ ≤ K * |θ - θ'|) (p : ℤ × ℤ) :
    doubleCoeff (fun θ t => k θ t - l θ t) p = doubleCoeff k p - doubleCoeff l p := by
  have hint : ∀ (f : ℝ → ℝ → ℂ), (∀ θ, Measurable (f θ)) → (∀ θ t, ‖f θ t‖ ≤ M) →
      ∀ θ, IntervalIntegrable (f θ) volume 0 anglePeriod := by
    intro f hm hb θ
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).mpr ?_
    exact Measure.integrableOn_of_bounded (M := M) measure_Ioc_lt_top.ne
      (by fun_prop) (ae_of_all _ fun t => hb θ t)
  have hcoeffLip : ∀ (f : ℝ → ℝ → ℂ), (∀ θ, Measurable (f θ)) → (∀ θ t, ‖f θ t‖ ≤ M) →
      (∀ θ θ' t, ‖f θ t - f θ' t‖ ≤ K * |θ - θ'|) → ∀ n : ℤ,
      Continuous fun θ => angleCoeff (f θ) n := by
    intro f hm hb hl n
    refine (LipschitzWith.of_dist_le_mul (K := K) fun θ θ' => ?_).continuous
    rw [dist_eq_norm, Real.dist_eq,
      ← fourierCoeffOn_sub_of_intervalIntegrable (hint f hm hb θ) (hint f hm hb θ')]
    exact norm_fourierCoeffOn_le (fun t _ => hl θ θ' t) n
  unfold doubleCoeff
  have e : (fun θ => angleCoeff (fun t => k θ t - l θ t) p.1) =
      fun θ => angleCoeff (k θ) p.1 - angleCoeff (l θ) p.1 := by
    funext θ
    exact fourierCoeffOn_sub_of_intervalIntegrable (hint k hkm hkb θ) (hint l hlm hlb θ) p.1
  rw [e]
  exact fourierCoeffOn_sub_of_intervalIntegrable
    ((hcoeffLip k hkm hkb hkl p.1).intervalIntegrable _ _)
    ((hcoeffLip l hlm hlb hll p.1).intervalIntegrable _ _) p.2

/-- Second differences are additive. -/
lemma secondDiff_sub' (f g : ℝ → ℂ) (h θ : ℝ) :
    secondDiff (fun x => f x - g x) h θ = secondDiff f h θ - secondDiff g h θ := by
  unfold secondDiff
  ring

/-! ### The periodized corrected kernel -/

variable {γ : ℝ → ℂ} {K K' : NNReal} {E : ℝ} {W : TransportPath}

/-- The corrected kernel, restricted to `[0, 2π)` in `θ` and extended periodically, with `t`
clamped to `[0, 2π]`. -/
def ckPer (W : TransportPath) (θ t : ℝ) : ℂ :=
  periodize (fun θ' => correctedKernel W θ' (clampTwoPi t)) θ

lemma ckPer_apply (W : TransportPath) (θ t : ℝ) :
    ckPer W θ t = correctedKernel W (toIcoMod two_pi_pos 0 θ) (clampTwoPi t) := rfl

section

variable (hK : LipschitzWith K γ)
    (hγ' : ∀ x ∈ angleInterval, ∀ y ∈ angleInterval, ‖deriv γ x - deriv γ y‖ ≤ K' * |x - y|)
    (hW : IsTransport γ E W) (hc : cutVector W ≠ 0) (h : ℝ) (hh : 0 < h) (θ θ' : ℝ)
    (hθ : θ ∈ Icc 0 (anglePeriod - 2 * h)) (t : ℝ)

lemma toIcoMod_mem_Icc_two_pi : toIcoMod two_pi_pos 0 θ ∈ angleInterval := by
  grind [toIcoMod_mem_Ico two_pi_pos 0 θ]

include hW in
lemma measurable_ckPer : Measurable (ckPer W θ) :=
  measurable_correctedKernel_clamp hW _

include hK hW in
lemma norm_ckPer_le :
    ‖ckPer W θ t‖ ≤ 4 + ‖cutBE W‖ :=
  norm_correctedKernel_le hK hW (toIcoMod_mem_Icc_two_pi θ) (clampTwoPi_mem t)

lemma ckPer_periodic (W : TransportPath) (θ t : ℝ) : ckPer W (θ + anglePeriod) t = ckPer W θ t :=
  periodic_periodize _ θ

include hK hW hc in
lemma ckPer_eq {θ t : ℝ} (hθ : θ ∈ angleInterval)
    (ht : t ∈ angleInterval) : ckPer W θ t = correctedKernel W θ t := by
  unfold ckPer
  rw [periodize_eqOn_Icc (correctedKernel_endpoint hK hW hc (clampTwoPi_mem t)) hθ,
    clampTwoPi_of_mem ht]

/-- The Lipschitz constant in `θ` of the corrected kernel. -/
def ckLip (K : NNReal) (E : ℝ) (W : TransportPath) : NNReal :=
  ⟨Real.sqrt E * shiftConst * K * (2 + ‖cutBE W‖) + 1 / π, by
    have := shiftConst_nonneg; positivity⟩

include hK hW hc in
lemma ckPer_lip :
    ‖ckPer W θ t - ckPer W θ' t‖ ≤ ckLip K E W * |θ - θ'| := by
  have hL := lipschitzWith_periodize (K := ckLip K E W)
    (fun x hx y hy => norm_correctedKernel_sub_le hK hW hx hy (clampTwoPi_mem t))
    (correctedKernel_endpoint hK hW hc (clampTwoPi_mem t))
  have := hL.dist_le_mul θ θ'
  rwa [dist_eq_norm, Real.dist_eq] at this

/-- The Lipschitz constant of `∂_θ r_E` off the cut. -/
def ckSecond (K K' : NNReal) (E : ℝ) (W : TransportPath) : ℝ :=
  (Real.sqrt E * shiftConst * K' + (Real.sqrt E * shiftConst * K) ^ 2) * (1 + ‖cutBE W‖)

include hK hW hc hh hγ' hθ in
lemma ckPer_second :
    ‖secondDiff (fun θ => ckPer W θ t) h θ‖ ≤ ckSecond K K' E W * h ^ 2 := by
  
  have hend := correctedKernel_endpoint hK hW hc (clampTwoPi_mem t)
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hm : ∀ c, 0 ≤ c → c ≤ 2 * h → θ + c ∈ angleInterval := fun c hc0 hc1 =>
    ⟨by linarith, by linarith⟩
  have heq : secondDiff (fun θ => ckPer W θ t) h θ =
      secondDiff (fun θ => correctedKernel W θ (clampTwoPi t)) h θ := by
    simp [secondDiff, ckPer]
    rw [periodize_eqOn_Icc hend (hm (2 * h) (by linarith) le_rfl),
      periodize_eqOn_Icc hend (hm h hh.le (by linarith)),
      periodize_eqOn_Icc hend (by simpa using hm 0 le_rfl (by linarith))]
  rw [heq]
  exact norm_secondDiff_le_of_lipschitz_deriv
    (fun x hx => hasDerivWithinAt_correctedKernel hK ((LipschitzOnWith.of_dist_le_mul (K := K') fun x hx y hy => by
      rw [dist_eq_norm, Real.dist_eq]; simp [*]).continuousOn) hW (clampTwoPi_mem t) hx)
    (fun x hx y hy => norm_correctedKernelDeriv_sub_le hK hγ' hW (clampTwoPi_mem t) hx hy)
    hh ⟨hθ0, hθ1⟩

include hK hW hc in
lemma doubleCoeff_ckPer (p : ℤ × ℤ) :
    doubleCoeff (ckPer W) p = doubleCoeff (correctedKernel W) p := by
  unfold doubleCoeff
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  congr 1
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  rw [Set.uIcc_of_le two_pi_pos.le] at hθ
  congr 1
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le two_pi_pos.le] at ht
  rw [ckPer_eq hK hW hc hθ ht]

end

/-- **Quantitative comparison of two corrected kernels.** If two corrected kernels (of transports
`W`, `W₀` of the same curve, at energies `E`, `E₀`, both with `c ≠ 0`) have regularity constants
at most `A` and `C`, and differ by at most `ε` on the square, then their double Fourier
coefficients satisfy `∑_{n,m} |m|^{2+2δ} |r_{n m} - r⁰_{n m}|² ≤ interpBound (2A) (2C) ε δ`. -/
theorem correctedKernelCoeff_sub_le {E₀ : ℝ} {W₀ : TransportPath} (hK : LipschitzWith K γ)
    (hγ' : ∀ x ∈ angleInterval, ∀ y ∈ angleInterval, ‖deriv γ x - deriv γ y‖ ≤ K' * |x - y|)
    (hW : IsTransport γ E W) (hW₀ : IsTransport γ E₀ W₀)
    (hc : cutVector W ≠ 0) (hc₀ : cutVector W₀ ≠ 0)
    {A : ℝ} {C : NNReal} (hA : ckSecond K K' E W ≤ A) (hA₀ : ckSecond K K' E₀ W₀ ≤ A)
    (hC : ckLip K E W ≤ C) (hC₀ : ckLip K E₀ W₀ ≤ C) {ε : ℝ}
    (hε : ∀ θ ∈ angleInterval, ∀ t ∈ angleInterval,
      ‖correctedKernel W θ t - correctedKernel W₀ θ t‖ ≤ ε)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ < 1 / 2) :
    Summable (fun p : ℤ × ℤ => |(p.2 : ℝ)| ^ (2 + 2 * δ) *
      ‖doubleCoeff (correctedKernel W) p - doubleCoeff (correctedKernel W₀) p‖ ^ 2) ∧
    ∑' p : ℤ × ℤ, |(p.2 : ℝ)| ^ (2 + 2 * δ) *
      ‖doubleCoeff (correctedKernel W) p - doubleCoeff (correctedKernel W₀) p‖ ^ 2 ≤
      interpBound (2 * A) ((2 * C : NNReal) : ℝ) ε δ ∧
    ∀ p, ‖doubleCoeff (correctedKernel W) p - doubleCoeff (correctedKernel W₀) p‖ ≤ ε := by
  set d : ℝ → ℝ → ℂ := fun θ t => ckPer W θ t - ckPer W₀ θ t with hd
  have hAnn : 0 ≤ A := le_trans (by unfold ckSecond; have := shiftConst_nonneg; positivity) hA
  
  have hbd  := fun θ t => hε _ (toIcoMod_mem_Icc_two_pi θ) _ (clampTwoPi_mem t)
  have hlip : ∀ θ θ' t, t ∈ angleIco → ‖d θ t - d θ' t‖ ≤ ((2 * C : NNReal) : ℝ) * |θ - θ'| := by
    intro θ θ' t _
    have e1 := ckPer_lip hK hW hc θ θ' t
    have e2 := ckPer_lip hK hW₀ hc₀ θ θ' t
    
    
    have : ‖d θ t - d θ' t‖ ≤ ‖ckPer W θ t - ckPer W θ' t‖ + ‖ckPer W₀ θ t - ckPer W₀ θ' t‖ := by
      rw [show d θ t - d θ' t = (ckPer W θ t - ckPer W θ' t) - (ckPer W₀ θ t - ckPer W₀ θ' t) by
        ring]
      exact norm_sub_le _ _
    push_cast
    have h0 := abs_nonneg (θ - θ')
    nlinarith
  
  have hsecond : ∀ h : ℝ, 0 < h → h ≤ π / 2 → ∀ θ ∈ Icc 0 (anglePeriod - 2 * h),
      ∀ t ∈ angleIco, ‖secondDiff (fun θ => d θ t) h θ‖ ≤ (2 * A) * h ^ 2 := by
    intro h hh _ θ hθ t _
    rw [secondDiff_sub']
    refine (norm_sub_le _ _).trans ?_
    have e1 := ckPer_second hK hγ' hW hc h hh θ hθ t
    have e2 := ckPer_second hK hγ' hW₀ hc₀ h hh θ hθ t
    have := sq_nonneg h
    nlinarith
  obtain ⟨hs, hle⟩ := kernelCoeff_interp (fun θ =>
    (measurable_ckPer hW θ).sub (measurable_ckPer hW₀ θ)) hbd (by positivity) hlip (fun θ t _ => by
    simp [hd, ckPer_periodic]) hsecond hδ hδ'
  have hcoeff : ∀ p, doubleCoeff d p =
      doubleCoeff (correctedKernel W) p - doubleCoeff (correctedKernel W₀) p := by
    intro p
    rw [← doubleCoeff_ckPer hK hW hc, ← doubleCoeff_ckPer hK hW₀ hc₀]
    exact doubleCoeff_sub (M := 4 + ‖cutBE W‖ + ‖cutBE W₀‖) (K := ckLip K E W + ckLip K E₀ W₀)
      (measurable_ckPer hW) (measurable_ckPer hW₀)
      (fun θ t => (norm_ckPer_le hK hW θ t).trans (by simp))
      (fun θ t => (norm_ckPer_le hK hW₀ θ t).trans (by simp))
      (fun θ θ' t => (ckPer_lip hK hW hc θ θ' t).trans (by
        push_cast
        linarith [mul_nonneg (NNReal.coe_nonneg (ckLip K E₀ W₀)) (abs_nonneg (θ - θ'))]))
      (fun θ θ' t => (ckPer_lip hK hW₀ hc₀ θ θ' t).trans (by
        push_cast
        linarith [mul_nonneg (NNReal.coe_nonneg (ckLip K E W)) (abs_nonneg (θ - θ'))])) p
  change Summable (fun p : ℤ × ℤ => |(p.2 : ℝ)| ^ (2 + 2 * δ) * ‖doubleCoeff d p‖ ^ 2) at hs
  change ∑' p : ℤ × ℤ, |(p.2 : ℝ)| ^ (2 + 2 * δ) * ‖doubleCoeff d p‖ ^ 2 ≤ _ at hle
  simp [hcoeff] at hs hle
  exact ⟨hs, hle, fun p => hcoeff p ▸ norm_doubleCoeff_le (fun θ _ t _ => hbd θ t) p⟩

/-- Uniform regularity constants near `E₀`: an upper bound for `ckSecond`. -/
def ckSecondBar (K K' : NNReal) (E₀ b : ℝ) : ℝ :=
  (Real.sqrt (E₀ + 1) * shiftConst * K' + (Real.sqrt (E₀ + 1) * shiftConst * K) ^ 2) * (1 + b)

/-- Uniform regularity constants near `E₀`: an upper bound for `ckLip`. -/
def ckLipBar (K : NNReal) (E₀ b : ℝ) (hb : 0 ≤ b) : NNReal :=
  ⟨Real.sqrt (E₀ + 1) * shiftConst * K * (2 + b) + 1 / π, by
    have := shiftConst_nonneg; positivity⟩

lemma ck_consts_le {E₀ b : ℝ} (hb : 0 ≤ b) (hE : E ≤ E₀ + 1) (hB : ‖cutBE W‖ ≤ b) :
    ckSecond K K' E W ≤ ckSecondBar K K' E₀ b ∧ ckLip K E W ≤ ckLipBar K E₀ b hb := by
  have hκ := shiftConst_nonneg
  
  constructor
  · unfold ckSecond ckSecondBar
    gcongr
  · rw [← NNReal.coe_le_coe]
    simp
    change √E * shiftConst * K * (2 + ‖cutBE W‖) + 1 / π ≤
      √(E₀ + 1) * shiftConst * K * (2 + b) + 1 / π
    gcongr

variable {Ws : ℝ → TransportPath}

section

variable (hK : LipschitzWith K γ)
    (hγ' : ∀ x ∈ angleInterval, ∀ y ∈ angleInterval, ‖deriv γ x - deriv γ y‖ ≤ K' * |x - y|)
    (hWs : ∀ E, IsTransport γ E (Ws E)) (E₀ : ℝ) (hc : cutVector (Ws E₀) ≠ 0)

include hK hWs hc in
/-- `c_E ≠ 0` for `E` near `E₀` if `c_{E₀} ≠ 0`. -/
lemma eventually_cutC_ne :
    ∀ᶠ E in 𝓝 E₀, cutVector (Ws E) ≠ 0 := by
  have hC := tendsto_cutVector_energy hK hWs E₀
  exact hC.eventually_ne hc

include hK hWs hc hγ' in
/-- Uniform bounds near `E₀` for the differences of corrected-kernel coefficients: for every
`ε > 0`, for `E` near `E₀` the `H^{1+δ}` seminorm (first variable) of `r_E - r_{E₀}` is at most
`interpBound A C ε δ`, and every coefficient of `r_E - r_{E₀}` is at most `ε`. -/
lemma exists_correctedKernelCoeff_bounds {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ < 1 / 2) :
    ∃ A C : ℝ, ∀ ε, 0 < ε → ∀ᶠ E in 𝓝 E₀,
      (Summable fun p : ℤ × ℤ => |(p.2 : ℝ)| ^ (2 + 2 * δ) *
        ‖doubleCoeff (correctedKernel (Ws E)) p - doubleCoeff (correctedKernel (Ws E₀)) p‖ ^ 2) ∧
      ∑' p : ℤ × ℤ, |(p.2 : ℝ)| ^ (2 + 2 * δ) *
        ‖doubleCoeff (correctedKernel (Ws E)) p - doubleCoeff (correctedKernel (Ws E₀)) p‖ ^ 2 ≤
        interpBound A C ε δ ∧
      ∀ p, ‖doubleCoeff (correctedKernel (Ws E)) p - doubleCoeff (correctedKernel (Ws E₀)) p‖ ≤
        ε := by
  set b : ℝ := ‖cutBE (Ws E₀)‖ + 1 with hbdef
  have hb : 0 ≤ b := by positivity
  
  
  have hEE  :=
    (tendsto_id.eventually (gt_mem_nhds (show E₀ < E₀ + 1 by linarith))).mono
      fun _ h => h.le
  have h0 := ck_consts_le (K := K) (K' := K')  hb (by linarith : E₀ ≤ E₀ + 1)
    (by linarith)
  refine ⟨2 * ckSecondBar K K' E₀ b, ((2 * ckLipBar K E₀ b hb : NNReal) : ℝ), fun ε hε => ?_⟩
  filter_upwards [(eventually_cutC_ne hK hWs E₀ hc), (((tendsto_cutBE_energy hK hWs E₀ hc).norm.eventually
    (gt_mem_nhds (show ‖cutBE (Ws E₀)‖ < b by linarith))).mono fun _ h => h.le), hEE, tendsto_correctedKernel_energy hK hWs E₀ hc hε] with
    E h1 h2 h3 h4
  have hconst := ck_consts_le (K := K) (K' := K') hb h3 h2
  exact correctedKernelCoeff_sub_le hK hγ' (hWs E) (hWs E₀) h1 hc hconst.1 h0.1 hconst.2 h0.2
    (fun θ hθ t ht => (h4 θ hθ t ht).le) hδ hδ'

include hK hWs hc hγ' in
/-- The double Fourier coefficients of `r_E` converge to those of `r_{E₀}`, uniformly in the
index, as `E → E₀` (when `c_{E₀} ≠ 0`). -/
theorem tendsto_doubleCoeff_correctedKernel_energy {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ E in 𝓝 E₀, ∀ p,
      ‖doubleCoeff (correctedKernel (Ws E)) p - doubleCoeff (correctedKernel (Ws E₀)) p‖ ≤ ε := by
  obtain ⟨A, C, h⟩ := exists_correctedKernelCoeff_bounds hK hγ' hWs E₀ hc (δ := 0) le_rfl
    (by norm_num)
  exact (h ε hε).mono fun E hE => hE.2.2

include hK hWs hc hγ' in
/-- **Lemma 6.6 (continuity in the energy of the `H^{1+δ}` bound, first variable).** For a
closed curve with `γ'` Lipschitz on `[0, L]`, transports `W_E` and `c_{E₀} ≠ 0`, the double
Fourier coefficients of the corrected kernels satisfy, for `0 ≤ δ < 1/2`,
`∑_{n,m} |m|^{2+2δ} |r_{n m}(E) - r_{n m}(E₀)|² → 0` as `E → E₀` (the series converging for `E`
near `E₀`). -/
theorem tendsto_correctedKernelCoeff_energy {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ < 1 / 2) :
    (∀ᶠ E in 𝓝 E₀, Summable fun p : ℤ × ℤ => |(p.2 : ℝ)| ^ (2 + 2 * δ) *
      ‖doubleCoeff (correctedKernel (Ws E)) p - doubleCoeff (correctedKernel (Ws E₀)) p‖ ^ 2) ∧
    Tendsto (fun E => ∑' p : ℤ × ℤ, |(p.2 : ℝ)| ^ (2 + 2 * δ) *
      ‖doubleCoeff (correctedKernel (Ws E)) p - doubleCoeff (correctedKernel (Ws E₀)) p‖ ^ 2)
      (𝓝 E₀) (𝓝 0) := by
  obtain ⟨A, C, key⟩ := exists_correctedKernelCoeff_bounds hK hγ' hWs E₀ hc hδ hδ'
  refine ⟨(key 1 one_pos).mono fun E h => h.1, ?_⟩
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    ((tendsto_interpBound A C hδ').eventually (gt_mem_nhds hη))
  filter_upwards [key (r / 2) (half_pos hr)] with E hE
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ((by positivity))]
  refine hE.2.1.trans_lt (hball ?_)
  rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hr)]
  linarith

include hK hWs hc hγ' in
/-- **Lemma 6.6 (continuity in the energy, second variable).** Under the same assumptions,
`∑_{n,m} |n|^{2+2δ} |r_{n m}(E) - r_{n m}(E₀)|² → 0` as `E → E₀`, `n` being the frequency in the
second variable. -/
theorem tendsto_correctedKernelCoeff_energy_snd {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ < 1 / 2) :
    (∀ᶠ E in 𝓝 E₀, Summable fun p : ℤ × ℤ => |(p.1 : ℝ)| ^ (2 + 2 * δ) *
      ‖doubleCoeff (correctedKernel (Ws E)) p - doubleCoeff (correctedKernel (Ws E₀)) p‖ ^ 2) ∧
    Tendsto (fun E => ∑' p : ℤ × ℤ, |(p.1 : ℝ)| ^ (2 + 2 * δ) *
      ‖doubleCoeff (correctedKernel (Ws E)) p - doubleCoeff (correctedKernel (Ws E₀)) p‖ ^ 2)
      (𝓝 E₀) (𝓝 0) := by
  obtain ⟨hs, ht⟩ := tendsto_correctedKernelCoeff_energy hK hγ' hWs E₀ hc hδ hδ'
  let σ : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (-p.2, -p.1)
      invFun := fun p => (-p.2, -p.1)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  set f : ℝ → ℤ × ℤ → ℝ := fun E p => |(p.2 : ℝ)| ^ (2 + 2 * δ) *
      ‖doubleCoeff (correctedKernel (Ws E)) p - doubleCoeff (correctedKernel (Ws E₀)) p‖ ^ 2
    with hf
  have e : ∀ E, (fun p : ℤ × ℤ => |(p.1 : ℝ)| ^ (2 + 2 * δ) *
      ‖doubleCoeff (correctedKernel (Ws E)) p - doubleCoeff (correctedKernel (Ws E₀)) p‖ ^ 2) =
      f E ∘ σ := by
    intro E
    funext p
    simp only [hf, Function.comp_apply, σ, Equiv.coe_fn_mk, Int.cast_neg, abs_neg]
    congr 2
    have h1 : doubleCoeff (correctedKernel (Ws E)) p =
        conj (doubleCoeff (correctedKernel (Ws E)) (-p.2, -p.1)) :=
      correctedKernelCoeff_conj_symm hK (hWs E) p.1 p.2
    have h2 : doubleCoeff (correctedKernel (Ws E₀)) p =
        conj (doubleCoeff (correctedKernel (Ws E₀)) (-p.2, -p.1)) :=
      correctedKernelCoeff_conj_symm hK (hWs E₀) p.1 p.2
    rw [h1, h2, ← map_sub, Complex.norm_conj]
  refine ⟨hs.mono fun E h => ?_, ?_⟩
  · rw [e E]
    exact σ.summable_iff.mpr h
  · refine ht.congr fun E => ?_
    rw [e E]
    exact (Equiv.tsum_eq σ (f E)).symm

include hK hWs hc hγ' in
/-- **Weighted Hilbert–Schmidt bound, continuity in the energy** (proof of Lemma 6.7). With
`λ_n = 1 + |n|`, for `0 ≤ t ≤ 1/2` and `0 ≤ δ < 1/2`,
`∑_{n,m} λ_m^{1+2t+2δ} λ_n^{1-2t} |r_{n m}(E) - r_{n m}(E₀)|² → 0` as `E → E₀`. -/
theorem tendsto_mixed_correctedKernelCoeff_energy {δ s : ℝ} (hδ : 0 ≤ δ) (hδ' : δ < 1 / 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    (∀ᶠ E in 𝓝 E₀, Summable fun p : ℤ × ℤ => (1 + |(p.2 : ℝ)|) ^ (1 + 2 * s + 2 * δ) *
      (1 + |(p.1 : ℝ)|) ^ (1 - 2 * s) *
      ‖doubleCoeff (correctedKernel (Ws E)) p - doubleCoeff (correctedKernel (Ws E₀)) p‖ ^ 2) ∧
    Tendsto (fun E => ∑' p : ℤ × ℤ, (1 + |(p.2 : ℝ)|) ^ (1 + 2 * s + 2 * δ) *
      (1 + |(p.1 : ℝ)|) ^ (1 - 2 * s) *
      ‖doubleCoeff (correctedKernel (Ws E)) p - doubleCoeff (correctedKernel (Ws E₀)) p‖ ^ 2)
      (𝓝 E₀) (𝓝 0) := by
  obtain ⟨hs2, ht2⟩ := tendsto_correctedKernelCoeff_energy hK hγ' hWs E₀ hc hδ hδ'
  obtain ⟨hs1', ht1⟩ := tendsto_correctedKernelCoeff_energy_snd hK hγ' hWs E₀ hc hδ hδ'
  set a : ℝ → ℤ × ℤ → ℝ := fun E p =>
    ‖doubleCoeff (correctedKernel (Ws E)) p - doubleCoeff (correctedKernel (Ws E₀)) p‖ ^ 2
    with ha
  have ha0 : ∀ E p, 0 ≤ a E p := fun E p => by positivity
  have hpt : ∀ E p, (1 + |(p.2 : ℝ)|) ^ (1 + 2 * s + 2 * δ) * (1 + |(p.1 : ℝ)|) ^ (1 - 2 * s) *
      a E p ≤ 2 ^ (2 + 2 * δ) * (|(p.1 : ℝ)| ^ (2 + 2 * δ) * a E p +
        |(p.2 : ℝ)| ^ (2 + 2 * δ) * a E p + if p = 0 then a E 0 else 0) := by
    intro E p
    have := mixed_weight_le (ha0 E p) (s := 2 + 2 * δ) (α := 1 + 2 * s + 2 * δ)
      (β := 1 - 2 * s) (by linarith) (by linarith) (by ring) p
    refine this.trans (le_of_eq ?_)
    congr 2
    split_ifs with h
    · rw [h]
    · rfl
  have hsing : Summable fun p : ℤ × ℤ => (if p = 0 then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {0}) fun p hp => by simp_all
  have hbound_summable : ∀ E, Summable (fun p : ℤ × ℤ => |(p.1 : ℝ)| ^ (2 + 2 * δ) * a E p) →
      Summable (fun p : ℤ × ℤ => |(p.2 : ℝ)| ^ (2 + 2 * δ) * a E p) →
      Summable (fun p : ℤ × ℤ => 2 ^ (2 + 2 * δ) * (|(p.1 : ℝ)| ^ (2 + 2 * δ) * a E p +
        |(p.2 : ℝ)| ^ (2 + 2 * δ) * a E p + if p = 0 then a E 0 else 0)) := by
    intro E h1 h2
    refine ((h1.add h2).add ((hsing.mul_left (a E 0)).congr fun p => ?_)).mul_left _
    simp
  refine ⟨(hs1'.and hs2).mono fun E h => ?_, ?_⟩
  · exact Summable.of_nonneg_of_le (fun p => by positivity) (hpt E)
      (hbound_summable E h.1 h.2)
  · have hzero : Tendsto (fun E => a E 0) (𝓝 E₀) (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro η hη
      filter_upwards [tendsto_doubleCoeff_correctedKernel_energy hK hγ' hWs E₀ hc
        (Real.sqrt_pos.mpr (half_pos hη))] with E hE
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (ha0 E 0)]
      have h1 := hE 0
      have h2 : a E 0 ≤ Real.sqrt (η / 2) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) h1 2
      rw [Real.sq_sqrt (by positivity)] at h2
      linarith
    
    refine squeeze_zero' (Eventually.of_forall fun E => (by positivity))
      ((hs1'.and hs2).mono fun E h => ?_) (by
        have := ((ht1.add ht2).add hzero).const_mul ((2 : ℝ) ^ (2 + 2 * δ))
        simpa using this)
    calc _
        ≤ ∑' p : ℤ × ℤ, 2 ^ (2 + 2 * δ) * (|(p.1 : ℝ)| ^ (2 + 2 * δ) * a E p +
          |(p.2 : ℝ)| ^ (2 + 2 * δ) * a E p + if p = 0 then a E 0 else 0) :=
          (Summable.of_nonneg_of_le (fun p => by positivity) (hpt E)
            (hbound_summable E h.1 h.2)).tsum_le_tsum (hpt E) (hbound_summable E h.1 h.2)
      _ = _ := by
          rw [tsum_mul_left, Summable.tsum_add (h.1.add h.2)
            ((hsing.mul_left (a E 0)).congr fun p => by simp),
            Summable.tsum_add h.1 h.2, tsum_ite_eq]

/-- Hilbert–Schmidt matrix operators are additive in the matrix. -/
lemma hsMatrixOp_sub (a b : ℤ × ℤ → ℂ) (ha : Summable fun p => ‖a p‖ ^ 2)
    (hb : Summable fun p => ‖b p‖ ^ 2) (hab : Summable fun p => ‖a p - b p‖ ^ 2) :
    hsMatrixOp a ha - hsMatrixOp b hb = hsMatrixOp (fun p => a p - b p) hab := by
  refine ContinuousLinearMap.ext fun f => lp.ext (funext fun m => ?_)
  rw [ContinuousLinearMap.sub_apply, lp.coeFn_sub, Pi.sub_apply]
  change ⟪hsRow a ha m, f⟫_ℂ - ⟪hsRow b hb m, f⟫_ℂ = ⟪hsRow (fun p => a p - b p) hab m, f⟫_ℂ
  have : hsRow (fun p => a p - b p) hab m = hsRow a ha m - hsRow b hb m :=
    lp.ext (funext fun n => by
      simp [hsRow_apply])
  rw [this, inner_sub_left]

/-- **Lemma 6.7 (kernel part): continuity in the energy of the normalized remainder.** For a
closed curve with `γ'` Lipschitz on `[0, L]`, transports `W_E`, `c_{E₀} ≠ 0`, `0 ≤ t ≤ 1/2` and
`0 ≤ δ < 1/2`, the Hilbert–Schmidt operators `Λ^{1/2} R_E Λ^{1/2} : H^t → H^{t+δ}` (on `ℓ²(ℤ)`,
with matrices `correctedRemainderMatrix (W_E) δ t`) are defined for `E` near `E₀` and converge to
the one at `E₀` in operator norm as `E → E₀`. -/
theorem tendsto_correctedRemainder_energy {δ s : ℝ} (hδ : 0 ≤ δ) (hδ' : δ < 1 / 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    (∀ᶠ E in 𝓝 E₀, Summable fun p => ‖correctedRemainderMatrix (Ws E) δ s p‖ ^ 2) ∧
    ∀ η, 0 < η → ∀ᶠ E in 𝓝 E₀,
      ∀ hE : Summable (fun p => ‖correctedRemainderMatrix (Ws E) δ s p‖ ^ 2),
        ‖hsMatrixOp (correctedRemainderMatrix (Ws E) δ s) hE -
          hsMatrixOp (correctedRemainderMatrix (Ws E₀) δ s)
            (summable_correctedRemainderMatrix hK hγ' (hWs E₀) hc hδ hδ' hs0 hs1)‖ < η := by
  refine ⟨(eventually_cutC_ne hK hWs E₀ hc).mono fun E hcE =>
    summable_correctedRemainderMatrix hK hγ' (hWs E) hcE hδ hδ' hs0 hs1, ?_⟩
  intro η hη
  obtain ⟨hsm, htm⟩ := tendsto_mixed_correctedKernelCoeff_energy hK hγ' hWs E₀ hc hδ hδ' hs0 hs1
  set m : ℝ → ℤ × ℤ → ℝ := fun E p => (1 + |(p.2 : ℝ)|) ^ (1 + 2 * s + 2 * δ) *
      (1 + |(p.1 : ℝ)|) ^ (1 - 2 * s) *
      ‖doubleCoeff (correctedKernel (Ws E)) p - doubleCoeff (correctedKernel (Ws E₀)) p‖ ^ 2
    with hm
  let σ : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (-p.2, p.1)
      invFun := fun p => (p.2, -p.1)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  have hsq : ∀ x : ℝ, 0 ≤ x → ∀ c : ℝ, (x ^ (c / 2)) ^ 2 = x ^ c := fun x hx c => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  have e : ∀ E, (fun p => ‖correctedRemainderMatrix (Ws E) δ s p -
      correctedRemainderMatrix (Ws E₀) δ s p‖ ^ 2) = fun p => anglePeriod ^ 2 * m E (σ p) := by
    intro E
    funext p
    
    
    rw [correctedRemainderMatrix, correctedRemainderMatrix, ← mul_sub, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow,
      mul_pow, mul_pow, hsq _ (by positivity), hsq _ (by positivity)]
    simp [hm, σ, doubleCoeff] <;> ring
  have hlim := htm.const_mul (anglePeriod ^ 2)
  have hsqrt : Tendsto (fun E => Real.sqrt (anglePeriod ^ 2 * ∑' p, m E p)) (𝓝 E₀) (𝓝 0) := by
    simpa using hlim.sqrt
  filter_upwards [hsm, hsqrt.eventually (gt_mem_nhds hη)] with E hmE hE hsumE
  have hab : Summable fun p => ‖correctedRemainderMatrix (Ws E) δ s p -
      correctedRemainderMatrix (Ws E₀) δ s p‖ ^ 2 := by
    rw [e E]
    exact (σ.summable_iff.mpr hmE).mul_left _
  rw [hsMatrixOp_sub _ _ _ _ hab]
  refine (norm_hsMatrixOp_le _ hab).trans_lt (lt_of_eq_of_lt ?_ hE)
  congr 1
  rw [e E, tsum_mul_left]
  congr 1
  exact Equiv.tsum_eq σ (m E)

end

end PolyaNeumann
