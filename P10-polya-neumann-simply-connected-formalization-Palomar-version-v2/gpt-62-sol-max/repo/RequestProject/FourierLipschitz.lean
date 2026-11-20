module

public import RequestProject.SobolevCircle
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Fourier coefficients of Lipschitz rows (the Hilbert–Schmidt estimate of Lemma 6.3)

Let `r : ℝ → H` be a `2π`-periodic `K`-Lipschitz map into a complex inner product space and
`(vⱼ)` an orthonormal family. For the scalar functions `φⱼ(θ) = ⟨r(θ), vⱼ⟩` with Fourier
coefficients `cⱼ(n)` on `[0, 2π]`,

  `∑ⱼ ∑ₙ n² |cⱼ(n)|² ≤ π² K² / 4`     (`sum_sq_mul_fourierCoeff_le`, `summable_sq_mul_fourierCoeff`).

This is the Hilbert–Schmidt bound into `H¹(𝕋)` used in Lemma 6.3 (periodic projected observation)
for the row `r(θ) = Π^c_E W_E(θ)^* e₀`. The proof uses difference quotients instead of
derivatives: by Parseval, `∑ₙ |e^{inh} - 1|² |cⱼ(n)|² = (2π)⁻¹ ∫ |φⱼ(θ+h) - φⱼ(θ)|²`, the Bessel
inequality sums this over `j` to at most `K² h²`, and `|e^{inh} - 1| ≥ 2|nh|/π` for `|nh| ≤ π`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real Filter MeasureTheory Set
open scoped InnerProductSpace

/-- Fourier coefficients of a shifted periodic function. -/
lemma fourierCoeffOn_comp_add {φ : ℝ → ℂ} (hper : Function.Periodic φ (2 * π)) (h : ℝ)
    (n : ℤ) :
    fourierCoeffOn two_pi_pos (fun θ => φ (θ + h)) n =
      Complex.exp (n * h * Complex.I) * fourierCoeffOn two_pi_pos φ n := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  set F : ℝ → ℂ := fun u => (fourier (-n) (u : AddCircle (2 * π - 0))) • φ u with hF
  have hFper : Function.Periodic F (2 * π) := by
    intro u
    show (fourier (-n) (((u + 2 * π : ℝ)) : AddCircle (2 * π - 0))) • φ (u + 2 * π) =
      (fourier (-n) ((u : ℝ) : AddCircle (2 * π - 0))) • φ u
    simp_all
  have hpt : ∀ θ : ℝ, (fourier (-n) (θ : AddCircle (2 * π - 0))) • φ (θ + h) =
      Complex.exp (n * h * Complex.I) * F (θ + h) := by
    intro θ
    simp only [hF, fourier_coe_apply, smul_eq_mul]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    have : (π : ℂ) ≠ 0 := by simp
    push_cast
    field_simp
    ring
  have hcongr : ∫ x in (0 : ℝ)..(2 * π), (fourier (-n) (x : AddCircle (2 * π - 0))) • φ (x + h) =
      ∫ x in (0 : ℝ)..(2 * π), Complex.exp (n * h * Complex.I) * F (x + h) :=
    intervalIntegral.integral_congr fun θ _ => hpt θ
  rw [hcongr, intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_right]
  have := hFper.intervalIntegral_add_eq h 0
  rw [zero_add, add_comm h (2 * π)] at this
  rw [zero_add, this]
  simp only [Complex.real_smul]
  ring

/-- Fourier coefficients on `[0, 2π]` are additive for functions continuous on `[0, 2π]`. -/
lemma fourierCoeffOn_sub_of_continuousOn {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {f g : ℝ → F} (hf : ContinuousOn f (Icc 0 (2 * π)))
    (hg : ContinuousOn g (Icc 0 (2 * π))) (n : ℤ) :
    fourierCoeffOn two_pi_pos (fun θ => f θ - g θ) n =
      fourierCoeffOn two_pi_pos f n - fourierCoeffOn two_pi_pos g n := by
  have hc : ContinuousOn (fun x : ℝ => fourier (-n) (x : AddCircle (2 * π - 0)))
      (uIcc 0 (2 * π)) :=
    ((map_continuous (fourier (-n))).comp continuous_quotient_mk').continuousOn
  rw [uIcc_of_le two_pi_pos.le] at hc
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral,
    ← smul_sub, ← intervalIntegral.integral_sub]
  · simp_rw [smul_sub]
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le two_pi_pos.le]
    fun_prop
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le two_pi_pos.le]
    fun_prop

lemma fourierCoeffOn_sub_of_continuous {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (n : ℤ) : fourierCoeffOn two_pi_pos (fun θ => f θ - g θ) n =
      fourierCoeffOn two_pi_pos f n - fourierCoeffOn two_pi_pos g n :=
  fourierCoeffOn_sub_of_continuousOn hf.continuousOn hg.continuousOn n

/-- Parseval's identity on `[0, 2π]` for continuous functions. -/
lemma hasSum_sq_fourierCoeffOn_of_continuous {φ : ℝ → ℂ} (hφ : Continuous φ) :
    HasSum (fun n => ‖fourierCoeffOn two_pi_pos φ n‖ ^ 2)
      ((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), ‖φ θ‖ ^ 2) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn
    hφ.continuousOn
  have hmem : MemLp φ 2 (volume.restrict (Set.Ioc 0 (2 * π))) := by
    refine MemLp.of_bound hφ.aestronglyMeasurable C ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => hC x (Set.Ioc_subset_Icc_self hx)
  have := hasSum_sq_fourierCoeffOn two_pi_pos hmem
  simp_all

/-- `|e^{ix} - 1|² ≥ 4x²/π²` for `|x| ≤ π`. -/
lemma sq_le_norm_exp_sub_one_sq {x : ℝ} (hx : |x| ≤ π) :
    4 / π ^ 2 * x ^ 2 ≤ ‖Complex.exp (x * Complex.I) - 1‖ ^ 2 := by
  have hnorm : ‖Complex.exp (x * Complex.I) - 1‖ ^ 2 = 4 * Real.sin (|x| / 2) ^ 2 := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.sq_norm,
      Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, Complex.one_re, Complex.sub_im, Complex.add_im,
      Complex.mul_im, Complex.one_im]
    have h1 : Real.sin (|x| / 2) ^ 2 = Real.sin (x / 2) ^ 2 := by
      rcases abs_choice x with h | h
      lia
      simp [h, neg_div, Real.sin_neg]
    rw [h1]
    have h2 : Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
      have := Real.cos_two_mul (x / 2)
      rw [show 2 * (x / 2) = x by ring] at this
      nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
    have h4 := Real.sin_sq_add_cos_sq x
    linarith
  rw [hnorm]
  have hpos : 0 ≤ |x| / 2 := by positivity
  have hle : |x| / 2 ≤ π / 2 := by linarith
  have hs := Real.mul_le_sin hpos hle
  have hs0 : 0 ≤ 2 / π * (|x| / 2) := by positivity
  have : (2 / π * (|x| / 2)) ^ 2 ≤ Real.sin (|x| / 2) ^ 2 := pow_le_pow_left₀ hs0 hs 2
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hpi : 0 < π := pi_pos
  rw [hx2]
  calc 4 / π ^ 2 * |x| ^ 2 = 4 * (2 / π * (|x| / 2)) ^ 2 := by field_simp
    _ ≤ 4 * Real.sin (|x| / 2) ^ 2 := by linarith

section BesselRows

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {v : ι → H} {r : ℝ → H}

private theorem sum_tsum_sq_fourierCoeff_rows_le (hv : Orthonormal ℂ v) (hr : Continuous r)
    {C : ℝ} (hC : ∀ θ ∈ Icc 0 (2 * π), ‖r θ‖ ^ 2 ≤ C) (J : Finset ι) :
    ∑ j ∈ J, ∑' n : ℤ, ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v j⟫_ℂ) n‖ ^ 2 ≤ C := by
  have hc (j : ι) : Continuous fun θ => ‖⟪r θ, v j⟫_ℂ‖ ^ 2 := (hr.inner continuous_const).norm.pow 2
  simp_rw [fun j => (hasSum_sq_fourierCoeffOn_of_continuous (hr.inner (continuous_const (y := v j)))).tsum_eq]
  rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum fun j _ => (hc j).intervalIntegrable _ _]
  have hi := intervalIntegral.integral_mono_on (μ := volume) two_pi_pos.le
    ((continuous_finset_sum J fun j _ => hc j).intervalIntegrable _ _)
    (intervalIntegrable_const (c := C)) (fun θ hθ => by
      simp_rw [norm_inner_symm (r θ)]
      exact (hv.sum_inner_products_le (r θ)).trans (hC θ hθ))
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hi
  calc
    _ ≤ (2 * π)⁻¹ * (2 * π * C) := by gcongr
    _ = C := inv_mul_cancel_left₀ two_pi_pos.ne' _

/-- Bessel's inequality for Fourier coefficients of the scalar rows of a continuous vector. -/
theorem tsum_sq_fourierCoeff_rows_le (hv : Orthonormal ℂ v) (hr : Continuous r) {B : ℝ}
    (hB : ∀ θ ∈ Icc 0 (2 * π), ‖r θ‖ ≤ B) :
    Summable (fun p : ι × ℤ => ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v p.1⟫_ℂ) p.2‖ ^ 2) ∧
    ∑' p : ι × ℤ, ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v p.1⟫_ℂ) p.2‖ ^ 2 ≤ B ^ 2 := by
  have hs (j : ι) := (hasSum_sq_fourierCoeffOn_of_continuous
    (hr.inner (continuous_const (y := v j)))).summable
  have h (J : Finset ι) := sum_tsum_sq_fourierCoeff_rows_le hv hr
    (C := B ^ 2) (fun θ hθ => pow_le_pow_left₀ (norm_nonneg _) (hB θ hθ) 2) J
  have hsum := summable_of_sum_le (f := fun j =>
    ∑' n : ℤ, ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v j⟫_ℂ) n‖ ^ 2)
    (fun j => tsum_nonneg fun _ => sq_nonneg _) h
  have hp := (summable_prod_of_nonneg (f := fun p : ι × ℤ =>
    ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v p.1⟫_ℂ) p.2‖ ^ 2) (fun _ => sq_nonneg _)).mpr ⟨hs, hsum⟩
  exact ⟨hp, hp.tsum_prod.trans_le (hsum.tsum_le_of_sum_le h)⟩

end BesselRows

section Rows

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {v : ι → H} (hv : Orthonormal ℂ v) {r : ℝ → H} {K : NNReal} (hr : LipschitzWith K r)
  (hper : Function.Periodic r (2 * π))
include hv hr hper

omit hv in
private lemma fourierCoeffOn_inner_diff (u : H) (h : ℝ) (n : ℤ) :
    fourierCoeffOn two_pi_pos (fun θ => ⟪r (θ + h) - r θ, u⟫_ℂ) n =
      (Complex.exp (n * h * Complex.I) - 1) *
        fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, u⟫_ℂ) n := by
  have hc : Continuous fun θ => ⟪r θ, u⟫_ℂ := hr.continuous.inner continuous_const
  have hp : Function.Periodic (fun θ => ⟪r θ, u⟫_ℂ) (2 * π) := fun θ => congrArg (fun x => ⟪x, u⟫_ℂ) (hper θ)
  simp_rw [inner_sub_left]
  have ht : Continuous fun θ => ⟪r (θ + h), u⟫_ℂ :=
    hc.comp (by fun_prop : Continuous fun θ : ℝ => θ + h)
  rw [fourierCoeffOn_sub_of_continuous ht hc, fourierCoeffOn_comp_add hp, sub_mul, one_mul]

/-- The difference-quotient estimate over finite sets of rows. -/
lemma sum_tsum_diff_le (J : Finset ι) (h : ℝ) :
    ∑ j ∈ J, ∑' n : ℤ, ‖Complex.exp (n * h * Complex.I) - 1‖ ^ 2 *
        ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v j⟫_ℂ) n‖ ^ 2 ≤ K ^ 2 * h ^ 2 := by
  have hd : Continuous fun θ => r (θ + h) - r θ := hr.continuous.comp
    (by fun_prop : Continuous fun θ : ℝ => θ + h) |>.sub hr.continuous
  have hC (θ : ℝ) : ‖r (θ + h) - r θ‖ ^ 2 ≤ K ^ 2 * h ^ 2 := by
    rw [← sq_abs h, ← mul_pow]
    have hl := hr.dist_le_mul (θ + h) θ
    rw [dist_eq_norm, Real.dist_eq, add_sub_cancel_left] at hl
    exact pow_le_pow_left₀ (norm_nonneg _) hl 2
  simpa only [fourierCoeffOn_inner_diff hr hper, norm_mul, mul_pow] using
    sum_tsum_sq_fourierCoeff_rows_le hv hd (fun θ _ => hC θ) J

/-- Finite form of the `H¹` Hilbert–Schmidt estimate. -/
lemma sum_sq_mul_fourierCoeff_le_of_finite (J : Finset ι) (N : ℕ) :
    ∑ j ∈ J, ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
        (n : ℝ) ^ 2 * ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v j⟫_ℂ) n‖ ^ 2 ≤
      π ^ 2 * K ^ 2 / 4 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Nat.cast_zero, neg_zero, Finset.Icc_self, Finset.sum_singleton, Int.cast_zero]
    simp  
    positivity
  set h : ℝ := π / N with hh
  have hNpos : (0 : ℝ) < N := by positivity
  have hhpos : 0 < h := div_pos pi_pos hNpos
  set c : ι → ℤ → ℂ := fun j n => fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v j⟫_ℂ) n
  have hsumm : ∀ j, Summable fun n : ℤ =>
      ‖Complex.exp (n * h * Complex.I) - 1‖ ^ 2 * ‖c j n‖ ^ 2 := by
    intro j
    have hd : Continuous fun θ => ⟪r (θ + h) - r θ, v j⟫_ℂ :=
      (hr.continuous.comp (by fun_prop : Continuous fun θ : ℝ => θ + h) |>.sub hr.continuous).inner continuous_const
    simpa only [c, fourierCoeffOn_inner_diff hr hper, norm_mul, mul_pow] using
      (hasSum_sq_fourierCoeffOn_of_continuous hd).summable
  have hpt : ∀ j, ∀ n ∈ Finset.Icc (-(N : ℤ)) N, (n : ℝ) ^ 2 * ‖c j n‖ ^ 2 ≤
      π ^ 2 / (4 * h ^ 2) * (‖Complex.exp (n * h * Complex.I) - 1‖ ^ 2 * ‖c j n‖ ^ 2) := by
    intro j n hn
    rw [Finset.mem_Icc] at hn
    have habs : |(n : ℝ) * h| ≤ π := by
      rw [abs_mul, abs_of_pos hhpos, hh]
      have : |(n : ℝ)| ≤ N := by
        rw [abs_le]; norm_cast
      calc |(n : ℝ)| * (π / N) ≤ N * (π / N) := by gcongr
        _ = π := by field_simp
    have hk := sq_le_norm_exp_sub_one_sq habs
    have heq : ((n * h : ℝ) : ℂ) * Complex.I = (n : ℂ) * h * Complex.I := by simp
    rw [heq] at hk
    have hpi : 0 < π := pi_pos
    have key : (n : ℝ) ^ 2 ≤ π ^ 2 / (4 * h ^ 2) * ‖Complex.exp (n * h * Complex.I) - 1‖ ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have : 4 / π ^ 2 * ((n : ℝ) * h) ^ 2 * π ^ 2 = 4 * h ^ 2 * (n : ℝ) ^ 2 := by
        field_simp
      nlinarith
    calc (n : ℝ) ^ 2 * ‖c j n‖ ^ 2 ≤
        (π ^ 2 / (4 * h ^ 2) * ‖Complex.exp (n * h * Complex.I) - 1‖ ^ 2) * ‖c j n‖ ^ 2 := by
          gcongr
      _ = _ := by ring
  calc ∑ j ∈ J, ∑ n ∈ Finset.Icc (-(N : ℤ)) N, (n : ℝ) ^ 2 * ‖c j n‖ ^ 2
      ≤ ∑ j ∈ J, ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
          π ^ 2 / (4 * h ^ 2) * (‖Complex.exp (n * h * Complex.I) - 1‖ ^ 2 * ‖c j n‖ ^ 2) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun n hn => hpt j n hn
    _ = π ^ 2 / (4 * h ^ 2) * ∑ j ∈ J, ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
          ‖Complex.exp (n * h * Complex.I) - 1‖ ^ 2 * ‖c j n‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
    _ ≤ π ^ 2 / (4 * h ^ 2) * ∑ j ∈ J, ∑' n : ℤ,
          ‖Complex.exp (n * h * Complex.I) - 1‖ ^ 2 * ‖c j n‖ ^ 2 := by
        gcongr with j hj
        exact (hsumm j).sum_le_tsum _ fun n _ => by positivity
    _ ≤ π ^ 2 / (4 * h ^ 2) * (K ^ 2 * h ^ 2) := by
        gcongr
        exact sum_tsum_diff_le hv hr hper J h
    _ = π ^ 2 * K ^ 2 / 4 := by field_simp

private lemma sum_sq_mul_fourierCoeff_le (u : Finset (ι × ℤ)) :
    ∑ p ∈ u, ((p.2 : ℝ)) ^ 2 * ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v p.1⟫_ℂ) p.2‖ ^ 2 ≤ π ^ 2 * K ^ 2 / 4 := by
  classical
  set J : Finset ι := u.image Prod.fst
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ p ∈ u, p.2 ∈ Finset.Icc (-(N : ℤ)) N := by
    refine ⟨(u.image fun p => p.2.natAbs).sup id, fun p hp => ?_⟩
    have : p.2.natAbs ≤ (u.image fun p => p.2.natAbs).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hp)
    rw [Finset.mem_Icc]
    omega
  calc ∑ p ∈ u, ((p.2 : ℝ)) ^ 2 * ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v p.1⟫_ℂ) p.2‖ ^ 2
      ≤ ∑ p ∈ J ×ˢ Finset.Icc (-(N : ℤ)) N,
          ((p.2 : ℝ)) ^ 2 * ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v p.1⟫_ℂ) p.2‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p _ _ => by positivity
        rw [Finset.mem_product]
        grind
    _ = ∑ j ∈ J, ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
          (n : ℝ) ^ 2 * ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v j⟫_ℂ) n‖ ^ 2 :=
        Finset.sum_product _ _ _
    _ ≤ π ^ 2 * K ^ 2 / 4 := sum_sq_mul_fourierCoeff_le_of_finite hv hr hper J N

/-- **`H¹` Hilbert–Schmidt estimate for Lipschitz rows.** For a `2π`-periodic `K`-Lipschitz
`r : ℝ → H` and an orthonormal family `(vⱼ)`, the Fourier coefficients `cⱼ(n)` of
`θ ↦ ⟨r(θ), vⱼ⟩` satisfy `∑ⱼ ∑ₙ n² |cⱼ(n)|² < ∞`, with sum at most `π² K² / 4`. -/
theorem summable_sq_mul_fourierCoeff :
    Summable fun p : ι × ℤ =>
      ((p.2 : ℝ)) ^ 2 * ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v p.1⟫_ℂ) p.2‖ ^ 2 := summable_of_sum_le (fun _ => by positivity) (sum_sq_mul_fourierCoeff_le hv hr hper)

/-- The value bound: `∑ⱼ ∑ₙ n² |cⱼ(n)|² ≤ π² K² / 4`. -/
theorem tsum_sq_mul_fourierCoeff_le :
    ∑' p : ι × ℤ,
      ((p.2 : ℝ)) ^ 2 * ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v p.1⟫_ℂ) p.2‖ ^ 2 ≤
      π ^ 2 * K ^ 2 / 4 := Summable.tsum_le_of_sum_le (summable_sq_mul_fourierCoeff hv hr hper) (sum_sq_mul_fourierCoeff_le hv hr hper)

end Rows

end PolyaNeumann
