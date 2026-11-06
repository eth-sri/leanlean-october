module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

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

public section


namespace PolyaNeumann

open Real Filter MeasureTheory
open scoped InnerProductSpace

/-- The Fourier phase lies on the unit circle, so its distance from one is at most two. -/
lemma norm_fourierPhase_sub_one_le (n : ℤ) (h : ℝ) :
    ‖Complex.exp (n * h * Complex.I) - 1‖ ≤ 2 := by
  refine (norm_sub_le _ _).trans ?_
  rw [show (n : ℂ) * h * Complex.I = ((n * h : ℝ) : ℂ) * Complex.I from (by push_cast; ring),
    Complex.norm_exp_ofReal_mul_I]
  norm_num

lemma norm_fourierCoeffOn_le_of_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {f : ℝ → F} 
    (hM : ∀ x ∈ boundaryInterval, ‖f x‖ ≤ M) n :
    ‖fourierCoeffOn two_pi_pos f n‖ ≤ M := by
  rw [fourierCoeffOn_eq_integral, norm_smul]
  have hb : ∀ x ∈ Set.uIoc (0 : ℝ) circlePeriod,
      ‖fourier (-n) (x : AddCircle (2 * π - 0)) • f x‖ ≤ M := by
    intro x hx
    rw [Set.uIoc_of_le two_pi_pos.le] at hx
    rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
    exact hM x (Set.Ioc_subset_Icc_self hx)
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  have h2 : (0 : ℝ) < 2 * π - 0 := by rw [sub_zero]; exact two_pi_pos
  rw [abs_of_pos h2] at this
  refine (mul_le_mul_of_nonneg_left this (norm_nonneg (1 / (2 * π - 0)))).trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  field_simp


lemma fourierCoeffOn_sub_of_intervalIntegrable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {f g : ℝ → F}
    (hf : IntervalIntegrable f volume 0 circlePeriod) (hg : IntervalIntegrable g volume 0 circlePeriod)
    n :
    fourierCoeffOn two_pi_pos (fun x => f x - g x) n =
      fourierCoeffOn two_pi_pos f n - fourierCoeffOn two_pi_pos g n := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral,
    ← smul_sub]
  congr 1
  have hc : ContinuousOn (fun x : ℝ => fourier (-n) (x : AddCircle (2 * π - 0))) (Set.uIcc 0 circlePeriod) :=
    ((fourier (-n)).continuous.comp (AddCircle.continuous_mk' _)).continuousOn
  simp_rw [smul_sub]
  exact intervalIntegral.integral_sub (hf.continuousOn_smul hc) (hg.continuousOn_smul hc)


lemma fourierCoeffOn_sub_of_continuousOn {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {f g : ℝ → F} (hf : ContinuousOn f boundaryInterval)
    (hg : ContinuousOn g boundaryInterval) n :
    fourierCoeffOn two_pi_pos (fun θ => f θ - g θ) n =
      fourierCoeffOn two_pi_pos f n - fourierCoeffOn two_pi_pos g n :=
  fourierCoeffOn_sub_of_intervalIntegrable
    (ContinuousOn.intervalIntegrable_of_Icc two_pi_pos.le hf)
    (ContinuousOn.intervalIntegrable_of_Icc two_pi_pos.le hg) n


/-- Fourier coefficients of a shifted periodic function. -/
lemma fourierCoeffOn_comp_add  (hper : Function.Periodic φ circlePeriod) h
    n :
    fourierCoeffOn two_pi_pos (fun θ => φ (θ + h)) n =
      Complex.exp (n * h * Complex.I) * fourierCoeffOn two_pi_pos φ n := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  set F : ComplexCurve := fun u => (fourier (-n) u) • φ u with hF
  have hFper : Function.Periodic F circlePeriod := by
    intro u
    show (fourier (-n) (((u + 2 * π : ℝ)))) • φ (u + 2 * π) =
      (fourier (-n) u) • φ u
    simp_all
  have hpt : ∀ θ : ℝ, (fourier (-n) (θ : AddCircle (2 * π - 0))) • φ (θ + h) =
      Complex.exp (n * h * Complex.I) * F (θ + h) := by
    intro θ
    simp only [hF, fourier_coe_apply, smul_eq_mul]
    rw [← mul_assoc, ← Complex.exp_add]
    push_cast
    field_simp
    ring
  have hcongr : ∫ x in (0 : ℝ)..circlePeriod, (fourier (-n) (x : AddCircle (2 * π - 0))) • φ (x + h) =
      ∫ x in (0 : ℝ)..circlePeriod, Complex.exp (n * h * Complex.I) * F (x + h) :=
    intervalIntegral.integral_congr fun θ _ => hpt θ
  rw [hcongr, intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_right]
  have := hFper.intervalIntegral_add_eq h 0
  rw [zero_add, add_comm h circlePeriod] at this
  rw [zero_add, this]
  simp only [Complex.real_smul]
  ring

/-- Parseval's identity on `[0, 2π]` for continuous functions. -/
lemma hasSum_sq_fourierCoeffOn_of_continuous {φ : ComplexCurve} (hφ : Continuous φ) :
    HasSum (fun n => ‖fourierCoeffOn two_pi_pos φ n‖ ^ 2)
      (circlePeriod⁻¹ * ∫ θ in (0 : ℝ)..circlePeriod, ‖φ θ‖ ^ 2) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := 0) (b := 2 * π)).exists_bound_of_continuousOn
    hφ.continuousOn
  have hmem : MemLp φ 2 (volume.restrict boundaryHalfOpenInterval) := by
    refine MemLp.of_bound hφ.aestronglyMeasurable C ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => hC x (Set.Ioc_subset_Icc_self hx)
  have := hasSum_sq_fourierCoeffOn two_pi_pos hmem
  simpa  using this

/-- `|e^{ix} - 1|² ≥ 4x²/π²` for `|x| ≤ π`. -/
lemma sq_le_norm_exp_sub_one_sq  (hx : |x| ≤ π) :
    4 / π ^ 2 * x ^ 2 ≤ ‖Complex.exp (x * Complex.I) - 1‖ ^ 2 := by
  have hnorm : ‖Complex.exp (x * Complex.I) - 1‖ ^ 2 = 4 * Real.sin (|x| / 2) ^ 2 := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.sq_norm,
      Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, Complex.one_re, Complex.sub_im, Complex.add_im,
      Complex.mul_im, Complex.one_im]
    have h1 : Real.sin (|x| / 2) ^ 2 = Real.sin (x / 2) ^ 2 := by
      rcases abs_choice x with h | h
      · rw [h]
      · rw [h, neg_div, Real.sin_neg, neg_sq]
    have h2 : Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
      have := Real.cos_two_mul (x / 2)
      rw [show 2 * (x / 2) = x by ring] at this
      nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
    have h4 := Real.sin_sq_add_cos_sq x
    nlinarith [h2, h4]
  rw [hnorm]
  have hpos : 0 ≤ |x| / 2 := by positivity
  have hle : |x| / 2 ≤ π / 2 := by linarith
  have hs := Real.mul_le_sin hpos hle
  have hs0 : 0 ≤ 2 / π * (|x| / 2) := by positivity
  have  := pow_le_pow_left₀ hs0 hs 2
  have hx2  := (sq_abs x).symm
  rw [hx2]
  calc 4 / π ^ 2 * |x| ^ 2 = 4 * (2 / π * (|x| / 2)) ^ 2 := by field_simp
    _ ≤ 4 * Real.sin (|x| / 2) ^ 2 := by linarith

section Rows

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {v : ι → H} (hv : Orthonormal ℂ v) {r : ℝ → H} {K } (hr : LipschitzWith K r)
  (hper : Function.Periodic r circlePeriod)
include hv hr hper

/-- The difference-quotient estimate: `∑ⱼ ∑ₙ |e^{inh} - 1|² |cⱼ(n)|² ≤ K² h²` over finite sets
of indices `j`. -/
lemma sum_tsum_diff_le J (h : ℝ) :
    ∑ j ∈ J, ∑' n : ℤ, ‖Complex.exp (n * h * Complex.I) - 1‖ ^ 2 *
        ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v j⟫_ℂ) n‖ ^ 2 ≤ K ^ 2 * h ^ 2 := by
  have hcont : ∀ j, Continuous fun θ => ⟪r θ, v j⟫_ℂ := fun j =>
    hr.continuous.inner continuous_const
  have hperj : ∀ j, Function.Periodic (fun θ => ⟪r θ, v j⟫_ℂ) circlePeriod := fun j θ => by
    simp  [hper θ]
  -- coefficients of the difference
  have hcoef : ∀ j n, fourierCoeffOn two_pi_pos (fun θ => ⟪r (θ + h) - r θ, v j⟫_ℂ) n =
      (Complex.exp (n * h * Complex.I) - 1) *
        fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v j⟫_ℂ) n := by
    intro j n
    simp_rw [inner_sub_left]
    have h1 := fourierCoeffOn_sub_of_continuousOn (f := fun θ => ⟪r (θ + h), v j⟫_ℂ)
      (g := fun θ => ⟪r θ, v j⟫_ℂ) ((hcont j).comp ((continuous_id.add continuous_const))).continuousOn (hcont j).continuousOn n
    have h2 := fourierCoeffOn_comp_add (hperj j) h n
    grind
  have hterm : ∀ j, ∑' n : ℤ, ‖Complex.exp (n * h * Complex.I) - 1‖ ^ 2 *
        ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v j⟫_ℂ) n‖ ^ 2 =
      circlePeriod⁻¹ * ∫ θ in (0 : ℝ)..circlePeriod, ‖⟪r (θ + h) - r θ, v j⟫_ℂ‖ ^ 2 := by
    intro j
    have hc : Continuous fun θ => ⟪r (θ + h) - r θ, v j⟫_ℂ :=
      ((hr.continuous.comp ((continuous_id.add continuous_const))).sub hr.continuous).inner continuous_const
    rw [← (hasSum_sq_fourierCoeffOn_of_continuous hc).tsum_eq]
    congr 1
    ext <;> simp_all <;> ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, ← intervalIntegral.integral_finset_sum]
  swap
  · intro j _
    exact (((hr.continuous.comp ((continuous_id.add continuous_const))).sub hr.continuous).inner
      continuous_const).norm.pow 2 |>.intervalIntegrable _ _
  have hbound : ∀ θ, ∑ j ∈ J, ‖⟪r (θ + h) - r θ, v j⟫_ℂ‖ ^ 2 ≤ K ^ 2 * h ^ 2 := by
    intro θ
    have hb := hv.sum_inner_products_le (r (θ + h) - r θ) (s := J)
    have hl : ‖r (θ + h) - r θ‖ ≤ K * |h| := by
      have := hr.dist_le_mul (θ + h) θ
      rw [dist_eq_norm, Real.dist_eq] at this
      simpa using this
    calc ∑ j ∈ J, ‖⟪r (θ + h) - r θ, v j⟫_ℂ‖ ^ 2
        = ∑ j ∈ J, ‖⟪v j, r (θ + h) - r θ⟫_ℂ‖ ^ 2 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [norm_inner_symm]
      _ ≤ ‖r (θ + h) - r θ‖ ^ 2 := hb
      _ ≤ (K * |h|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hl 2
      _ = K ^ 2 * h ^ 2 := by rw [mul_pow, sq_abs]
  have hint : ∫ θ in (0 : ℝ)..circlePeriod, ∑ j ∈ J, ‖⟪r (θ + h) - r θ, v j⟫_ℂ‖ ^ 2 ≤
      ∫ θ in (0 : ℝ)..circlePeriod, (K : ℝ) ^ 2 * h ^ 2 := by
    refine intervalIntegral.integral_mono_on two_pi_pos.le ?_ intervalIntegrable_const
      fun θ _ => hbound θ
    refine (continuous_finset_sum _ fun j _ => ?_).intervalIntegrable _ _
    exact (((hr.continuous.comp ((continuous_id.add continuous_const))).sub hr.continuous).inner
      continuous_const).norm.pow 2
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hint
  calc circlePeriod⁻¹ * ∫ θ in (0)..circlePeriod, ∑ j ∈ J, ‖⟪r (θ + h) - r θ, v j⟫_ℂ‖ ^ 2
      ≤ circlePeriod⁻¹ * (2 * π * (K ^ 2 * h ^ 2)) := by gcongr
    _ = K ^ 2 * h ^ 2 := by field_simp

/-- Finite form of the `H¹` Hilbert–Schmidt estimate. -/
lemma sum_sq_mul_fourierCoeff_le_of_finite J (N : ℕ) :
    ∑ j ∈ J, ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
        (n : ℝ) ^ 2 * ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v j⟫_ℂ) n‖ ^ 2 ≤
      π ^ 2 * K ^ 2 / 4 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp  
    positivity
  set h : ℝ := π / N with hh
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hhpos : 0 < h := div_pos pi_pos hNpos
  set c : ι → FourierSeq := fun j n => fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v j⟫_ℂ) n
  have hsumm : ∀ j, Summable fun n : ℤ =>
      ‖Complex.exp (n * h * Complex.I) - 1‖ ^ 2 * ‖c j n‖ ^ 2 := by
    intro j
    have hc : Continuous fun θ => ⟪r θ, v j⟫_ℂ := hr.continuous.inner continuous_const
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((hasSum_sq_fourierCoeffOn_of_continuous hc).summable.mul_left 4)
    have : ‖Complex.exp (n * h * Complex.I) - 1‖ ≤ 2 := by
      exact norm_fourierPhase_sub_one_le n h
    have h2 : ‖Complex.exp (n * h * Complex.I) - 1‖ ^ 2 ≤ 4 := by
      have h0 := norm_nonneg (Complex.exp (n * h * Complex.I) - 1)
      nlinarith
    gcongr
  have hpt : ∀ j, ∀ n ∈ Finset.Icc (-(N : ℤ)) N, (n : ℝ) ^ 2 * ‖c j n‖ ^ 2 ≤
      π ^ 2 / (4 * h ^ 2) * (‖Complex.exp (n * h * Complex.I) - 1‖ ^ 2 * ‖c j n‖ ^ 2) := by
    intro j n hn
    rw [Finset.mem_Icc] at hn
    have habs : |(n : ℝ) * h| ≤ π := by
      rw [abs_mul, abs_of_pos hhpos, hh]
      have : |(n : ℝ)| ≤ N := by
        rw [abs_le]; exact_mod_cast (by assumption)
      calc |(n : ℝ)| * (π / N) ≤ N * (π / N) := by gcongr
        _ = π := by field_simp
    have hk := sq_le_norm_exp_sub_one_sq habs
    have heq : ((n * h : ℝ) : ℂ) * Complex.I = (n : ℂ) * h * Complex.I := by push_cast; ring
    rw [heq] at hk
    have hpi  := pi_pos
    have key : (n : ℝ) ^ 2 ≤ π ^ 2 / (4 * h ^ 2) * ‖Complex.exp (n * h * Complex.I) - 1‖ ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have : 4 / π ^ 2 * ((n : ℝ) * h) ^ 2 * π ^ 2 = 4 * h ^ 2 * (n : ℝ) ^ 2 := by
        field_simp
      nlinarith
    nlinarith
  calc ∑ j ∈ J, ∑ n ∈ Finset.Icc (-(N : ℤ)) N, n ^ 2 * ‖c j n‖ ^ 2
      ≤ ∑ j ∈ J, ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
          π ^ 2 / (4 * h ^ 2) * (‖Complex.exp (n * h * Complex.I) - 1‖ ^ 2 * ‖c j n‖ ^ 2) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum (hpt j)
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

/-- The Hilbert–Schmidt estimate for an arbitrary finite set of Fourier entries. -/
lemma sum_sq_mul_fourierCoeff_le (u : Finset (ι × ℤ)) :
    ∑ p ∈ u, ((p.2 : ℝ)) ^ 2 *
      ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v p.1⟫_ℂ) p.2‖ ^ 2 ≤ π ^ 2 * K ^ 2 / 4 := by
  classical
  set J : Finset ι := u.image Prod.fst
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ p ∈ u, p.2 ∈ Finset.Icc (-(N : ℤ)) N := by
    refine ⟨(u.image fun p => p.2.natAbs).sup id, fun p hp => ?_⟩
    have : p.2.natAbs ≤ (u.image fun p => p.2.natAbs).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hp)
    grind
  calc ∑ p ∈ u, p.2 ^ 2 * ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v p.1⟫_ℂ) p.2‖ ^ 2
      ≤ ∑ p ∈ J ×ˢ Finset.Icc (-(N : ℤ)) N,
          p.2 ^ 2 * ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v p.1⟫_ℂ) p.2‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p _ _ => by positivity
        grind
    _ = ∑ j ∈ J, ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
          n ^ 2 * ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v j⟫_ℂ) n‖ ^ 2 :=
        Finset.sum_product _ _ _
    _ ≤ π ^ 2 * K ^ 2 / 4 := sum_sq_mul_fourierCoeff_le_of_finite hv hr hper J N

/-- **`H¹` Hilbert–Schmidt estimate for Lipschitz rows.** For a `2π`-periodic `K`-Lipschitz
`r : ℝ → H` and an orthonormal family `(vⱼ)`, the Fourier coefficients `cⱼ(n)` of
`θ ↦ ⟨r(θ), vⱼ⟩` satisfy `∑ⱼ ∑ₙ n² |cⱼ(n)|² < ∞`, with sum at most `π² K² / 4`. -/
theorem summable_sq_mul_fourierCoeff :
    Summable fun p : ι × ℤ =>
      ((p.2 : ℝ)) ^ 2 * ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v p.1⟫_ℂ) p.2‖ ^ 2 :=
  summable_of_sum_le (fun p => by positivity) (sum_sq_mul_fourierCoeff_le hv hr hper)

/-- The value bound: `∑ⱼ ∑ₙ n² |cⱼ(n)|² ≤ π² K² / 4`. -/
theorem tsum_sq_mul_fourierCoeff_le :
    ∑' p : ι × ℤ,
      ((p.2 : ℝ)) ^ 2 * ‖fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v p.1⟫_ℂ) p.2‖ ^ 2 ≤
      π ^ 2 * K ^ 2 / 4 :=
  (summable_sq_mul_fourierCoeff hv hr hper).tsum_le_of_sum_le
    (sum_sq_mul_fourierCoeff_le hv hr hper)

end Rows

end PolyaNeumann
