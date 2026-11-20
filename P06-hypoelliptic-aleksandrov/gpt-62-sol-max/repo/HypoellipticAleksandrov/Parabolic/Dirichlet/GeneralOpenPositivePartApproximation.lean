module

public import PDEFoundation.Measure.LpDominatedConvergence
public import PDEFoundation.Sobolev.H1.LevelSets
public import PDEFoundation.Sobolev.H1.ZeroBoundary
public import PDEFoundation.Sobolev.W1p.Truncation

/-! # Supported positive-part approximation on general open sets -/

@[expose] public section

open scoped ENNReal NNReal Topology

namespace PDE

open Filter MeasureTheory Set

namespace H1Function

variable {d : ℕ} {U : Set (Vec d)} {u : H1Function U}

private theorem hasWeakGradientOn_of_smooth_approximation
    {f : Vec d → ℝ} {Du : Vec d → Vec d}
    {φ : ℕ → Vec d → ℝ}
    (hf : MemL2On U f) (hDu : GradMemL2On U Du)
    (hφSmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n))
    (hφCompact : ∀ n, HasCompactSupport (φ n))
    (hφSupport : ∀ n, tsupport (φ n) ⊆ U)
    (hvalue : Tendsto
      (fun n => eLpNorm (φ n - f) (2 : ℝ≥0∞) (volumeOn U)) atTop (𝓝 0))
    (hgrad : ∀ i, Tendsto
      (fun n => eLpNorm
        (fun x => (fderiv ℝ (φ n) x) (basisVec i) - Du x i)
        (2 : ℝ≥0∞) (volumeOn U)) atTop (𝓝 0)) :
    HasWeakGradientOn U f Du := by
  apply HasWeakGradientOn.of_tendsto_eLpNorm
    (uSeq := φ)
    (DuSeq := fun n x i => (fderiv ℝ (φ n) x) (basisVec i)) hf hDu
  · intro n
    exact (WeakTestFunction.mk (φ n) (hφSmooth n) (hφCompact n)
      (hφSupport n)).memLp_toFun 2
  · intro n i
    exact (WeakTestFunction.mk (φ n) (hφSmooth n) (hφCompact n)
      (hφSupport n)).memLp_partialDeriv i 2
  · intro n
    exact HasWeakGradientOn.of_contDiff ((hφSmooth n).of_le (by norm_num))
  · exact hvalue
  · exact hgrad

private theorem exists_shifted_regularization_scale
    (φ : Vec d → ℝ) (hφCompact : HasCompactSupport φ)
    (hφMeas : AEStronglyMeasurable φ (volumeOn U))
    (k : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧
      eLpNorm
          (fun x => smoothPositivePartApprox (k : ℝ) δ (φ x) -
            max (φ x - (k : ℝ)) 0)
          (2 : ℝ≥0∞) (volumeOn U) ≤ ENNReal.ofReal ε := by
  let δSeq : ℕ → ℝ := fun n => 1 / (n + 1)
  let err : ℕ → Vec d → ℝ := fun n x =>
    smoothPositivePartApprox (k : ℝ) (δSeq n) (φ x) -
      max (φ x - (k : ℝ)) 0
  have hδPos : ∀ n, 0 < δSeq n := by
    intro n
    dsimp only [δSeq]
    positivity
  have hδTendsto : Tendsto δSeq atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have herrBound : ∀ n,
      eLpNorm (err n) (2 : ℝ≥0∞) (volumeOn U) ≤
        ENNReal.ofReal (2 * δSeq n) *
          (volumeOn U) (tsupport φ) ^ (1 / (2 : ℝ)) := by
    intro n
    apply eLpNorm_sub_le_of_dist_bdd (μ := volumeOn U)
      (p := (2 : ℝ≥0∞)) (by norm_num)
      isClosed_closure.measurableSet.nullMeasurableSet (mul_nonneg (by norm_num) (hδPos n).le)
    · exact ((smoothPositivePartApprox_contDiff (k : ℝ) (δSeq n)).continuous
        |>.comp_aestronglyMeasurable hφMeas).sub
        (((continuous_id.sub continuous_const).max continuous_const)
          |>.comp_aestronglyMeasurable hφMeas)
    · intro x
      rw [Real.dist_eq]
      simpa only [sub_zero] using
        abs_smoothPositivePartApprox_sub_le (c := (k : ℝ)) (hδPos n) (φ x)
    · exact (Function.support_comp_subset
        (smoothPositivePartApprox_eq_zero_of_le (hδPos n) k.2) φ).trans
        subset_closure
    · intro x hx
      by_contra hxt
      have hzero : φ x = 0 := image_eq_zero_of_notMem_tsupport hxt
      have hmax : max ((0 : ℝ) - (k : ℝ)) 0 = 0 := max_eq_right (sub_nonpos.mpr k.2)
      simp only [Function.mem_support, hzero] at hx
      exact hx hmax
  have hconv : Tendsto
      (fun n => eLpNorm (err n) (2 : ℝ≥0∞) (volumeOn U))
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds ?_ (fun n => zero_le') herrBound
    have hfinite : (volumeOn U) (tsupport φ) ^ (1 / (2 : ℝ)) ≠ ∞ := by
      exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (hφCompact.measure_lt_top.ne)
    have hofReal : Tendsto (fun n => ENNReal.ofReal (2 * δSeq n)) atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero, mul_zero] using
        ENNReal.tendsto_ofReal (hδTendsto.const_mul (2 : ℝ))
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const hofReal (Or.inr hfinite)
  have heventNorm : ∀ᶠ n in atTop,
      eLpNorm (err n) (2 : ℝ≥0∞) (volumeOn U) ≤ ENNReal.ofReal ε :=
    ((tendsto_order.1 hconv).2 _ (ENNReal.ofReal_pos.2 hε)).mono fun _ => le_of_lt
  have heventScale : ∀ᶠ n in atTop, δSeq n ≤ ε :=
    ((tendsto_order.1 hδTendsto).2 _ hε).mono fun _ => le_of_lt
  obtain ⟨n, hnNorm, hnScale⟩ := (heventNorm.and heventScale).exists
  exact ⟨δSeq n, hδPos n, hnScale, hnNorm⟩

private theorem memLp_max_sub_nonneg
    {w : Vec d → ℝ} (hw : MemLp w (2 : ℝ≥0∞) (volumeOn U))
    (k : ℝ≥0) :
    MemLp (fun x => max (w x - (k : ℝ)) 0) (2 : ℝ≥0∞) (volumeOn U) := by
  refine MemLp.of_le hw ?_ ?_
  · exact ((continuous_id.sub continuous_const).max continuous_const)
      |>.comp_aestronglyMeasurable hw.aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rcases le_total (w x) (k : ℝ) with hx | hx
    · rw [max_eq_right (sub_nonpos.mpr hx), abs_zero]
      exact abs_nonneg _
    · rw [max_eq_left (sub_nonneg.mpr hx), abs_of_nonneg (sub_nonneg.mpr hx), abs_of_nonneg (k.2.trans hx)]
      exact sub_le_self _ k.2

private theorem fderiv_shifted_smooth_comp_basisVec
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (k : ℝ≥0) {δ : ℝ} (x : Vec d) (i : Fin d) :
    (fderiv ℝ (fun y => smoothPositivePartApprox (k : ℝ) δ (φ y)) x)
        (basisVec i) =
      smoothPositivePartStep (k : ℝ) δ (φ x) *
        (fderiv ℝ φ x) (basisVec i) := by
  simpa only [deriv_smoothPositivePartApprox] using
    fderiv_comp_basisVec
      ((smoothPositivePartApprox_contDiff (k : ℝ) δ).differentiable
        (by simp)).differentiableAt
      (hφ.differentiable (by simp)).differentiableAt

private theorem shifted_gradient_error_decomposition
    (s a g D : ℝ) :
    s * a - D = s * (a - g) + (s * g - D) := by
  ring

private theorem tendsto_shifted_smooth_value
    {u : H1Function U} {φ : ℕ → Vec d → ℝ}
    (hφMeas : ∀ n, AEStronglyMeasurable (φ n) (volumeOn U))
    (hφ : Tendsto
      (fun n => eLpNorm (φ n - u.toFun) (2 : ℝ≥0∞) (volumeOn U))
      atTop (𝓝 0))
    (k : ℝ≥0) {δ : ℕ → ℝ}
    (hreg : Tendsto
      (fun n => eLpNorm
        (fun x => smoothPositivePartApprox (k : ℝ) (δ n) (φ n x) -
          max (φ n x - (k : ℝ)) 0)
        (2 : ℝ≥0∞) (volumeOn U)) atTop (𝓝 0)) :
    Tendsto
      (fun n => eLpNorm
        (fun x => smoothPositivePartApprox (k : ℝ) (δ n) (φ n x) -
          max (u.toFun x - (k : ℝ)) 0)
        (2 : ℝ≥0∞) (volumeOn U)) atTop (𝓝 0) := by
  let reg : ℕ → Vec d → ℝ := fun n x =>
    smoothPositivePartApprox (k : ℝ) (δ n) (φ n x) -
      max (φ n x - (k : ℝ)) 0
  let lip : ℕ → Vec d → ℝ := fun n x =>
    max (φ n x - (k : ℝ)) 0 - max (u.toFun x - (k : ℝ)) 0
  have hlipMeas : ∀ n, AEStronglyMeasurable (lip n) (volumeOn U) := by
    intro n
    exact (((continuous_id.sub continuous_const).max continuous_const)
      |>.comp_aestronglyMeasurable (hφMeas n)).sub
      (((continuous_id.sub continuous_const).max continuous_const)
        |>.comp_aestronglyMeasurable u.memL2.aestronglyMeasurable)
  have hlipBound : ∀ n,
      eLpNorm (lip n) (2 : ℝ≥0∞) (volumeOn U) ≤
        eLpNorm (φ n - u.toFun) (2 : ℝ≥0∞) (volumeOn U) := by
    intro n
    apply eLpNorm_mono_ae (hlipMeas n)
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    simpa only [lip, Pi.sub_apply, sub_sub_sub_cancel_right] using
      abs_max_sub_max_le_abs (φ n x - (k : ℝ))
        (u.toFun x - (k : ℝ)) 0
  have hlip : Tendsto
      (fun n => eLpNorm (lip n) (2 : ℝ≥0∞) (volumeOn U))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hφ
      (fun _ => zero_le') hlipBound
  have hsum : Tendsto
      (fun n => eLpNorm (reg n) (2 : ℝ≥0∞) (volumeOn U) +
        eLpNorm (lip n) (2 : ℝ≥0∞) (volumeOn U)) atTop (𝓝 0) := by
    simpa only [zero_add] using hreg.add hlip
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le') (fun n => ?_)
  have hdecomp :
      (fun x => smoothPositivePartApprox (k : ℝ) (δ n) (φ n x) -
        max (u.toFun x - (k : ℝ)) 0) = reg n + lip n := by
    funext x
    simp only [reg, lip, Pi.add_apply]
    ring
  rw [hdecomp]
  exact eLpNorm_add_le (by norm_num)

private theorem tendsto_shifted_smooth_gradient
    {φ : ℕ → Vec d → ℝ} (hφSmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n))
    (k : ℝ≥0) {δ : ℕ → ℝ} {g D : Vec d → Vec d}
    (hfirstMeas : ∀ i n, AEStronglyMeasurable
      (fun x => smoothPositivePartStep (k : ℝ) (δ n) (φ n x) *
        ((fderiv ℝ (φ n) x) (basisVec i) - g x i)) (volumeOn U))
    (hsecondMeas : ∀ i n, AEStronglyMeasurable
      (fun x => smoothPositivePartStep (k : ℝ) (δ n) (φ n x) * g x i - D x i)
      (volumeOn U))
    (hfirst : ∀ i, Tendsto (fun n => eLpNorm
      (fun x => smoothPositivePartStep (k : ℝ) (δ n) (φ n x) *
        ((fderiv ℝ (φ n) x) (basisVec i) - g x i))
      (2 : ℝ≥0∞) (volumeOn U)) atTop (𝓝 0))
    (hsecond : ∀ i, Tendsto (fun n => eLpNorm
      (fun x => smoothPositivePartStep (k : ℝ) (δ n) (φ n x) * g x i - D x i)
      (2 : ℝ≥0∞) (volumeOn U)) atTop (𝓝 0)) :
    ∀ i, Tendsto (fun n => eLpNorm
      (fun x => (fderiv ℝ
        (fun y => smoothPositivePartApprox (k : ℝ) (δ n) (φ n y)) x)
          (basisVec i) - D x i)
      (2 : ℝ≥0∞) (volumeOn U)) atTop (𝓝 0) := by
  intro i
  have hsum : Tendsto (fun n =>
      eLpNorm
        (fun x => smoothPositivePartStep (k : ℝ) (δ n) (φ n x) *
          ((fderiv ℝ (φ n) x) (basisVec i) - g x i))
        (2 : ℝ≥0∞) (volumeOn U) +
      eLpNorm
        (fun x => smoothPositivePartStep (k : ℝ) (δ n) (φ n x) * g x i - D x i)
        (2 : ℝ≥0∞) (volumeOn U)) atTop (𝓝 0) := by
    simpa only [zero_add] using (hfirst i).add (hsecond i)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le') (fun n => ?_)
  let first : Vec d → ℝ := fun x =>
    smoothPositivePartStep (k : ℝ) (δ n) (φ n x) *
      ((fderiv ℝ (φ n) x) (basisVec i) - g x i)
  let second : Vec d → ℝ := fun x =>
    smoothPositivePartStep (k : ℝ) (δ n) (φ n x) * g x i - D x i
  have hdecomp :
      (fun x => (fderiv ℝ
        (fun y => smoothPositivePartApprox (k : ℝ) (δ n) (φ n y)) x)
          (basisVec i) - D x i) = first + second := by
    funext x
    rw [fderiv_shifted_smooth_comp_basisVec (hφSmooth n) k x i]
    simp only [first, second, Pi.add_apply]
    exact shifted_gradient_error_decomposition _ _ _ _
  rw [hdecomp]
  exact eLpNorm_add_le (by norm_num)

section
variable {f : ℕ → Vec d → ℝ}

private theorem tendsto_shifted_step_mul_sub_indicator {f₀ : Vec d → ℝ}
    {g : Vec d → ℝ} {x : Vec d} (k : ℝ≥0)
    {δ : ℕ → ℝ} (hδPos : ∀ n, 0 < δ n)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hf : Tendsto (fun n => f n x) atTop (𝓝 (f₀ x)))
    (hzero : f₀ x = (k : ℝ) → g x = 0) :
    Tendsto (fun n =>
      smoothPositivePartStep (k : ℝ) (δ n) (f n x) * g x -
        (if (k : ℝ) < f₀ x then g x else 0)) atTop (𝓝 0) := by
  rcases lt_trichotomy (f₀ x) (k : ℝ) with hlt | heq | hgt
  · have hevent : ∀ᶠ n in atTop, f n x < (f₀ x + (k : ℝ)) / 2 :=
      (tendsto_order.1 hf).2 _ (by linarith)
    have hstep : ∀ᶠ n in atTop,
        smoothPositivePartStep (k : ℝ) (δ n) (f n x) = 0 := by
      filter_upwards [hevent] with n hn
      exact smoothPositivePartStep_eq_zero (hδPos n) (by
        linarith [(hδPos n).le])
    apply (tendsto_congr' (hstep.mono fun n hn => ?_)).2 tendsto_const_nhds
    simp only [if_neg hlt.not_gt, hn, zero_mul, sub_zero]
  · have hg : g x = 0 := hzero heq
    have hfun : (fun n =>
        smoothPositivePartStep (k : ℝ) (δ n) (f n x) * g x -
          (if (k : ℝ) < f₀ x then g x else 0)) = fun _ : ℕ => (0 : ℝ) := by
      funext n
      rw [hg]
      split <;> simp
    rw [hfun]
    exact tendsto_const_nhds
  · have hfLarge : ∀ᶠ n in atTop, (f₀ x + (k : ℝ)) / 2 < f n x :=
      (tendsto_order.1 hf).1 _ (by linarith)
    have hδSmall : ∀ᶠ n in atTop, δ n < (f₀ x - (k : ℝ)) / 4 :=
      (tendsto_order.1 hδ).2 _ (by linarith)
    have hone : ∀ᶠ n in atTop,
        smoothPositivePartStep (k : ℝ) (δ n) (f n x) = 1 := by
      filter_upwards [hfLarge, hδSmall] with n hn hdn
      exact smoothPositivePartStep_eq_one (hδPos n) (by linarith)
    apply (tendsto_congr' (hone.mono fun n hn => ?_)).2 tendsto_const_nhds
    simp only [if_pos hgt, hn, one_mul, sub_self]

private theorem tendsto_shifted_step_indicator_eLpNorm {f₀ g : Vec d → ℝ}
    (hfMeas : ∀ n, AEStronglyMeasurable (f n) (volumeOn U))
    (hf₀Meas : AEStronglyMeasurable f₀ (volumeOn U))
    (hgMem : MemLp g (2 : ℝ≥0∞) (volumeOn U))
    (k : ℝ≥0) {δ : ℕ → ℝ} (hδPos : ∀ n, 0 < δ n)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hf : ∀ᵐ x ∂(volumeOn U),
      Tendsto (fun n => f n x) atTop (𝓝 (f₀ x)))
    (hlevel : ∀ᵐ x ∂(volumeOn U), f₀ x = (k : ℝ) → g x = 0) :
    Tendsto (fun n => eLpNorm
      (fun x => smoothPositivePartStep (k : ℝ) (δ n) (f n x) * g x -
        {y | (k : ℝ) < f₀ y}.indicator g x)
      (2 : ℝ≥0∞) (volumeOn U)) atTop (𝓝 0) := by
  apply tendsto_eLpNorm_two_zero_of_ae_dominated
    (bound := fun x => (2 : ℝ) * g x)
  · intro n
    apply AEStronglyMeasurable.sub
    · exact ((smoothPositivePartStep_continuous (k : ℝ) (δ n))
        |>.comp_aestronglyMeasurable (hfMeas n)).mul hgMem.aestronglyMeasurable
    · rw [aestronglyMeasurable_indicator_iff₀
      (nullMeasurableSet_lt aemeasurable_const hf₀Meas.aemeasurable)]
      exact hgMem.aestronglyMeasurable.restrict
  · exact hgMem.const_mul 2
  · intro n
    filter_upwards with x
    simp only [indicator_apply, Real.norm_eq_abs, norm_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    split_ifs
    · have hmul :
          |smoothPositivePartStep (k : ℝ) (δ n) (f n x) * g x| ≤ |g x| := by
        rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _)
          (abs_smoothPositivePartStep_le_one _ _ _)
      calc
        |smoothPositivePartStep (k : ℝ) (δ n) (f n x) * g x - g x| ≤
            |smoothPositivePartStep (k : ℝ) (δ n) (f n x) * g x| + |g x| :=
          abs_sub _ _
        _ ≤ |g x| + |g x| := add_le_add hmul le_rfl
        _ = 2 * |g x| := by ring
    · rw [sub_zero, abs_mul]
      calc
        |smoothPositivePartStep (k : ℝ) (δ n) (f n x)| * |g x| ≤ |g x| :=
          mul_le_of_le_one_left (abs_nonneg _) (abs_smoothPositivePartStep_le_one _ _ _)
        _ ≤ 2 * |g x| := by nlinarith [abs_nonneg (g x)]
  · filter_upwards [hf, hlevel] with x hfx hlx
    simpa only [indicator_apply, Set.mem_setOf_eq] using
      tendsto_shifted_step_mul_sub_indicator k hδPos hδ hfx hlx

end

/-- Shifted positive parts retain a supported, nonnegative smooth approximation.
The nonnegative shift ensures that the truncation sends zero to zero. -/
theorem exists_shiftedPositivePart_nonnegative_supportedSmoothApproximation
    (w : H1Function U) (happrox : w.SupportedSmoothApproximation)
    (k : ℝ≥0) (hlevel : ∀ᵐ x ∂volumeOn U, w.toFun x = (k : ℝ) → w.grad x = 0) :
    ∃ z : H1Function U,
      z.toFun = (fun x => max (w.toFun x - (k : ℝ)) 0) ∧
      z.grad = {x | (k : ℝ) < w.toFun x}.indicator w.grad ∧
      ∃ hz : z.SupportedSmoothApproximation, ∀ n x, 0 ≤ hz.approx n x := by
  have happroxMeas : ∀ n,
      AEStronglyMeasurable (happrox.approx n) (volumeOn U) := by
    intro n
    exact (happrox.toWeakTestFunction n).memLp_toFun
      (2 : ℝ≥0∞) |>.aestronglyMeasurable
  obtain ⟨σ, hσStrictMono, hσAeRaw⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      happrox.tendsto_value).exists_seq_tendsto_ae
  have hσAe : ∀ᵐ x ∂(volumeOn U),
      Tendsto (fun n => happrox.approx (σ n) x) atTop (nhds (w.toFun x)) := by
    simpa only [H1Function.toW1pFunction_toFun] using hσAeRaw
  let ε : ℕ → ℝ := fun n => 1 / (n + 1)
  have hεPos : ∀ n, 0 < ε n := by
    intro n
    dsimp only [ε]
    positivity
  have hεTendsto : Tendsto ε atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hscale : ∀ n, ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε n ∧
      eLpNorm
        (fun x => smoothPositivePartApprox (k : ℝ) δ
            (happrox.approx (σ n) x) -
          max (happrox.approx (σ n) x - (k : ℝ)) 0)
        (2 : ℝ≥0∞) (volumeOn U) ≤ ENNReal.ofReal (ε n) := by
    intro n
    exact exists_shifted_regularization_scale
      (happrox.approx (σ n))
      (happrox.approx_hasCompactSupport (σ n)) (happroxMeas (σ n)) k (ε n) (hεPos n)
  let δ : ℕ → ℝ := fun n => Classical.choose (hscale n)
  have hδPos : ∀ n, 0 < δ n := fun n => (Classical.choose_spec (hscale n)).1
  have hδLe : ∀ n, δ n ≤ ε n := fun n => (Classical.choose_spec (hscale n)).2.1
  have hδTendsto : Tendsto δ atTop (nhds 0) :=
    squeeze_zero (fun n => (hδPos n).le) hδLe hεTendsto
  let shiftedApprox : ℕ → Vec d → ℝ := fun n x =>
    smoothPositivePartApprox (k : ℝ) (δ n) (happrox.approx (σ n) x)
  have hsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (shiftedApprox n) := by
    intro n
    exact (smoothPositivePartApprox_contDiff (k : ℝ) (δ n)).comp
      (happrox.approx_smooth (σ n))
  have hcompact : ∀ n, HasCompactSupport (shiftedApprox n) := by
    intro n
    change HasCompactSupport
      ((fun s => smoothPositivePartApprox (k : ℝ) (δ n) s) ∘
        happrox.approx (σ n))
    have hzero : smoothPositivePartApprox (k : ℝ) (δ n) 0 = 0 :=
      smoothPositivePartApprox_eq_zero_of_le (hδPos n) k.2
    exact @HasCompactSupport.comp_left _ ℝ ℝ _ _ _ _ _
      (happrox.approx_hasCompactSupport (σ n)) hzero
  have hsupport : ∀ n, tsupport (shiftedApprox n) ⊆ U := by
    intro n
    refine (closure_mono (Function.support_comp_subset
      (smoothPositivePartApprox_eq_zero_of_le (hδPos n) k.2)
      (happrox.approx (σ n)))).trans ?_
    exact happrox.approx_tsupport_subset (σ n)
  have hreg : Tendsto (fun n => eLpNorm
      (fun x => smoothPositivePartApprox (k : ℝ) (δ n)
          (happrox.approx (σ n) x) -
        max (happrox.approx (σ n) x - (k : ℝ)) 0)
      (2 : ℝ≥0∞) (volumeOn U)) atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun n => ENNReal.ofReal (ε n)) atTop (nhds 0) from ?_)
      (fun _ => zero_le') (fun n => (Classical.choose_spec (hscale n)).2.2)
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hεTendsto
  have hvalue : Tendsto (fun n => eLpNorm
      (fun x => shiftedApprox n x - max (w.toFun x - (k : ℝ)) 0)
      (2 : ℝ≥0∞) (volumeOn U)) atTop (nhds 0) := by
    apply tendsto_shifted_smooth_value
      (fun n => happroxMeas (σ n))
      (happrox.tendsto_value.comp hσStrictMono.tendsto_atTop) k
    simpa only [shiftedApprox] using hreg
  let g := w.grad
  let D : Vec d → Vec d := fun x =>
    {y | (k : ℝ) < w.toFun y}.indicator g x
  have hDCoord : ∀ x i, D x i =
      {y | (k : ℝ) < w.toFun y}.indicator (fun y => g y i) x := by
    intro x i
    simp only [D, indicator_apply]
    split <;> rfl
  have hgMem : GradMemL2On U g := w.gradMemL2
  have hDMem : GradMemL2On U D := by
    intro i
    rw [show (fun x => D x i) =
        {y | (k : ℝ) < w.toFun y}.indicator (fun y => g y i) by
      funext x; exact hDCoord x i]
    refine MemLp.of_le (hgMem i) ?_ ?_
    · exact (hgMem i).aestronglyMeasurable.indicator₀
        (nullMeasurableSet_lt aemeasurable_const
          w.memL2.aestronglyMeasurable.aemeasurable)
    · filter_upwards with x
      simp only [indicator_apply]
      split <;> simp
  have hfirstMeas : ∀ i n, AEStronglyMeasurable
      (fun x => smoothPositivePartStep (k : ℝ) (δ n)
        (happrox.approx (σ n) x) *
          ((fderiv ℝ (happrox.approx (σ n)) x) (basisVec i) - g x i))
      (volumeOn U) := by
    intro i n
    exact ((smoothPositivePartStep_continuous (k : ℝ) (δ n))
      |>.comp_aestronglyMeasurable (happroxMeas (σ n))).mul
      (((happrox.toWeakTestFunction (σ n)).memLp_partialDeriv i 2).aestronglyMeasurable.sub
        (hgMem i).aestronglyMeasurable)
  have hfirst : ∀ i, Tendsto (fun n => eLpNorm
      (fun x => smoothPositivePartStep (k : ℝ) (δ n)
        (happrox.approx (σ n) x) *
          ((fderiv ℝ (happrox.approx (σ n)) x) (basisVec i) - g x i))
      (2 : ℝ≥0∞) (volumeOn U)) atTop (nhds 0) := by
    intro i
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (happrox.tendsto_grad i |>.comp hσStrictMono.tendsto_atTop)
      (fun _ => zero_le') (fun n => ?_)
    apply eLpNorm_mono_ae (hfirstMeas i n)
    filter_upwards with x
    simp only [norm_mul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (abs_nonneg _)
      (abs_smoothPositivePartStep_le_one _ _ _)
  have hsecondMeas : ∀ i n, AEStronglyMeasurable
      (fun x => smoothPositivePartStep (k : ℝ) (δ n)
        (happrox.approx (σ n) x) * g x i - D x i) (volumeOn U) := by
    intro i n
    exact (((smoothPositivePartStep_continuous (k : ℝ) (δ n))
      |>.comp_aestronglyMeasurable (happroxMeas (σ n))).mul
      (hgMem i).aestronglyMeasurable).sub (hDMem i).aestronglyMeasurable
  have hsecond : ∀ i, Tendsto (fun n => eLpNorm
      (fun x => smoothPositivePartStep (k : ℝ) (δ n)
        (happrox.approx (σ n) x) * g x i - D x i)
      (2 : ℝ≥0∞) (volumeOn U)) atTop (nhds 0) := by
    intro i
    have ht := tendsto_shifted_step_indicator_eLpNorm
      (fun n => happroxMeas (σ n)) w.memL2.aestronglyMeasurable
      (hgMem i) k hδPos hδTendsto hσAe
      (by
        filter_upwards [hlevel] with x hx
        intro hval
        change w.grad x i = 0
        rw [hx hval]
        rfl)
    simpa only [hDCoord] using ht
  have hgrad : ∀ i, Tendsto (fun n => eLpNorm
      (fun x => (fderiv ℝ (shiftedApprox n) x) (basisVec i) - D x i)
      (2 : ℝ≥0∞) (volumeOn U)) atTop (nhds 0) := by
    simpa only [shiftedApprox] using tendsto_shifted_smooth_gradient
      (fun n => happrox.approx_smooth (σ n)) k hfirstMeas hsecondMeas hfirst hsecond
  have hfMem : MemL2On U (fun x => max (w.toFun x - (k : ℝ)) 0) :=
    memLp_max_sub_nonneg w.memL2 k
  have hweak : HasWeakGradientOn U
      (fun x => max (w.toFun x - (k : ℝ)) 0) D :=
    hasWeakGradientOn_of_smooth_approximation hfMem hDMem hsmooth hcompact hsupport
      (by simpa only [shiftedApprox, Pi.sub_def] using hvalue) hgrad
  let z : H1Function U :=
    { toFun := fun x => max (w.toFun x - (k : ℝ)) 0
      grad := D
      memL2 := hfMem
      gradMemL2 := hDMem
      hasWeakGradient := hweak }
  refine ⟨z, rfl, rfl, ?_⟩
  let hz : z.SupportedSmoothApproximation :=
    { approx := shiftedApprox
      approx_smooth := hsmooth
      approx_hasCompactSupport := hcompact
      approx_tsupport_subset := hsupport
      tendsto_value := by simpa only [z, H1Function.toW1pFunction, Pi.sub_def] using hvalue
      tendsto_grad := by simpa only [z, H1Function.toW1pFunction] using hgrad }
  exact ⟨hz, fun n x => smoothPositivePartApprox_nonneg (hδPos n) _⟩

end H1Function

end PDE
