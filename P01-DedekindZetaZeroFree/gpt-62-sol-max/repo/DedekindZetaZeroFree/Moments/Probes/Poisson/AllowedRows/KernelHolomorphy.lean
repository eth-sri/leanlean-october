module

public import DedekindZetaZeroFree.Analysis.GaussianWeightConvolution
public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.Height
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.AnalyticContinuation
public import DedekindZetaZeroFree.Analysis.Integration.HolomorphicDominatedIntegral
public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.SubpowerBounds

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RowKernelHolomorphy

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory DedekindZetaZeroFree.Quantitative.PoissonKernel
  DedekindZetaZeroFree.Quantitative.DetectorHeight

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

private lemma exp_shift (x₀ δ r : ℝ) (h : |δ| ≤ r) :
    Real.exp (-(x₀ + δ) ^ 2) ≤
      Real.exp (r ^ 2) * (Real.exp (-(x₀ - r) ^ 2) + Real.exp (-(x₀ + r) ^ 2)) := by
  have h1 := abs_le.1 h
  rcases le_total 0 x₀ with hx | hx
  · have : -(x₀ + δ) ^ 2 ≤ r ^ 2 + -(x₀ - r) ^ 2 := by
      nlinarith [mul_nonneg hx (show 0 ≤ δ + r by linarith [h1.1]), sq_nonneg δ]
    calc Real.exp (-(x₀ + δ) ^ 2) ≤ Real.exp (r ^ 2 + -(x₀ - r) ^ 2) := Real.exp_le_exp.2 this
      _ = Real.exp (r ^ 2) * Real.exp (-(x₀ - r) ^ 2) := Real.exp_add _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (Real.exp_pos _).le) (Real.exp_pos _).le
  · have : -(x₀ + δ) ^ 2 ≤ r ^ 2 + -(x₀ + r) ^ 2 := by
      nlinarith [mul_nonneg (neg_nonneg.2 hx) (show 0 ≤ r - δ by linarith [h1.2]), sq_nonneg δ]
    calc Real.exp (-(x₀ + δ) ^ 2) ≤ Real.exp (r ^ 2 + -(x₀ + r) ^ 2) := Real.exp_le_exp.2 this
      _ = Real.exp (r ^ 2) * Real.exp (-(x₀ + r) ^ 2) := Real.exp_add _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (Real.exp_pos _).le) (Real.exp_pos _).le

private lemma pt_env (X X₀ a a₀ r' v s t1 t2 k : ℝ) (m w : ℂ) (hk : 0 ≤ k) (hr0 : 0 < r')
    (hr1 : r' ≤ 1) (hX : |X - X₀| ≤ 1) (ha : |a - a₀| ≤ r') :
    Real.exp ((X + v - 1) ^ 2 - (a + s) ^ 2) * ‖m‖ * ‖w‖ * (2 + |t1| + |t2| + |a|) ^ k ≤
      Real.exp ((|X₀| + |v| + 2) ^ 2 + 1) * 2 ^ k *
        (Real.exp ((X₀ + v - 1) ^ 2 - (a₀ + r' + s) ^ 2) * ‖m‖ * ‖w‖ *
            (2 + |t1| + |t2| + |a₀ + r'|) ^ k +
         Real.exp ((X₀ + v - 1) ^ 2 - (a₀ - r' + s) ^ 2) * ‖m‖ * ‖w‖ *
            (2 + |t1| + |t2| + |a₀ - r'|) ^ k) := by
  have ha' := abs_le.1 ha
  have hq : (X + v - 1) ^ 2 ≤ (|X₀| + |v| + 2) ^ 2 := by
    have h1 := abs_le.1 hX
    have h2 := neg_abs_le X₀
    have h3 := le_abs_self X₀
    have h4 := neg_abs_le v
    have h5 := le_abs_self v
    exact sq_le_sq' (by linarith) (by linarith)
  have hshift := exp_shift (a₀ + s) (a - a₀) r' ha
  have e1 : (a₀ + s) + (a - a₀) = a + s := by ring
  rw [e1] at hshift
  have hA : Real.exp (-((a₀ + s) - r') ^ 2) ≤ Real.exp ((X₀ + v - 1) ^ 2 - (a₀ - r' + s) ^ 2) :=
    Real.exp_le_exp.2 (by nlinarith [sq_nonneg (X₀ + v - 1)])
  have hB : Real.exp (-((a₀ + s) + r') ^ 2) ≤ Real.exp ((X₀ + v - 1) ^ 2 - (a₀ + r' + s) ^ 2) :=
    Real.exp_le_exp.2 (by nlinarith [sq_nonneg (X₀ + v - 1)])
  have hexp_r : Real.exp (r' ^ 2) ≤ Real.exp 1 := Real.exp_le_exp.2 (by nlinarith)
  have h1 : Real.exp ((X + v - 1) ^ 2 - (a + s) ^ 2) ≤
      Real.exp ((|X₀| + |v| + 2) ^ 2 + 1) *
        (Real.exp ((X₀ + v - 1) ^ 2 - (a₀ + r' + s) ^ 2) +
          Real.exp ((X₀ + v - 1) ^ 2 - (a₀ - r' + s) ^ 2)) := by
    have hsum : Real.exp (-((a₀ + s) - r') ^ 2) + Real.exp (-((a₀ + s) + r') ^ 2) ≤
        Real.exp ((X₀ + v - 1) ^ 2 - (a₀ + r' + s) ^ 2) +
          Real.exp ((X₀ + v - 1) ^ 2 - (a₀ - r' + s) ^ 2) := by linarith
    calc Real.exp ((X + v - 1) ^ 2 - (a + s) ^ 2)
        = Real.exp ((X + v - 1) ^ 2) * Real.exp (-(a + s) ^ 2) := by
          rw [sub_eq_add_neg, Real.exp_add]
      _ ≤ Real.exp ((|X₀| + |v| + 2) ^ 2) * (Real.exp (r' ^ 2) *
            (Real.exp (-((a₀ + s) - r') ^ 2) + Real.exp (-((a₀ + s) + r') ^ 2))) :=
          mul_le_mul (Real.exp_le_exp.2 hq) hshift (Real.exp_pos _).le (Real.exp_pos _).le
      _ ≤ Real.exp ((|X₀| + |v| + 2) ^ 2) * (Real.exp (r' ^ 2) *
            (Real.exp ((X₀ + v - 1) ^ 2 - (a₀ + r' + s) ^ 2) +
              Real.exp ((X₀ + v - 1) ^ 2 - (a₀ - r' + s) ^ 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le)
            (Real.exp_pos _).le
      _ ≤ Real.exp ((|X₀| + |v| + 2) ^ 2) * (Real.exp 1 *
            (Real.exp ((X₀ + v - 1) ^ 2 - (a₀ + r' + s) ^ 2) +
              Real.exp ((X₀ + v - 1) ^ 2 - (a₀ - r' + s) ^ 2))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hexp_r
              (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)) (Real.exp_pos _).le
      _ = _ := by rw [Real.exp_add]; ring
  have hPP : (2 + |t1| + |t2| + |a|) ^ k ≤ 2 ^ k * (2 + |t1| + |t2| + |a₀ + r'|) ^ k := by
    have hle : 2 + |t1| + |t2| + |a| ≤ 2 * (2 + |t1| + |t2| + |a₀ + r'|) := by
      have : |a| ≤ |a₀ + r'| + 2 :=
        abs_le.2 ⟨by linarith [neg_le_abs (a₀ + r')], by linarith [le_abs_self (a₀ + r')]⟩
      linarith [abs_nonneg t1, abs_nonneg t2, abs_nonneg (a₀ + r')]
    calc (2 + |t1| + |t2| + |a|) ^ k ≤ (2 * (2 + |t1| + |t2| + |a₀ + r'|)) ^ k :=
          Real.rpow_le_rpow (by positivity) hle hk
      _ = 2 ^ k * (2 + |t1| + |t2| + |a₀ + r'|) ^ k := Real.mul_rpow (by norm_num) (by positivity)
  have hPM : (2 + |t1| + |t2| + |a|) ^ k ≤ 2 ^ k * (2 + |t1| + |t2| + |a₀ - r'|) ^ k := by
    have hle : 2 + |t1| + |t2| + |a| ≤ 2 * (2 + |t1| + |t2| + |a₀ - r'|) := by
      have : |a| ≤ |a₀ - r'| + 2 :=
        abs_le.2 ⟨by linarith [neg_le_abs (a₀ - r')], by linarith [le_abs_self (a₀ - r')]⟩
      linarith [abs_nonneg t1, abs_nonneg t2, abs_nonneg (a₀ - r')]
    calc (2 + |t1| + |t2| + |a|) ^ k ≤ (2 * (2 + |t1| + |t2| + |a₀ - r'|)) ^ k :=
          Real.rpow_le_rpow (by positivity) hle hk
      _ = 2 ^ k * (2 + |t1| + |t2| + |a₀ - r'|) ^ k := Real.mul_rpow (by norm_num) (by positivity)
  have hK : 0 ≤ ‖m‖ * ‖w‖ := by positivity
  have heP : 0 ≤ Real.exp ((X₀ + v - 1) ^ 2 - (a₀ + r' + s) ^ 2) := (Real.exp_pos _).le
  have heM : 0 ≤ Real.exp ((X₀ + v - 1) ^ 2 - (a₀ - r' + s) ^ 2) := (Real.exp_pos _).le
  have hE : 0 ≤ Real.exp ((|X₀| + |v| + 2) ^ 2 + 1) := (Real.exp_pos _).le
  have a1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPP hK) heP
  have a2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPM hK) heM
  have hKP : 0 ≤ ‖m‖ * ‖w‖ * (2 + |t1| + |t2| + |a|) ^ k := by positivity
  calc Real.exp ((X + v - 1) ^ 2 - (a + s) ^ 2) * ‖m‖ * ‖w‖ * (2 + |t1| + |t2| + |a|) ^ k
      = Real.exp ((X + v - 1) ^ 2 - (a + s) ^ 2) *
          (‖m‖ * ‖w‖ * (2 + |t1| + |t2| + |a|) ^ k) := by ring
    _ ≤ (Real.exp ((|X₀| + |v| + 2) ^ 2 + 1) *
        (Real.exp ((X₀ + v - 1) ^ 2 - (a₀ + r' + s) ^ 2) +
          Real.exp ((X₀ + v - 1) ^ 2 - (a₀ - r' + s) ^ 2))) *
          (‖m‖ * ‖w‖ * (2 + |t1| + |t2| + |a|) ^ k) := mul_le_mul_of_nonneg_right h1 hKP
    _ = Real.exp ((|X₀| + |v| + 2) ^ 2 + 1) *
        (Real.exp ((X₀ + v - 1) ^ 2 - (a₀ + r' + s) ^ 2) * (‖m‖ * ‖w‖ * (2 + |t1| + |t2| + |a|) ^ k) +
         Real.exp ((X₀ + v - 1) ^ 2 - (a₀ - r' + s) ^ 2) * (‖m‖ * ‖w‖ * (2 + |t1| + |t2| + |a|) ^ k)) := by
          ring
    _ ≤ Real.exp ((|X₀| + |v| + 2) ^ 2 + 1) *
        (Real.exp ((X₀ + v - 1) ^ 2 - (a₀ + r' + s) ^ 2) *
            (‖m‖ * ‖w‖ * (2 ^ k * (2 + |t1| + |t2| + |a₀ + r'|) ^ k)) +
         Real.exp ((X₀ + v - 1) ^ 2 - (a₀ - r' + s) ^ 2) *
            (‖m‖ * ‖w‖ * (2 ^ k * (2 + |t1| + |t2| + |a₀ - r'|) ^ k))) := by
          apply mul_le_mul_of_nonneg_left _ hE
          linarith [a1, a2]
    _ = _ := by ring

private lemma wM_eq (η : ℂ) (v y : ℝ) (p : ℝ × ℝ) :
    WeightConvolution.weightModulus D η v y p =
      Real.exp ((η.re + v - 1) ^ 2 - (η.im + p.1) ^ 2) *
        ‖D.M ((v : ℂ) + (p.1 : ℂ) * Complex.I)‖ *
        ‖D.W1Hat ((y : ℂ) + (p.2 : ℂ) * Complex.I)‖ := by
  unfold WeightConvolution.weightModulus
  rw [norm_mul, norm_mul, Complex.norm_exp]
  have hre : ((η + ((v : ℂ) + (p.1 : ℂ) * Complex.I) - 1) ^ 2).re =
      (η.re + v - 1) ^ 2 - (η.im + p.1) ^ 2 := by
    simp [pow_two] <;> ring
  rw [hre]

theorem differentiableOn_nested_integral (V : Set ℂ) (hV : IsOpen V) (G : ℂ → ℂ → ℂ → ℂ)
    (y v : ℝ) (hv : 0 < v)
    (hdiff : ∀ ξ ∈ V, ∀ s t : ℝ, DifferentiableAt ℂ
      (fun x : ℂ => G x ((y : ℂ) + (s : ℂ) * Complex.I) ((v : ℂ) + (t : ℂ) * Complex.I)) ξ)
    (hcont : ∀ ξ ∈ V, Continuous (fun p : ℝ × ℝ =>
      G ξ ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I)))
    (hmaj : ∀ ξ₀ ∈ V, ∃ r : ℝ, 0 < r ∧ Metric.ball ξ₀ r ⊆ V ∧ ∃ C k : ℝ, 0 ≤ C ∧ 0 ≤ k ∧
      ∀ ξ ∈ Metric.ball ξ₀ r, ∀ p : ℝ × ℝ,
        ‖G ξ ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I)‖ ≤
          C * WeightConvolution.weightModulus D ξ v y p *
            (2 + |p.1| + |p.2| + |ξ.im|) ^ k) :
    DifferentiableOn ℂ (fun ξ => comparisonVerticalIntegral y (fun w =>
      comparisonVerticalIntegral v (fun z => G ξ w z))) V := by
  classical
  obtain ⟨H, hH⟩ : ∃ H : ℂ → ℝ × ℝ → ℂ, ∀ ξ p, H ξ p =
      G ξ ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I) :=
    ⟨fun ξ p => G ξ ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I),
      fun _ _ => rfl⟩
  have hHf : ∀ ξ, H ξ = fun p : ℝ × ℝ =>
      G ξ ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I) :=
    fun ξ => funext (hH ξ)
  have hdom : ∀ ξ₀ ∈ V, ∃ r : ℝ, 0 < r ∧ Metric.ball ξ₀ r ⊆ V ∧
      ∃ g : ℝ × ℝ → ℝ, Integrable g ∧ ∀ ξ ∈ Metric.ball ξ₀ r, ∀ p, ‖H ξ p‖ ≤ g p := by
    intro ξ₀ hξ₀
    obtain ⟨r, hr, hball, C, k, hC, hk, hb⟩ := hmaj ξ₀ hξ₀
    obtain ⟨C', -, hC'⟩ := WeightConvolution.weight_kernel_decay D v v y y ξ₀.re ξ₀.re hv
      le_rfl le_rfl le_rfl 1 k one_pos hk
    have hr' : 0 < min r 1 := lt_min hr one_pos
    obtain ⟨ξp, hpre, hpim⟩ : ∃ ξp : ℂ, ξp.re = ξ₀.re ∧ ξp.im = ξ₀.im + min r 1 :=
      ⟨⟨ξ₀.re, ξ₀.im + min r 1⟩, rfl, rfl⟩
    obtain ⟨ξm, hmre, hmim⟩ : ∃ ξm : ℂ, ξm.re = ξ₀.re ∧ ξm.im = ξ₀.im - min r 1 :=
      ⟨⟨ξ₀.re, ξ₀.im - min r 1⟩, rfl, rfl⟩
    have hIp := (hC' ξp hpre.ge hpre.le v y le_rfl le_rfl le_rfl le_rfl).1
    have hIm := (hC' ξm hmre.ge hmre.le v y le_rfl le_rfl le_rfl le_rfl).1
    refine ⟨min r 1, hr', (Metric.ball_subset_ball (min_le_left _ _)).trans hball,
      fun p => C * Real.exp ((|ξ₀.re| + |v| + 2) ^ 2 + 1) * 2 ^ k *
        (WeightConvolution.weightModulus D ξp v y p * (2 + |p.1| + |p.2| + |ξp.im|) ^ k +
         WeightConvolution.weightModulus D ξm v y p * (2 + |p.1| + |p.2| + |ξm.im|) ^ k),
      (hIp.add hIm).const_mul _, ?_⟩
    intro ξ hξ p
    have hd : ‖ξ - ξ₀‖ < min r 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hξ
    have hX : |ξ.re - ξ₀.re| ≤ 1 := by
      have := Complex.abs_re_le_norm (ξ - ξ₀)
      rw [Complex.sub_re] at this
      linarith [min_le_right r 1]
    have ha : |ξ.im - ξ₀.im| ≤ min r 1 := by
      have := Complex.abs_im_le_norm (ξ - ξ₀)
      rw [Complex.sub_im] at this
      linarith
    have hb' := hb ξ (Metric.ball_subset_ball (min_le_left _ _) hξ) p
    have hb'' : ‖H ξ p‖ ≤ C * WeightConvolution.weightModulus D ξ v y p *
        (2 + |p.1| + |p.2| + |ξ.im|) ^ k := by rw [hH]; exact hb'
    refine hb''.trans ?_
    beta_reduce
    have key := pt_env ξ.re ξ₀.re ξ.im ξ₀.im (min r 1) v p.1 p.1 p.2 k
      (D.M ((v : ℂ) + (p.1 : ℂ) * Complex.I)) (D.W1Hat ((y : ℂ) + (p.2 : ℂ) * Complex.I))
      hk hr' (min_le_right _ _) hX ha
    have key2 := mul_le_mul_of_nonneg_left key hC
    rw [wM_eq D ξ v y p, wM_eq D ξp v y p, wM_eq D ξm v y p, hpre, hpim, hmre, hmim]
    calc C * (Real.exp ((ξ.re + v - 1) ^ 2 - (ξ.im + p.1) ^ 2) *
          ‖D.M ((v : ℂ) + (p.1 : ℂ) * Complex.I)‖ *
          ‖D.W1Hat ((y : ℂ) + (p.2 : ℂ) * Complex.I)‖) * (2 + |p.1| + |p.2| + |ξ.im|) ^ k
        = C * (Real.exp ((ξ.re + v - 1) ^ 2 - (ξ.im + p.1) ^ 2) *
          ‖D.M ((v : ℂ) + (p.1 : ℂ) * Complex.I)‖ *
          ‖D.W1Hat ((y : ℂ) + (p.2 : ℂ) * Complex.I)‖ * (2 + |p.1| + |p.2| + |ξ.im|) ^ k) := by
          ring
      _ ≤ _ := key2
      _ = _ := by ring
  have hmeas : ∀ ξ ∈ V, AEStronglyMeasurable (H ξ) (volume : Measure (ℝ × ℝ)) := by
    intro ξ hξ
    rw [hHf ξ]
    exact (hcont ξ hξ).aestronglyMeasurable
  have hdiffp : ∀ p, DifferentiableOn ℂ (fun ξ => H ξ p) V := by
    intro p ξ hξ
    simp only [hH]
    exact (hdiff ξ hξ p.2 p.1).differentiableWithinAt
  have h2 := HolomorphicDominatedIntegral.differentiableOn_integral_prod_real hV hmeas hdiffp hdom
  have heq : ∀ ξ ∈ V, comparisonVerticalIntegral y (fun w =>
      comparisonVerticalIntegral v (fun z => G ξ w z)) =
        ((2 * (Real.pi : ℂ))⁻¹) ^ 2 * ∫ p, H ξ p := by
    intro ξ hξ
    have hint : Integrable (H ξ) :=
      HolomorphicDominatedIntegral.integrable_of_locally_dominated (μ := volume) hmeas hdom hξ
    have e0 : ∫ p, H ξ p = ∫ s : ℝ, ∫ t : ℝ, H ξ (t, s) := integral_prod_symm (H ξ) hint
    have e1 : ∫ s : ℝ, ∫ t : ℝ, H ξ (t, s) = ∫ s : ℝ, ∫ t : ℝ,
        G ξ ((y : ℂ) + (s : ℂ) * Complex.I) ((v : ℂ) + (t : ℂ) * Complex.I) := by
      simp only [hH]
    show (2 * (Real.pi : ℂ))⁻¹ * ∫ s : ℝ, ((2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ,
      G ξ ((y : ℂ) + (s : ℂ) * Complex.I) ((v : ℂ) + (t : ℂ) * Complex.I)) = _
    rw [integral_const_mul, e0, e1]
    ring
  exact (h2.const_mul (((2 * (Real.pi : ℂ))⁻¹) ^ 2)).congr (fun ξ hξ => heq ξ hξ)




end

end DedekindZetaZeroFree.Quantitative.RowKernelHolomorphy
