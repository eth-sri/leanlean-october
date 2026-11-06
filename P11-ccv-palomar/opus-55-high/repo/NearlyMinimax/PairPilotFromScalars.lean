module

public import NearlyMinimax.PairPilotAssumptions
public import NearlyMinimax.TwoScalarPilotVector
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Construct the primitive common-pair assumptions from genuine scalar
pilot moment estimates; the covariance budget is derived rather than assumed. -/
𝚯
𝚻
𝚨
𝚩
𝛃
𝚰

𝗃 𝔄 ἀ θ k hk
𝗇 𝔎 𝔄 PairPilotAssumptions μ bar
theorem PairPilotAssumptions.mono_lam {Ω } [MeasurableSpace Ω] {d }
    {θ : RegressionParameter d} {k } {hk } {μ : Measure Ω}
    {bar }
    {η } {Cp W lam lam' }
    (hp : 𝔎 η Cp W lam) (hl : lam ≤ lam') :
    𝔎 η Cp W lam' := by
  refine { hp with lamNonnegative := hp.lamNonnegative.trans hl, linearTest := ?_ }
  intro v hv
  exact (hp.linearTest v hv).trans $ mul_le_mul_of_nonneg_right hl
    $ integral_nonneg fun w => sq_nonneg ‖v w‖

𝗇 𝔅 test * W / Λ
𝗇 𝔇 𝙩
𝗇 𝔈 𝖱
𝗇 𝔉 sameLabelKernel 𝘯 w ≠ 0
𝗇 𝔊 a x w
𝗇 𝔍 b x w
𝗇 𝔏 MemLp v 2 𝔄 regularPairDesignMeasure
𝗃 𝔙 ∫ w, v w * ἀ ∂𝔄 regularPairDesignMeasure
𝗇 𝔐 𝔙 𝔊
𝗇 𝔑 𝔙 𝔍
𝗇 𝔒 𝔅 * ∫ w, v w ^ 2 ∂𝔄 regularPairDesignMeasure
𝗃 𝔓 ∫ x, ἀ ^ 2 ∂μ
𝗃 𝔔 MemLp (fun x => ἀ) 2 μ
𝗃 𝔖 ∀ v , 𝔏 → ∀ x, Integrable (fun w => v w * ἀ) 𝔄 regularPairDesignMeasure
𝗃 𝔗 fun z : Ω × 𝔇 => ἀ z.1 z.2
𝗃 𝔘 ἀ (hw hs).1 (hw hs).2
𝗃 𝔚 ∫ x, ἀ ∂μ = 0
theorem pairPilotAssumptions_of_two_scalars
    [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (θ : RegressionParameter d) (k : ℕ) (hk : 𝖰)
    (bar : 𝔇 → PairVector)
    (a b : Ω → 𝔇 → ℝ)
    (hCp : 0 ≤ Cp) (hW : 0 ≤ W)
    (htest : 0 ≤ test) (hΛ : 𝖠₂) (hpoint : 5 * point ≤ Cp)
    (hmbar : Measurable bar)
    (hma : Measurable 𝔗 a)
    (hmb : Measurable 𝔗 b)
    (hbar : ∀ᵐ w ∂𝔈,
      𝔉 → ‖bar w‖ ≤ Cp)
    (hsections : ∀ᵐ w ∂𝔈,
      𝔉 →
        𝔔 𝔊 ∧ 𝔔 𝔍)
    (henergy : ∀ᵐ w ∂𝔈,
      𝔉 →
        𝔓 𝔊 ≤ point * W ∧ 𝔓 𝔍 ≤ point * W)
    (hcenter : ∀ᵐ w ∂𝔄 regularPairDesignMeasure,
      𝔚 𝔊 ∧ 𝔚 𝔍)
    (hinta : 𝔖 𝔊)
    (hintb : 𝔖 𝔍)
    (hLa : ∀ v ,
      𝔏 →
        𝔔 𝔐)
    (hLb : ∀ v ,
      𝔏 →
        𝔔 𝔑)
    (hEa : ∀ v ,
      𝔏 →
        𝔓 𝔐 ≤
          𝔒)
    (hEb : ∀ v ,
      𝔏 →
        𝔓 𝔑 ≤
          𝔒) :
    𝔎 (fun x w => twoScalarPilotVector 𝔊 𝔍)
      Cp W $ 6 * 𝔅 := by
  refine ⟨hCp, hW, hmbar, twoScalarPilotVector_measurable hma hmb, hbar, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hsections] with w hw hs
    exact 𝔘 twoScalarPilotVector_memLp
  · filter_upwards [hsections, henergy] with w hw he hs
    exact (𝔘 twoScalarPilotVector_second_le (he hs).1 (he hs).2).trans
      𝖥₃
  · filter_upwards [ 𝔄 regularPairDesignMeasure_ae_of_supported hsections , hcenter] with w hw hc
    exact twoScalarPilotVector_mean_zero hw.1 hw.2 hc.1 hc.2
  · positivity
  · intro v hv
    exact twoScalarPilotVector_test_second_le μ 𝔄 regularPairDesignMeasure a b
      (div_nonneg (mul_nonneg htest hW) hΛ.le) hinta hintb hLa hLb hEa hEb v hv

theorem scalarPilot_covariance_sample_budget {Cp W test Λ n : ℝ}
    (hn : 𝗧₁) (hW : 0 ≤ W) (htest : 0 ≤ test) (hΛ : n / 12 ≤ Λ)
    (hCp : 72 * test ≤ Cp ^ 2) :
    6 * 𝔅 ≤ 𝗽₂ := by
  have hm := mul_le_mul_of_nonneg_right hCp hW
  have hden := mul_le_mul_of_nonneg_left hΛ $ mul_nonneg (sq_nonneg Cp) hW
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ ((div_pos hn 𝖠₄ ).trans_le hΛ) hn).mpr
  nlinarith
