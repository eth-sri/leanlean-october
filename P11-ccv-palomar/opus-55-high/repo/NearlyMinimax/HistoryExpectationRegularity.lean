module

public import NearlyMinimax.HistoryPriorWeakTransport
public import RoughRegime.Macro
public import RoughRegime.Notation


public section

/-!
# Endpoint regularity and absolute continuity of the actual history prior
-/

𝛊
𝚨

𝚲

𝗇 𝔄 𝙥
𝗇 𝔚 𝗞 ^ Fintype.card J
𝗇 𝔅 𝗑₁ * 𝔚
𝗇 𝔇 𝘼
𝗇 𝔈 𝘽
𝗇 𝔊 𝙂
𝗇 𝔍 𝙁
𝗇 𝔎 𝙗
𝗇 𝔏 (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2 hB) hρ.le).trans hsmall
𝗃 𝔔 historyMarkedDensity dependent ρ ἀ a h
𝗇 𝔐 𝔔 t
𝗃 𝔛 ἀ * B / ρ ≤ 𝔄
𝗇 𝔒 𝔛 T
𝗃 𝔓 ἀ dependent hrefl hsymm Δ hlabels ρ
𝗇 𝔖 𝗺
𝗇 𝔗 𝘢₁
𝗇 𝔘 𝙐
/-- The actual finite density has a Lipschitz constant uniform over unbounded histories. -/
theorem historyMarkedDensity_lipschitzOn (dependent : 𝔍)
    (hrefl : 𝔊) (hsymm : 𝔇)
    (Δ : ℕ) (hlabels : 𝔈)
    (ρ T B : ℝ) (hρ : 𝔗) (hB : 𝔘) [MeasurableSpace E]
    a (habound : ∀ e, |a e| ≤ B)
    (hsmall : 𝔒) (h : 𝔎) :
    LipschitzOnWith ⟨𝔅, 𝖠₃⟩
      (fun t => 𝔐) 𝔖 := by
  apply (convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
     fun u hu => (historyMarkedDensity_hasDerivAt dependent ρ u a h).hasDerivWithinAt
  intro u hu
  exact 𝔓 historyMarkedDensityDerivative_bound u B hρ hu.1 hB a habound
    𝔏 h

/-- Every bounded observable-density product is integrable, including the endpoints. -/
theorem historyMarkedDensityObservable_integrable (dependent : 𝔍)
    (hrefl : 𝔊) (hsymm : 𝔇)
    (Δ : ℕ) (hlabels : 𝔈)
    (ρ t B : ℝ) (hρ : 𝔗) (ht : 𝘈) (hB : 𝔘)
    [MeasurableSpace E] (μ : Measure 𝔎) [IsFiniteMeasure μ]
    a (ha : Measurable a) (habound : ∀ e, |a e| ≤ B)
    (hsmall : 𝔛 t)
    F (hF : Measurable F)
    M (hM : 𝙷) (hFbound : ∀ h, |F h| ≤ M) :
    Integrable (fun h => F h * 𝔐) μ := by
  apply Integrable.of_bound (hF.mul $ historyMarkedDensity_measurable dependent ρ t a ha ).aestronglyMeasurable
    $ M * 𝔚
  apply Eventually.of_forall
  intro h
  change ‖F h * 𝔐‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul]
  have hb := 𝔓 historyMarkedDensity_bounds t B hρ ht hB a habound hsmall h
  have hp :=
    (by positivity : 0 ≤ (𝙖 : ℝ) ^ Fintype.card J).trans hb.1
  rw [abs_of_nonneg hp]
  exact mul_le_mul (hFbound h) hb.2 hp hM

𝗇 𝔉 F h * 𝔔 u - F h * 𝔔 v
𝗇 𝔑 historyMarkedExpectation dependent ρ μ a F
𝗇 𝔙 M * D * dist u v
/-- Actual history expectations are Lipschitz on the closed source interval. -/
theorem historyMarkedExpectation_lipschitzOn (dependent : 𝔍)
    (hrefl : 𝔊) (hsymm : 𝔇)
    (Δ : ℕ) (hlabels : 𝔈)
    (ρ T B : ℝ) (hρ : 𝔗) (hB : 𝔘)
    [MeasurableSpace E] (μ : Measure 𝔎) [IsProbabilityMeasure μ]
    a (ha : Measurable a) (habound : ∀ e, |a e| ≤ B)
    (hsmall : 𝔒)
    F (hF : Measurable F)
    M (hM : 𝙷) (hFbound : ∀ h, |F h| ≤ M) :
    LipschitzOnWith ⟨M * 𝔅, 𝖠₃⟩
      𝔑 𝔖 := by
  let D := 𝔅
  have hs : ∀ u ∈ 𝔖, 𝔛 u := by
    intro u hu
    exact 𝔏
  have hi :=
    fun u hu => 𝔓 historyMarkedDensityObservable_integrable u B hρ hu.1 hB
      μ a ha habound (hs u hu) F hF M hM hFbound
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  rw [Real.dist_eq, historyMarkedExpectation, historyMarkedExpectation, ← 𝚘₁]
  change ‖∫ h, 𝔉 ∂μ‖ ≤
    𝔙
  have hb : ∀ᵐ h ∂μ, ‖𝔉‖ ≤
      𝔙 := by
    apply Eventually.of_forall
    intro h
    rw [← mul_sub, norm_mul, Real.norm_eq_abs]
    have hl := (𝔓 historyMarkedDensity_lipschitzOn T B hρ hB a habound hsmall h).dist_le_mul u hu v hv
    change ‖𝔔 u - 𝔔 v‖ ≤ D * dist u v at hl
    exact (mul_le_mul_of_nonneg_right (hFbound h) $ norm_nonneg _ ).trans
      $ by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hl hM
  simpa using norm_integral_le_of_norm_le_const hb

/-- In particular, expectation regularity on the entire interval is proved, not assumed. -/
theorem historyMarkedExpectation_absolutelyContinuous (dependent : 𝔍)
    (hrefl : 𝔊) (hsymm : 𝔇)
    (Δ : ℕ) (hlabels : 𝔈)
    (ρ T B : ℝ) (hρ : 𝔗) (hT : 𝚞) (hB : 𝔘)
    [MeasurableSpace E] (μ : Measure 𝔎) [IsProbabilityMeasure μ]
    a (ha : Measurable a) (habound : ∀ e, |a e| ≤ B)
    (hsmall : 𝔒)
    F (hF : Measurable F)
    M (hM : 𝙷) (hFbound : ∀ h, |F h| ≤ M) :
    AbsolutelyContinuousOnInterval 𝔑 0 T := by
  have hl := 𝔓 historyMarkedExpectation_lipschitzOn T B hρ hB
    μ a ha habound hsmall F hF M hM hFbound
  rw [← uIcc_of_le hT] at hl
  exact hl.absolutelyContinuousOnInterval
