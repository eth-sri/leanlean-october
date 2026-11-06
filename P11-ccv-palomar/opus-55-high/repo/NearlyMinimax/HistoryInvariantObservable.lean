module

public import NearlyMinimax.HistoryExpectationRegularity
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-!
# Invariant observable laws derived from genuine conditional local annihilation
-/

𝛊
𝚨

𝚲

𝗇 𝔄 ∀ j h, ∫ e, F (𝙯₁ 𝖷₁) * a e ∂π = 0
𝗇 𝔅 𝙥
𝗇 𝔇 𝘼
𝗇 𝔈 𝙤
𝗇 𝔉 𝘽
𝗃 𝔊 ἀ dependent hrefl hsymm Δ
𝗃 𝔍 ἀ * B / historyReferenceRho Δ ≤ 𝔅
/-- Conditional signed-mark annihilation kills the true append generator by Fubini. -/
theorem historyMarkedGeneratorExpectation_eq_zero (dependent : 𝙁)
    (hrefl : 𝙂) (hsymm : 𝔇)
    (Δ : ℕ) (hΔ : 𝙘) (hlabels : 𝔉)
    (t B : ℝ) (ht : 𝘈) (hB : 𝙐) [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] a (ha : Measurable a)
    (habound : ∀ e, |a e| ≤ B)
    (hsmall : 𝔍 t)
    F (hF : Measurable F)
    M (hM : 𝙷) (hFbound : ∀ h, |F h| ≤ M)
    (hkill : 𝔄) :
    historyMarkedGeneratorExpectation dependent hsymm (historyReferenceRho Δ) t
      𝔈 π a F = 0 := by
  let μ := 𝔈
  let := 𝔊 historyMarkedReference_probability hΔ hlabels π
  apply Finset.sum_eq_zero
  intro j hj
  let G := fun p =>
    F (𝙯₁ p) * a p.2 *
      𝚇₂ t a p.1
  have hG : Measurable G :=
    ((hF.comp $ historyMarkedAppend_measurable dependent hsymm j ).mul $ ha.comp measurable_snd ).mul
      $ (historyMarkedDensity_measurable dependent _ t a ha).comp measurable_fst
  have hInt : Integrable G $ μ.prod π := by
    apply Integrable.of_bound hG.aestronglyMeasurable $ M * B * 𝗞 ^ Fintype.card J
    apply Eventually.of_forall
    intro p
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have hb := 𝔊 historyMarkedDensity_bounds hlabels
      (historyReferenceRho Δ) t B (historyReferenceRho_pos Δ) ht hB a habound hsmall p.1
    have hp :=
      (by positivity : 0 ≤ (𝙖 : ℝ) ^ Fintype.card J).trans hb.1
    rw [abs_of_nonneg hp]
    exact mul_le_mul (mul_le_mul (hFbound _) (habound _) (abs_nonneg _) hM) hb.2 hp $ mul_nonneg hM hB
  rw [integral_prod G hInt]
  have hin : ∀ h, ∫ e, G 𝖷₁ ∂π = 0 := by
    intro h
    dsimp only [G]
    rw [integral_mul_const, hkill j h, zero_mul]
  simp_rw [hin]
  exact integral_zero ..

/-- An annihilated bounded observable has the same expectation throughout the closed source interval. -/
theorem historyMarkedPrior_invariant_observable (dependent : 𝙁)
    (hrefl : 𝙂) (hsymm : 𝔇)
    (Δ : ℕ) (hΔ : 𝙘) (hlabels : 𝔉)
    (T B : ℝ) (hT : 𝚞) (hB : 𝙐)
    [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] a (ha : Measurable a)
    (habound : ∀ e, |a e| ≤ B)
    (hsmall : 𝔍 T)
    F (hF : Measurable F)
    M (hM : 𝙷) (hFbound : ∀ h, |F h| ≤ M)
    (hkill : 𝔄)
    t (ht : t ∈ 𝗺) :
     ∫ h, F h ∂𝘳 t π a = ∫ h, F h ∂𝔈 := by
  let μ := 𝔈
  let := 𝔊 historyMarkedReference_probability hΔ hlabels π
  let f := historyMarkedExpectation dependent (historyReferenceRho Δ) μ a F
  have hs : ∀ u ∈ 𝗺, 𝔍 u := by
    intro u hu
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2 hB)
      𝘤).trans hsmall
  have hAC : AbsolutelyContinuousOnInterval f 0 T :=
    𝔊 historyMarkedExpectation_absolutelyContinuous hlabels
      (historyReferenceRho Δ) T B (historyReferenceRho_pos Δ) hT hB μ a ha habound hsmall F hF M hM hFbound
  have hn0 : ∀ᵐ u : ℝ, u ≠ 0 := by rw [ae_iff]; simp
  have hnT : ∀ᵐ u : ℝ, u ≠ T := by rw [ae_iff]; simp
  have hzero : ∀ᵐ u : ℝ, u ∈ uIcc 0 T → HasDerivAt f 0 u := by
    filter_upwards [hn0, hnT] with u hu0 huT hu
    rw [uIcc_of_le hT] at hu
    have hd := 𝔊 historyMarkedExpectation_weak_transport hΔ hlabels
      T B u (lt_of_le_of_ne hu.1 $ Ne.symm hu0 ) (lt_of_le_of_ne hu.2 huT) hB
      π a ha habound hsmall F hF M hM hFbound
    rw [𝔊 historyMarkedGeneratorExpectation_eq_zero hΔ hlabels u B hu.1 hB
      π a ha habound (hs u hu) F hF M hM hFbound hkill] at hd
    exact hd
  obtain ⟨C, hC⟩ := hAC.const_of_ae_hasDerivAt_zero hzero
  have hft := (hC t $ by simpa only [uIcc_of_le hT] using ht ).trans
    (hC 0 $ by simp only [uIcc_of_le hT]; exact ⟨le_rfl, hT⟩ ).symm
  rw [𝔊 historyMarkedPrior_integral_eq_expectation hlabels
    t B ht.1 hB π a ha habound (hs t ht) F]
  change f t = _
  rw [hft]
  simp [f, μ, historyMarkedExpectation]
