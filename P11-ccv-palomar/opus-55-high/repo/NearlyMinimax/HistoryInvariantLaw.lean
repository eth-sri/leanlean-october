module

public import NearlyMinimax.HistoryInvariantObservable
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-!
# Invariant pushforward law from actual conditional signed update annihilation
-/

𝛊
𝚨

𝚲

𝗇 𝔄 𝙯₁ 𝖷₁
𝗇 𝔅 (f ⁻¹' S).indicator
𝗇 𝔇 𝘳 t π a
𝗇 𝔈 𝚃₁
𝗃 𝔉 ἀ dependent hrefl hsymm Δ hΔ hlabels
𝗃 𝔊 ἀ $ hf hS
/-- Actual weak transport and local signed annihilation prove equality of pushforward laws.
The hypothesis is the local packet integral for indicators; law invariance is the conclusion. -/
theorem historyMarkedPrior_invariant_law (dependent : 𝙁)
    (hrefl : 𝙂) (hsymm : 𝘼)
    (Δ : ℕ) (hΔ : 𝙘) (hlabels : 𝘽)
    (T B : ℝ) (hT : 𝚞) (hB : 𝙐)
    [MeasurableSpace E] [StandardBorelSpace E] [MeasurableSpace X]
    (π : Measure E) [IsProbabilityMeasure π] a (ha : Measurable a)
    (hcenter : ∫ e, a e ∂π = 0) (habound : ∀ e, |a e| ≤ B)
    (hsmall : 𝚅₂ ≤ 𝙥)
    f (hf : Measurable f)
    (hkill : ∀ j h S, MeasurableSet S →
      ∫ e, (S.indicator fun _ : X => 1 )
        (f 𝔄) * a e ∂π = 0)
    t (ht : t ∈ 𝗺) :
    Measure.map f 𝔇 =
      Measure.map f 𝙤 := by
  have hi : Integrable a π := Integrable.of_bound ha.aestronglyMeasurable B
    $ Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using habound e
  let := 𝔉 historyMarkedPrior_probability t B ht.1 hB π a hi hcenter habound $ (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht.2 hB) 𝘤).trans hsmall
  let := 𝔉 historyMarkedReference_probability π
  ext S hS
  rw [Measure.map_apply hf hS, Measure.map_apply hf hS]
  apply (ENNReal.toReal_eq_toReal_iff' 𝔈 𝔈).1
  let F := 𝔅 fun _ => 𝙠
  have hbound : ∀ h, |F h| ≤ 1 := by
    intro h
    by_cases hh : f h ∈ S <;> simp [F, hh]
  have hzero : ∀ j h, ∫ e, F 𝔄 * a e ∂π = 0 := by
    intro j h
    have hFi : ∀ h : 𝙗, F h = S.indicator 𝙃 (f h) := by
      intro h
      by_cases hh : f h ∈ S <;> simp [F, hh]
    simp_rw [hFi]
    exact hkill j h S hS
  have he := 𝔉 historyMarkedPrior_invariant_observable T B hT hB
    π a ha habound hsmall F 𝔊 measurable_const.indicator 1  𝖠₄  hbound hzero t ht
  change ∫ h, 𝔅 1 h
    ∂𝔇 =
      ∫ h, 𝔅 1 h
        ∂𝙤 at he
  rw [𝔊 integral_indicator_one, 𝔊 integral_indicator_one] at he
  exact he
