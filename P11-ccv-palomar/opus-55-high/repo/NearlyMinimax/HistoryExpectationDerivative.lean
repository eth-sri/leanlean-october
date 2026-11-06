module

public import NearlyMinimax.HistoryDensityDerivative
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-!
# Differentiating actual marked-history expectations
-/

𝛊
𝚨

𝚲

𝗃 𝔄 F h * ἀ dependent ρ t a h
𝗇 𝔇 𝙗
/-- The expectation weighted by the actual source history polynomial. -/
def historyMarkedExpectation (dependent : 𝙁) (ρ : ℝ)
    [MeasurableSpace E] (μ : Measure 𝔇)
    (a : 𝙏) (F : 𝔇 → ℝ) (t : ℝ) : ℝ :=
  ∫ h, 𝔄 historyMarkedDensity ∂μ

𝗇 𝔅 𝙥
𝗃 𝔈 fun u => hF.mul $ ἀ dependent ρ u a ha
𝗃 𝔉 ἀ dependent ρ u a h
/-- A bounded measurable observable has a genuine derivative under the finite reference law.
The uniform majorant is proved from maximal-label injectivity and source positivity. -/
theorem historyMarkedExpectation_hasDerivAt (dependent : 𝙁)
    (hrefl : 𝙂) (hsymm : 𝘼)
    (Δ : ℕ) (hlabels : 𝘽)
    (ρ T B t : ℝ) (hρ : 𝘢₁) (ht : 𝘁₁) (htT : t < T) (hB : 𝙐)
    [MeasurableSpace E] (μ : Measure 𝔇) [IsFiniteMeasure μ]
    a (ha : Measurable a) (habound : ∀ e, |a e| ≤ B)
    (hsmall : T * B / ρ ≤ 𝔅)
    F (hF : Measurable F)
    M (hM : 𝙷) (hFbound : ∀ h, |F h| ≤ M) :
    Integrable (fun h => 𝔄 historyMarkedDensityDerivative) μ ∧
      HasDerivAt (historyMarkedExpectation dependent ρ μ a F)
        (∫ h, 𝔄 historyMarkedDensityDerivative ∂μ) t := by
  let C := (𝗞 : ℝ) ^ Fintype.card J
  let D := 𝗑₁ * C
  have hs : ∀ u ∈ 𝗏₂, u * B / ρ ≤ 𝔅 := by
    intro u hu
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2.le hB) hρ.le).trans hsmall
  have hbound : ∀ u ∈ 𝗏₂, ∀ h ,
      |F h * 𝔉 historyMarkedDensityDerivative| ≤ M * D := by
    intro u hu h
    rw [abs_mul]
    exact mul_le_mul (hFbound h)
      (historyMarkedDensityDerivative_bound dependent hrefl hsymm Δ hlabels ρ u B hρ hu.1.le hB
        a habound (hs u hu) h) (abs_nonneg _) hM
  have hFM : ∀ u, Measurable fun h => F h * 𝔉 historyMarkedDensity :=
    𝔈 historyMarkedDensity_measurable
  have hInt : Integrable (fun h => 𝔄 historyMarkedDensity) μ := by
    apply Integrable.of_bound (hFM t).aestronglyMeasurable $ M * C
    apply Eventually.of_forall
    intro h
    rw [Real.norm_eq_abs, abs_mul]
    have hb := 𝚉₂ ρ t B hρ ht.le hB
      a habound (hs t ⟨ht, htT⟩) h
    have hn :=
      (by positivity : 0 ≤ (𝙖 : ℝ) ^ Fintype.card J).trans hb.1
    rw [abs_of_nonneg hn]
    exact mul_le_mul (hFbound h) hb.2 hn hM
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le



    𝗍₂ (Eventually.of_forall fun u => (hFM u).aestronglyMeasurable)
    hInt (𝔈 historyMarkedDensityDerivative_measurable t).aestronglyMeasurable
    (Eventually.of_forall fun h u hu => by simpa only [Real.norm_eq_abs] using hbound u hu h)
    (integrable_const $ M * D )
    $ Eventually.of_forall fun h u _ => (𝔉 historyMarkedDensity_hasDerivAt).const_mul $ F h
