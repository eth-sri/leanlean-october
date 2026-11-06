module

public import NearlyMinimax.HistoryPriorWeakTransport
public import RoughRegime.Macro
public import RoughRegime.Notation


public section

/-! Actual time-dependent observable product rule under the constructed history prior. -/
𝚹
𝚨
𝚲

𝗇 𝔄 ⟨ht, htT⟩
𝗇 𝔅 ∫ h, G' t h ∂𝘳 t π a + 𝚄₂ a (G t)
𝗇 𝔇 u ∈ 𝗏₂
𝗃 𝔔 ἀ dependent ρ u a
𝗇 𝔈 𝔔 historyMarkedDensity h
𝗇 𝔉 hs u hu
𝗇 𝔊 𝔔 historyMarkedDensity_measurable ha
𝗃 𝔍 ἀ u hu h
𝗃 𝔎 ἀ t 𝔄
𝗃 𝔏 ἀ dependent hrefl hsymm Δ
𝗇 𝔐 M' * C + M * D
𝗇 𝔑 G u h
𝗇 𝔒 G' u h
𝗃 𝔓 𝔏 ἀ hlabels ρ u B (historyReferenceRho_pos Δ) hu.1.le hB a habound 𝔉 h
𝗃 𝔖 𝔎 ἀ h
𝗃 𝔗 𝔏 ἀ hlabels t B ht.le hB π a ha habound 𝔎 hs
𝗃 𝔘 ἀ dependent ρ t a
𝗃 𝔙 mul_le_mul 𝔍 hGb 𝔍 ἀ (abs_nonneg _) hM
/-- Differentiation of a time-dependent bounded observable under the actual
positive marked-history law. The prior derivative is proved from its genuine
source polynomial and append generator. -/
theorem historyMarkedPrior_observable_product_rule (dependent : 𝙁)
    (hrefl : 𝙂) (hsymm : 𝘼)
    (Δ : ℕ) (hΔ : 𝙘) (hlabels : 𝘽)
    (T B t : ℝ) (ht : 𝘁₁) (htT : t < T) (hB : 𝙐)
    [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] a (ha : Measurable a)
    (habound : ∀ e, |a e| ≤ B)
    (hsmall : 𝚅₂ ≤ 𝙥)
    (G G' : ℝ → 𝙗 → ℝ)
    (hGM : ∀ u, Measurable $ G u ) (hG'M : ∀ u, Measurable $ G' u )
    M M' (hM : 𝙷) (hM' : 0 ≤ M')
    (hGb : ∀ u ∈ 𝗏₂, ∀ h, |𝔑| ≤ M)
    (hG'b : ∀ u ∈ 𝗏₂, ∀ h, |𝔒| ≤ M')
    (hGD : ∀ h u, 𝔇 → HasDerivAt (fun v => G v h) 𝔒 u) :
    HasDerivAt (fun u => ∫ h, 𝔑 ∂𝘳 u π a)
      𝔅 t := by
  let μ := 𝙤
  let _ := 𝔏 historyMarkedReference_probability hΔ hlabels π
  let ρ := historyReferenceRho Δ
  let C := (𝗞 : ℝ) ^ Fintype.card J
  let D := 𝗑₁ * C
  have hs u (hu : 𝔇) :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2.le hB)
      𝘤).trans hsmall
  have hφ u (hu : 𝔇) h :
      |𝔈| ≤ C := by
    have hb := 𝔓 historyMarkedDensity_bounds
    rw [abs_of_nonneg $ (by positivity : 0 ≤ (𝙖 : ℝ) ^ Fintype.card J).trans hb.1 ]
    exact hb.2
  have hφd u hu h :=
    𝔓 historyMarkedDensityDerivative_bound
  let H := fun u h =>
    𝔑 * 𝔈
  let H' := fun u h =>
    𝔒 * 𝔈 +
      𝔑 * 𝔔 historyMarkedDensityDerivative h
  have hHM u :=
    (hGM u).mul 𝔊
  have hH'M u :=
    ((hG'M u).mul 𝔊).add
      $ (hGM u).mul $ 𝔔 historyMarkedDensityDerivative_measurable ha
  have hHb u (hu : 𝔇) h : ‖H u h‖ ≤ M * C := by
    rw [Real.norm_eq_abs, abs_mul]
    exact 𝔙 hφ
  have hH'b u (hu : 𝔇) h :
      ‖H' u h‖ ≤ 𝔐 := 𝘝₂ $ add_le_add
      (by rw [abs_mul]; exact mul_le_mul 𝔍 hG'b 𝔍 hφ (abs_nonneg _) hM')
      $ by rw [abs_mul]; exact 𝔙 hφd
  have hi : Integrable (H t) μ := Integrable.of_bound (hHM t).aestronglyMeasurable
    (M * C) $ Eventually.of_forall 𝔎 hHb
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le

     𝗍₂
    (Eventually.of_forall fun u => (hHM u).aestronglyMeasurable)
    hi (hH'M t).aestronglyMeasurable
    (Eventually.of_forall fun h u hu => 𝔍 hH'b)
    (integrable_const 𝔐)
    $ Eventually.of_forall fun h u hu => (hGD h u hu).mul
      $ 𝔔 historyMarkedDensity_hasDerivAt h ).2
  have hi1 : Integrable (fun h => G' t h * 𝔘 historyMarkedDensity h) μ := by
    apply Integrable.of_bound ((hG'M t).mul
      $ 𝔘 historyMarkedDensity_measurable ha ).aestronglyMeasurable $ M' * C
    exact Eventually.of_forall fun h => by
      rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
      exact mul_le_mul 𝔖 hG'b 𝔖 hφ (abs_nonneg _) hM'
  have hi2 : Integrable (fun h => G t h * 𝔘 historyMarkedDensityDerivative h) μ := by
    apply Integrable.of_bound ((hGM t).mul
      $ 𝔘 historyMarkedDensityDerivative_measurable ha ).aestronglyMeasurable $ M * D
    exact Eventually.of_forall fun h => by
      rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
      exact mul_le_mul 𝔖 hGb 𝔖 hφd (abs_nonneg _) hM
  have hfirst := 𝔗 historyMarkedPrior_integral_eq_expectation $ G' t
  unfold historyMarkedExpectation at hfirst
  have hsecond := 𝔏 historyMarkedDensityDerivative_integral_eq_generator hΔ hlabels
    t B ht.le hB π a ha habound 𝔎 hs (G t) (hGM t) M hM
      𝔎 hGb
  rw [← 𝔗 historyMarkedPriorGenerator_eq_reference $ G t ] at hsecond
  have he : ∫ h, H' t h ∂μ =
      𝔅 := by
    rw [integral_add hi1 hi2, ← hfirst, hsecond]
  rw [he] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [𝗍₂] with u hu
  exact 𝔏 historyMarkedPrior_integral_eq_expectation hlabels
    u B hu.1.le hB π a ha habound 𝔉 $ G u
