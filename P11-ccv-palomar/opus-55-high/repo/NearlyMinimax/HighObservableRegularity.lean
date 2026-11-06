module

public import NearlyMinimax.HighObservableProductRule
public import NearlyMinimax.HistoryExpectationRegularity
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-! Endpoint regularity of genuine time-dependent marked-prior observables. -/
𝚹
𝚨
𝚭
𝚩
𝚲

𝗇 𝔄 𝘡₂ u a h
𝗇 𝔅 𝗺
𝗇 𝔇 (K * C + M * D) * dist u v
𝗇 𝔈 G u h
𝗇 𝔉 G v h * (𝔄 - 𝘡₂ v a h)
𝗇 𝔊 𝗞
𝗇 𝔍 (𝔈 - G v h) * 𝔄
𝗇 𝔎 hφ u hu h
𝗇 𝔏 hs u hu
𝗇 𝔐 H u h - H v h
𝗃 𝔑 ἀ dependent hrefl hsymm Δ
𝗃 𝔒 ∫ h, H ἀ h ∂μ
theorem historyMarkedPrior_variable_observable_lipschitz (dependent : 𝙁)
    (hrefl : 𝙂) (hsymm : 𝘼)
    (Δ : ℕ) (hΔ : 𝙘) (hlabels : 𝘽)
    (T B : ℝ) (hB : 𝙐) [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] a (ha : Measurable a)
    (habound : ∀ e, |a e| ≤ B)
    (hsmall : 𝚅₂ ≤ 𝙥)
    (G : ℝ → 𝙗 → ℝ) (hGM : ∀ u, Measurable $ G u )
    M (hM : 𝙷) (hGb : ∀ u ∈ 𝔅, ∀ h, |𝔈| ≤ M)
    K (hGlip : ∀ h, LipschitzOnWith K (fun u => 𝔈) 𝔅) :
    LipschitzOnWith
      ⟨K * 𝔊 ^ Fintype.card J +
        M * ((historyReferenceRho Δ)⁻¹ * Fintype.card J * B * 𝔊 ^ Fintype.card J),
        by have hρ := historyReferenceRho_pos Δ; positivity⟩
      (fun u => ∫ h, 𝔈 ∂𝘳 u π a) 𝔅 := by
  let μ := 𝙤
  let _ := 𝔑 historyMarkedReference_probability hΔ hlabels π
  let ρ := historyReferenceRho Δ
  let C := (𝔊 : ℝ) ^ Fintype.card J
  let D := 𝗑₁ * C
  have hρ := historyReferenceRho_pos Δ
  have hs u (hu : u ∈ 𝔅) :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2 hB) hρ.le).trans hsmall
  have hφ u (hu : u ∈ 𝔅) h :
      ‖𝔄‖ ≤ C := by
    have hb := 𝔑 historyMarkedDensity_bounds hlabels ρ u B hρ hu.1 hB a habound 𝔏 h
    rw [Real.norm_eq_abs, abs_of_nonneg $ (by positivity : 0 ≤ (𝙖 : ℝ) ^ Fintype.card J).trans hb.1 ]
    exact hb.2
  let H := fun u h => 𝔈 * 𝔄
  have hi u (hu : u ∈ 𝔅) : Integrable (H u) μ := by
    apply Integrable.of_bound ((hGM u).mul $ historyMarkedDensity_measurable dependent ρ u a ha ).aestronglyMeasurable $ M * C
    exact Eventually.of_forall fun h => by
      rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (hGb u hu h) 𝔎 (norm_nonneg _) hM
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  rw [𝔑 historyMarkedPrior_integral_eq_expectation hlabels u B hu.1 hB π a ha habound 𝔏,
    𝔑 historyMarkedPrior_integral_eq_expectation hlabels v B hv.1 hB π a ha habound $ hs v hv ]
  change dist 𝔒 u 𝔒 v ≤ 𝔇
  rw [dist_eq_norm, ← 𝚘₁]
  have hb : ∀ᵐ h ∂μ, ‖𝔐‖ ≤ 𝔇 := by
    apply Eventually.of_forall
    intro h
    have hGdiff := (hGlip h).dist_le_mul u hu v hv
    have he : 𝔐 = 𝔍 +
      𝔉 := 𝖢₃
    rw [he]
    calc
      _ ≤ ‖𝔍‖ +
          ‖𝔉‖ := norm_add_le ..
      _ ≤ K * dist u v * C + M * (D * dist u v) := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul hGdiff 𝔎 (norm_nonneg _) 𝖠₃ )
          $ mul_le_mul (by simpa only [Real.norm_eq_abs] using hGb v hv h) ((𝔑 historyMarkedDensity_lipschitzOn hlabels ρ T B hρ hB a habound hsmall h).dist_le_mul u hu v hv) (norm_nonneg _) hM
      𝘿 := 𝖢₃
  simpa using norm_integral_le_of_norm_le_const hb
