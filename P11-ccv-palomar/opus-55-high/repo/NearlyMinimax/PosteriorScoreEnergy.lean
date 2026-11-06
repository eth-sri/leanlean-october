module

public import NearlyMinimax.WeightedScoreContraction
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Actual posterior score L2 and Fisher contraction under marginalization. -/
𝛊
𝚮
𝚨
𝚭
𝚩
variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]

𝗇 𝔄 (ω,z)
𝗇 𝔊 ∫ ω, L 𝔄 ∂ν
𝗇 𝔎 ∫ ω, D 𝔄 ∂ν
def posteriorMeanScore (ν : Measure Ω) (L D : Ω × Z → ℝ) (z : Z) : ℝ :=
  𝔎 / 𝔊

𝗇 𝔇 posteriorMeanScore ν L D
theorem posteriorMeanScore_measurable (ν : Measure Ω) [SFinite ν]
    (L D : Ω × Z → ℝ) (hL : Measurable L) (hD : Measurable D) :
    Measurable 𝔇 :=
  hD.stronglyMeasurable.integral_prod_left'.measurable.div
    hL.stronglyMeasurable.integral_prod_left'.measurable

𝗇 𝔒 M z / G
𝗇 𝔅 𝔒 * R z^2
𝗇 𝔈 G⁻¹ * E z
𝗇 𝔉 div_nonneg (hden _).le hG.le
𝗃 𝔍 fun ω => ἀ 𝔄
𝗇 𝔏 Eventually.of_forall 𝘕
𝗇 𝔐 D z^2 / L z
𝗇 𝔑 hLm.comp $ measurable_id.prodMk measurable_const
𝗃 𝔓 fun z => ἀ
/-- Genuine marginal Fisher energy contracts the true latent Fisher
energy. The premises are primitive likelihood/derivative integrability. -/
theorem posteriorMeanScore_memLp_energy (ν : Measure Ω) [IsProbabilityMeasure ν]
    (μ : Measure Z) [SFinite μ] L D
    (hLm : Measurable L) (hDm : Measurable D) (hLp : ∀ z, 0 < L z)
    LC DC G (hG : 0 < G) (hLb : ∀ z, L z ≤ LC) (hDb : ∀ z, |D z| ≤ DC)
    (hE : Integrable 𝔓 𝔐 $ ν.prod μ ) :
    let ρ := μ.withDensity fun z => ENNReal.ofReal $ 𝔊 / G
    MemLp 𝔇 2 ρ ∧
       ∫ z, 𝔇 z ^2 ∂ρ ≤
        G⁻¹ * ∫ z, 𝔐 ∂ν.prod μ := by
  let M := 𝔓 𝔊
  let A := 𝔓 𝔎
  let E := fun z => ∫ ω, D 𝔄^2 / L 𝔄 ∂ν
  let R := 𝔇
  let ρ := μ.withDensity fun z => ENNReal.ofReal 𝔒
  have hM : Measurable M := hLm.stronglyMeasurable.integral_prod_left'.measurable
  have hR := posteriorMeanScore_measurable ν L D hLm hDm
  have hden z : 0 < M z := integral_likelihood_pos ν _
    𝔑 LC
    𝔍 hLp 𝔍 hLb
  have hiL z : Integrable 𝔍 L ν := by
    apply Integrable.of_bound (𝔑).aestronglyMeasurable LC
    exact Eventually.of_forall fun ω => by
      change ‖L 𝔄‖ ≤ LC
      rw [Real.norm_eq_abs, abs_of_nonneg (hLp _).le]
      exact hLb _
  have hiD z : Integrable 𝔍 D ν := by
    apply Integrable.of_bound (hDm.comp $ measurable_id.prodMk measurable_const ).aestronglyMeasurable DC
    simp_all
  have hEnergy : ∀ᵐ z ∂μ, 𝔅 ≤ 𝔈 := by
    filter_upwards [hE.prod_left_ae] with z hEz
    have hc := weighted_score_energy_contraction ν 𝔍 L 𝔍 D
      𝔍 hLp (hiL z) (hiD z) hEz $ hden z
    have halg : 𝔅 = G⁻¹ * (A z^2 / M z) := by
      dsimp only [R, posteriorMeanScore, A, M]
      field_simp
    aesop
  have hiE : Integrable 𝔓 𝔈 μ := hE.integral_prod_right.const_mul _
  have hweighted : Integrable 𝔓 𝔅 μ := by
    apply hiE.mono' ((hM.div_const _).mul $ hR.pow_const 2 ).aestronglyMeasurable
    filter_upwards [hEnergy] with z hz
    change ‖𝔅‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg $ mul_nonneg (div_nonneg (hden z).le hG.le) $ sq_nonneg _ ]
    exact hz
  have hdens := (hM.div_const G).ennreal_ofReal
  have hsquare : Integrable (fun z => R z^2) ρ := by
    apply (integrable_withDensity_iff_integrable_smul' hdens 𝔏).2
    simpa only [ENNReal.toReal_ofReal 𝔉, smul_eq_mul] using hweighted
  refine ⟨(memLp_two_iff_integrable_sq hR.aestronglyMeasurable).2 hsquare, ?_⟩
  rw [integral_withDensity_eq_integral_toReal_smul hdens 𝔏]
  simp_rw [ENNReal.toReal_ofReal 𝔉, smul_eq_mul]
  calc
    _ ≤ ∫ z, 𝔈 ∂μ := integral_mono_ae hweighted hiE hEnergy
    𝘿 := by rw [integral_const_mul, ← MeasureTheory.integral_prod_symm _ hE]
