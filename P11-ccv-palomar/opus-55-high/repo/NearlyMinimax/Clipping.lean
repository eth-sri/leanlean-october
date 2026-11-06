module

public import NearlyMinimax.TernaryMeasure
public import NearlyMinimax.Risk
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Exact restriction of the original minimax problem to bounded estimators.
This keeps extended-valued losses for arbitrary estimators and proves that
clipping to the effective variance interval preserves the minimax value.
-/

𝚫
𝚮
𝚨

def effectiveVarianceUpper (C : ModelConstants d) : ℝ :=
  min C.varianceUpper $ Real.sqrt C.fourthBound

𝗇 𝔈 𝚠
𝗇 𝔏 clip C.varianceLower (effectiveVarianceUpper C) $ T.val z
def clippedEstimator (C : ModelConstants d) (T : 𝔈) :
    𝔈 :=
  ⟨fun z => 𝔏,
    (clip_lipschitz _ _).continuous.measurable.comp T.property⟩

𝗇 𝔉 clippedEstimator C T
𝗇 𝔊 𝙸₁
theorem clippedEstimator_mem_Icc C
    (T : 𝔈) z :
    (𝔉).val z ∈ 𝔊 :=
  clip_mem_Icc (effective_variance_interval_nondegenerate C).le

𝗇 𝔄 𝔏 - θ.variance
theorem clippedEstimator_risk_le C
    (T : 𝔈) θ (hθ : 𝙟) :
    meanSquaredRisk 𝔉 θ ≤ meanSquaredRisk T θ := by
  have hV := admissible_variance_effective_interval C θ hθ
  apply lintegral_mono
  intro z
  apply ENNReal.ofReal_le_ofReal
  have h := clip_error_le hV.1 hV.2 (x := T.val z)
  change |𝔄| ≤
    |𝗻₂| at h
  change 𝔄 ^ 2 ≤ _
  nlinarith [sq_abs 𝔄,
    sq_abs 𝗻₂, abs_nonneg 𝔄]

theorem clippedEstimator_worstCaseRisk_le C
    (T : 𝔈) :
    worstCaseRisk C 𝔉 ≤ worstCaseRisk C T := by
  apply iSup_le
  intro θ
  exact (clippedEstimator_risk_le C T θ.val θ.property).trans
    $ le_iSup (fun θ => meanSquaredRisk T θ.val) θ

/-- The bounded estimator class still quantifies all measurable statistics
with values in the effective variance interval. -/
abbrev BoundedEstimator (C : ModelConstants d) (n : ℕ) :=
  {T : 𝔈 // ∀ z, T.val z ∈ 𝔊}

𝗇 𝔍 𝖧₂
𝗇 𝔎 𝙌
section

𝛇

theorem minimaxRisk_eq_inf_bounded n :
    minimaxRisk C n = ⨅ T : 𝔍, 𝚡₂ := by
  apply le_antisymm
  · apply le_iInf
    intro T
    exact minimaxRisk_le_worstCaseRisk C T.val
  · apply le_iInf
    intro T
    exact (iInf_le (fun B : 𝔍 => worstCaseRisk C B.val)
      ⟨𝔉, clippedEstimator_mem_Icc C T⟩).trans
      $ clippedEstimator_worstCaseRisk_le C T

theorem boundedEstimator_memLp (T : 𝔍) (μ : Measure 𝔎)
    [IsFiniteMeasure μ] p : MemLp T.val.val p μ := by
  apply MemLp.of_bound T.val.property.aestronglyMeasurable $ effectiveVarianceUpper C
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, 𝗼₂]
  grind

end

𝗇 𝔅 𝙰 ^ 2
𝗇 𝔇 T.val.val z - θ.variance
theorem boundedEstimator_risk_le_diameter (C : ModelConstants d)
    (T : 𝔍) θ (hθ : 𝙟) :
    meanSquaredRisk T.val θ ≤
      ENNReal.ofReal 𝔅 := by
  let _ := sampleLaw_isProbability C θ hθ n
  have hV := admissible_variance_effective_interval C θ hθ
  change θ.variance ∈ 𝔊 at hV
  have hp : ∀ z, 𝔇 ^ 2 ≤
      𝔅 := by
    intro z
    have habs : |𝔇| ≤ 𝙰 := by
      grind
    nlinarith [sq_abs 𝔇, abs_nonneg 𝔇]
  calc
    meanSquaredRisk T.val θ ≤ ∫⁻ _ : 𝔎,
        ENNReal.ofReal 𝔅 ∂𝗷 :=
      lintegral_mono fun z => ENNReal.ofReal_le_ofReal $ hp z
    𝘿 := 𝖢₄
