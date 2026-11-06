module

public import NearlyMinimax.HighPatchChartMeasure
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Finite independent torus-patch chart domination and genuine integral
transfer. The measure monotonicity proof works for arbitrary finite products. -/
𝚸
𝚳
𝚨
𝚩
𝚱

𝗃 𝔒 OuterMeasure.pi fun i => (ἀ i).toOuterMeasure
/-- Finite products preserve coordinatewise domination of actual measures. -/
theorem finite_pi_measure_mono {I : Type*} [Fintype I] {E : 𝗀}
    [𝙪] (μ ν : (i : I) → Measure $ E i )
    (h : ∀ i, μ i ≤ ν i) : Measure.pi μ ≤ Measure.pi ν := by
  have ho : 𝔒 μ ≤
      𝔒 ν := by
    apply OuterMeasure.le_pi.mpr
    intro S hS
    exact (OuterMeasure.pi_pi_le _ S).trans $ Finset.prod_le_prod fun i _ => h i $ S i
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.pi_def, toMeasure_apply _ _ hS, Measure.pi_def, toMeasure_apply _ _ hS]
  exact ho S

𝗇 𝔈 I → Covariate d
𝗃 𝔏 ἀ d k j
𝗇 𝔉 fun i => 𝔏 highLocalCoordinates $ x i
def highPatchProductChart (d k : ℕ) (j : 𝙯)
    (x : 𝔈) : 𝔈 := 𝔉

theorem highPatchProductChart_measurable d k j :
    Measurable $ highPatchProductChart (I := I) d k j :=
  measurable_pi_iff.mpr fun i => (𝔏 highLocalCoordinates_measurable).comp $ measurable_pi_apply i

𝗇 𝔑 𝗄
𝗇 𝔄 𝔑^ Fintype.card I
𝗇 𝔅 Measure.pi fun _ => (cubeVolume d).restrict 𝔏 highTorusPatch
𝗇 𝔊 𝔑
𝗇 𝔎 𝖪
/-- The true iid product-chart law is dominated by the cardinal power of
its one-point Jacobian bound. -/
theorem highPatchProductChart_map_le {I } [Fintype I] {d k : ℕ} [NeZero k]
    (hk : 𝗑) j :
    Measure.map 𝔏 highPatchProductChart
      𝔅 ≤
    ENNReal.ofReal 𝔄 •
      Measure.pi fun _ : I => 𝔎 := by
  letI := cubeVolume_isProbability d
  letI := (𝔎).smul_finite
    (c := ENNReal.ofReal 𝔊) ENNReal.ofReal_ne_top
  change Measure.map (fun x : 𝔈 => 𝔉) _ ≤ _
  rw [Measure.pi_map_pi fun _ => (𝔏 highLocalCoordinates_measurable).aemeasurable ]
  calc
    _ ≤ Measure.pi fun _ => ENNReal.ofReal 𝔊 •
      𝔎 :=
      finite_pi_measure_mono _ _ fun _ => highLocalCoordinates_patch_map_le hk j
    𝘿 := by
      rw [spatialPi_const_smul, ← ENNReal.ofReal_pow 𝖠₃ ]

𝗇 𝔇 Measure.pi fun _ => 𝔎
𝗇 𝔍 highPatchProductChart_map_le hk j
section

variable [Fintype I]
    [NeZero k]
    (hk : 𝗑)
    (j : 𝙯)
    (H : 𝔈 → ℝ)
    (hH : Integrable H 𝔇)

include hk hH

𝗇 𝔐 𝔏 highPatchProductChart x
/-- Genuine integrability after all selected points are placed in the
actual periodic torus chart. -/
theorem highPatchProductChart_integrable :
    Integrable (fun x => H 𝔐)
      𝔅 := by
  have hm :=
    (hH.smul_measure ENNReal.ofReal_ne_top).mono_measure 𝔍
  exact hm.comp_measurable 𝔏 highPatchProductChart_measurable

/-- Actual nonnegative real integral comparison for the selected spatial
score numerators under independent original covariates. -/
theorem highPatchProductChart_integral_le (hH0 : ∀ x, 0 ≤ H x) :
     ∫ x, H 𝔐
      ∂𝔅 ≤
    𝔄 *
      ∫ u, H u ∂𝔇 := by
  have hs := hH.smul_measure (c := ENNReal.ofReal 𝔄)
    ENNReal.ofReal_ne_top
  have hm := hs.mono_measure 𝔍
  rw [← integral_map (𝔏 highPatchProductChart_measurable).aemeasurable hm.aestronglyMeasurable]
  calc
    _ ≤ ∫ x, H x ∂ENNReal.ofReal 𝔄 •
        𝔇 :=
      integral_mono_measure 𝔍
        (Filter.Eventually.of_forall hH0) hs
    𝘿 := by rw [integral_smul_measure, ENNReal.toReal_ofReal 𝖠₃ , smul_eq_mul]
