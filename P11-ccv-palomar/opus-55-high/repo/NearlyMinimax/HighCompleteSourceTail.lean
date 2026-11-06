module

public import NearlyMinimax.HighSourceRowTail
public import NearlyMinimax.HighUnionScorePrimitives
public import RoughRegime.Macro


@[expose] public section
set_option hygiene false

/-! The genuine complete-source all-count raw response numerator bound.
Every source row is integrated on its actual positive reference law;
the variance derivative is subtracted exactly once after their union. -/
noncomputable section
𝚸
𝚨
𝛀
set_option maxHeartbeats 1800000
𝚬
𝚿

𝗇 𝔖 Fin n → ℝ
𝗇 𝔣 ι → ℝ
𝗇 𝔤 η^2
def highMarkedLocalScoreNumerator [Fintype ι] [MeasurableSpace E]
    (π : Measure E) (activation : E → ℝ) (a V η : ℝ)
    (p : 𝔖) (pReset : E → 𝔖) (cReset : E → 𝔣)
    (g w : 𝔖) (φ : Fin n → 𝔣) (c : 𝔣) (y : Fin n → Fin 3) : ℝ :=
  highMarkedResponseAction π activation a V η pReset cReset g w φ y -
    𝔤*(∏ u, p u)*∑ u, w u ^2*highResponseVarianceTerm a V η g w φ c y u

𝗃 𝔬 ∑ γ, φ u γ*ἀ γ
𝗇 𝔇 𝔬 v
𝗇 𝔏 ∀ y, 0 ≤ ternaryMass a f V y
𝗇 𝔔 ρ/2
𝗇 𝔚 highResponseProduct a V η g w φ
𝗇 𝔨 η*w u
theorem highResponseProduct_ball_abs_le_one [Fintype ι]
    (C a V η ρ : ℝ) (ha : a ≠ 0) (hη : 0 ≤ η) (hηρ : η ≤ 𝔔)
    (g w : 𝔖) φ
    (hg : ∀ u, |g u| ≤ 𝔔) (hw : ∀ u, |w u| ≤ 1)
    (hφ : ∀ v : 𝔣, ∑ γ, |v γ| ≤ C⁻¹ → ∀ u, |𝔇| ≤ 1)
    (hp : ∀ f , |f| ≤ ρ → 𝔏)
    v (hv : ∑ γ, |v γ| ≤ C⁻¹) y :
    |𝔚 v y| ≤ 1 := by
  apply highMarkedResponseProduct_abs_le_one a V η ha g w φ v
  intro u b
  apply hp _
  change |g u+𝔨*𝔇| ≤ ρ
  have hh : |𝔨*𝔇| ≤ η := by
    rw [abs_mul,abs_mul,abs_of_nonneg hη]
    have ht := mul_le_mul (hw u) (hφ v hv u) (abs_nonneg _) $ by norm_num
    nlinarith
  grind

section Complete
variable {d k D M q n : ℕ} [NeZero d] [NeZero k] [LinearOrder $ HighWindowLabels d k ]
  (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
  (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
  (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)

local notation "R" => completeSourceRows C k D M q Cfr lam ℓ N μ
include hD hq hM hCfr hℓ hℓN

𝗃 𝔭 ἀ C R
𝗇 𝔦 𝔭 highUnionSourceResetDensity j h
𝗇 𝔙 𝔦 e $ x u
𝗇 𝔄 fun e u => 𝔙
set_option hygiene false
𝗃 𝔞 ἀ d D M q ad bd Cfr lam ℓ N μ
𝗇 𝔅 𝔞 sourceRowDensityProj i e
𝗇 𝔉 highUnionLaw R $ highCenterMix C
𝗇 𝔊 highUnionActivation R $ highCenterMix C
𝗇 𝔍 𝔭 highUnionSourceResetCoefficient j h
𝗇 𝔎 (lt_trans zero_lt_one C.one_lt_densityUpper).le
𝗇 𝔐 completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN
𝗇 𝔑 (𝔭 highUnionSourceState h).2 j
𝗇 𝔒 ∏ u, 𝔙
𝗇 𝔜 𝔞 sourceRowDensityLift r₀ i
𝗇 𝔗 𝔜 𝔅
𝗇 𝔘 highMarkedResponseAction 𝔉 𝔊 a V η 𝔄 𝔍 g w φ y
𝗇 𝔟 HighFrameIndex d D
𝗇 𝔠 C.densityUpper^n
𝗇 𝔡 highRowTotalMass (R).rowMass
𝗇 𝔢 (highUnionSourceResetDensity_measurable C R G j h).comp
𝗇 𝔥 x u ∈ highTorusPatch d k j
𝗃 𝔪 ἀ d k D M q
𝗃 𝔫 (R).rowSlope j i ἀ (x u)*_
𝗃 𝔮 𝔪 ἀ ad bd Cfr lam ℓ N μ r₀
theorem completeSourceResponseAction_all_count_bound (hn : 1 ≤ n)
    j
    h
    a V η ρ (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hηρ : η ≤ 𝔔)
    (x : Fin n → Covariate d) g w
    φ
    (hg : ∀ u, |g u| ≤ 𝔔) (hw : ∀ u, |w u| ≤ 1)
    (hφ : ∀ v : 𝔟 → ℝ, ∑ γ, |v γ| ≤ Cfr⁻¹ →
      ∀ u, |𝔇| ≤ 1)
    (hp : ∀ f , |f| ≤ ρ → 𝔏) y :
    |𝔘| ≤
       𝔠*highSeparatedDerivativeBudget a ρ*n^2*𝔤 *
        𝔡 := by
  let ad := C.densityLower+1/M
  let bd := C.densityUpper-1/M
  let G := 𝔐
  have hCf : 0 < Cfr := by linarith
  obtain ⟨had,hadbd⟩ := high_source_interval_numeric C M hM
  have hpos := 𝔪 sourceRowMass_positive_actual hD hq ad bd had hadbd Cfr hCf
    lam ℓ N μ hℓ hℓN
  letI : StandardBorelSpace $ HighUnionMark 𝔞 SourceRowMark :=
    highUnionMark_standardBorel
  let c := 𝔑
  have hc := 𝔭 highUnionSourceState_coefficient_ball G h j
  let β₀ : 𝔟 := ⟨fun _ => 0,by simp⟩
  let r₀ : HighResponseMarkIndex 𝔟 q := ((β₀,β₀),(false,false),0)
  let reset :=
    fun i z u => 𝔦
      (Sum.inl ⟨i,𝔜 z⟩) $ x u
  have hresetMeas (i) (u) : Measurable fun z => reset i z u := 𝔢
      $ (measurable_inl.comp $ (rowSigmaMk_measurable i).comp
        $ 𝔞 sourceRowDensityLift_measurable r₀ i ).prodMk measurable_const
  have hresetBound (i) (z) (u) : |reset i z u| ≤ C.densityUpper :=
    highUnionSourceResetDensity_abs_le C R G j h ..
  have hirrel (i) e (u) :
      𝔦 (Sum.inl ⟨i,e⟩) (x u) =
      reset i 𝔅 u := by
    dsimp only [reset]
    unfold highUnionSourceResetDensity
    unfold highUnionSourceDensity
    rw [highUnionSourceState_append,highUnionSourceState_append]
    change (if 𝔥 then 𝔫 e+(R).rowIntercept i e else _) =
       if 𝔥 then 𝔫 𝔗+
        (R).rowIntercept i 𝔗 else _
    simp only [completeSourceRows]
    rw [𝔮 sourceRow_density_projection_slope j i e $ x u ,
      𝔮 sourceRow_density_projection_intercept i e]
  let O := fun e => 𝔒*
    𝔚 (𝔭 highUnionSourceResetCoefficient j h e) y
  have hmO : Measurable O := (Finset.measurable_fun_prod _ fun u _ =>
    𝔢
      $ measurable_id.prodMk measurable_const ).mul
        $ highMarkedResponseProduct_measurable a V η _
          (highUnionSourceResetCoefficient_measurable C R G j h) g w φ y
  have hOb (e) : ‖O e‖ ≤ 𝔠 := by
    have hResponse := highResponseProduct_ball_abs_le_one Cfr a V η ρ ha.ne' hη hηρ
      g w φ hg hw hφ hp _ (highUnionResponseReset_ball R Cfr hCf G.vector_ball G.time_interval e c hc) y
    change |𝔒*𝔚 _ y| ≤ _
    rw [abs_mul]
    exact (mul_le_mul (finite_density_product_abs_bound _ C.densityUpper 𝔎
       fun u => highUnionSourceResetDensity_abs_le C R G j h e $ x u ) hResponse
        (abs_nonneg _) $ pow_nonneg 𝔎 _ ).trans_eq $ mul_one _
  have he : 𝔘 =
      ∑ i, highMarkedResponseAction ((R).rowLaw i) ((R).rowActivation i) a V η
        (fun e => reset i 𝔅)
        (fun e => coefficientReset c ((R).rowVector i e) $ (R).rowTime i e ) g w φ y := by
    unfold highMarkedResponseAction
    simp_rw [mul_assoc]
    rw [𝔭 highUnionSource_bounded_action G hpos O hmO 𝔠 hOb]
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [] with e
    simp only [O,hirrel,highUnionSourceResetCoefficient,highUnionResponseReset,
      highUnionResponseVector,highUnionResponseTime,Sum.elim_inl,c]
  rw [he]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  apply (Finset.sum_le_sum fun i _ =>
    𝔪 sourceRow_reference_all_count_bound hn ad bd Cfr lam ℓ N μ a V η ρ C.densityUpper
      hCf ha hη hρ hηρ 𝔎 hpos i (reset i) (hresetMeas i) (hresetBound i)
      g w φ c hc hg hw hφ hp y ).trans_eq
  exact (Finset.mul_sum ..).symm

𝗇 𝔧 𝔭 highUnionSourceDensity h $ x u
𝗇 𝔈 fun u => 𝔧
𝗇 𝔓 𝔨*𝔬 c
𝗇 𝔛 highMarkedLocalScoreNumerator 𝔉 𝔊 a V η 𝔈 𝔄 𝔍 g w φ
theorem completeSourceNumerator_all_count_exponential_bound (hn : 1 ≤ n)
    j
    h
    a V η ρ (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hηρ : η ≤ 𝔔)
    (x : Fin n → Covariate d) g w
    φ
    (hg : ∀ u, |g u| ≤ 𝔔) (hw : ∀ u, |w u| ≤ 1)
    (hφ : ∀ v : 𝔟 → ℝ, ∑ γ, |v γ| ≤ Cfr⁻¹ →
      ∀ u, |𝔇| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → 𝔏) y :
    |𝔛 𝔑 y| ≤
       highSeparatedScoreExponentialConstant a ρ C.densityUpper 1 1 ^n *
        𝔤*(𝔡+1) := by
  let G := 𝔐
  let c := 𝔑
  let B := 𝔡
  have hc := 𝔭 highUnionSourceState_coefficient_ball G h j
  have hpCurrent (u) (b) : 0 ≤ ternaryMass a (coefficientRegression η g w φ c u) V b := by
    apply hp _
    have hv := hφ c hc u
    change |g u+𝔓| ≤ ρ
    have hh : |𝔓| ≤ η := by
      rw [abs_mul,abs_mul,abs_of_nonneg hη]
      have ht := mul_le_mul (hw u) hv (abs_nonneg _) $ by norm_num
      nlinarith
    grind
  have hIncoming (u) : |𝔧| ≤ C.densityUpper := by
    have hi := 𝔭 highUnionSourceDensity_coarse_interval G h $ x u
    rw [abs_of_nonneg $ C.densityLower_pos.le.trans hi.1 ]
    exact hi.2
  have haction := completeSourceResponseAction_all_count_bound C hD hq hM Cfr lam ℓ N μ
    hCfr hℓ hℓN hn j h a V η ρ ha hη hρ hηρ x g w φ hg hw hφ hp y
  have hcorrection := high_response_variance_correction_abs_bound hn a V η C.densityUpper
    ha 𝔎 𝔈 g w φ c
    hw hIncoming hpCurrent y
  have hraw : |𝔛 c y| ≤
      𝔠*(highSeparatedDerivativeBudget a ρ*B+1/a^2)*n^2*𝔤 := by
    unfold highMarkedLocalScoreNumerator
    grind
  apply hraw.trans
  simpa only [mul_one,div_one] using highSeparated_score_budget_absorb n hn a ρ C.densityUpper
    1 1 η B 𝔎 (by norm_num) (by norm_num) G.total_positive.le
