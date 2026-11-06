module

public import NearlyMinimax.IncrementPilotKernels
public import NearlyMinimax.IncrementCoordinateBounds
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Joint Borel derivative coefficient fields for actual dyadic pilots. -/
open MeasureTheory Matrix
𝚺
𝚨
𝚭
set_option synthInstance.maxHeartbeats 300000
𝚩

𝗃 𝔖 Fin ἀ → ℝ
𝗇 𝔄 fun _ : Fin k => 𝔖 p
𝗇 𝔗 ContinuousMultilinearMap ℝ 𝔄
instance finiteInputMultilinearMeasurableSpace
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    MeasurableSpace $ 𝔗 F := borel _

instance finiteInputMultilinearBorelSpace
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    BorelSpace $ 𝔗 F := ⟨rfl⟩

𝗇 𝔉 fun _ => 𝔖 p
instance finiteInputScalarMultilinearFiniteDimensional (p k : ℕ) :
    FiniteDimensional ℝ $ 𝔗 ℝ := by
  let e : ContinuousMultilinearMap ℝ 𝔉 ℝ →L[ℝ]
       (Fin k → Fin p) → ℝ := ContinuousLinearMap.pi fun σ =>
    ContinuousMultilinearMap.apply ℝ 𝔉 ℝ
       fun i => Pi.single (σ i) 1
  apply FiniteDimensional.of_injective e.toLinearMap
  intro H G he
  ext v
  change H.toMultilinearMap v = G.toMultilinearMap v
  rw [LiftL2.multilinear_coordinate_expansion H.toMultilinearMap,
    LiftL2.multilinear_coordinate_expansion G.toMultilinearMap]
  apply Finset.sum_congr rfl
  intro σ _
  have hc := congrFun he σ
  aesop

theorem rowFunctional_continuous : Continuous $ rowFunctional (r := r) := by
  unfold rowFunctional
  fun_prop

𝗇 𝔎 𝔖 r
theorem continuous_row_postcompose :
    Continuous fun z : 𝔎 ×
      𝔗 𝔎 =>
        (rowFunctional z.1).compContinuousMultilinearMap z.2 := ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ 𝔄
    𝔎 ℝ).continuous.comp $ rowFunctional_continuous.comp continuous_fst ).clm_apply continuous_snd

𝗇 𝔍 𝔖 q →L[ℝ] 𝔖 p
𝗇 𝔙 fun _ => z.2
theorem continuous_multilinear_pullback :
    Continuous fun z :
      𝔗 ℝ ×
        𝔍 =>
        z.1.compContinuousLinearMap 𝔙 := by
  change Continuous fun z :
      ContinuousMultilinearMap ℝ 𝔉 ℝ ×
        𝔍 =>
      (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
        (fun _ => 𝔖 q) 𝔉 ℝ 𝔙) z.1
  fun_prop

𝗇 𝔓 𝖼₁
𝗇 𝔔 dyadicIncrementRawMean θ j w.1
𝗇 𝔚 𝗣
𝗇 𝔅 fun w => (rowFunctional $ row w ).compContinuousMultilinearMap $ 𝗸₁ (incrementFinVector 𝔚 C.densityLower C.densityUpper 𝔓 y m) 𝔔
𝗇 𝔇 𝗸₁ (incrementFinScalar 𝔚 C.densityLower C.densityUpper 𝔓 y m $ row w ) 𝔔
𝗇 𝔈 𝙩
𝗇 𝔊 𝖳₂ w.1 y m (row w) k
𝗇 𝔏 Nonempty 𝘘
𝗇 𝔐 𝔚
𝗃 𝔛 fun w : 𝔈 => ἀ
/-- The anchor and arbitrary measurable physical row determine a Borel
global derivative field under the original admissible population law. -/
theorem dyadicIncrementKernel_field_measurable (C : ModelConstants d)
    [𝔏] θ (hθ : 𝙟)
    j y m k
    row
    (hrow : Measurable row) :
    Measurable 𝔛 𝔊 := by
  have hm : Measurable 𝔛 𝔔 :=
    (dyadicIncrementRawMean_measurable (ℓ := C.order) C θ hθ j).comp measurable_fst
  have hD := ((incrementFinVector_contDiff 𝔐
    C.densityLower C.densityUpper 𝔓 y m).continuous_iteratedFDeriv
      $ show 𝘪₂ from le_top ).measurable.comp hm
  have hscalar := continuous_row_postcompose.measurable.comp $ hrow.prodMk hD
  change Measurable 𝔅 at hscalar
  have heq : 𝔅 =
       fun w => 𝔇 := by
    funext w
    ext v
    exact (incrementFinScalar_iteratedFDeriv ..).symm
  rw [heq] at hscalar
  exact continuous_multilinear_pullback.measurable.comp
    $ hscalar.prodMk $ (incrementPilotCoordinate_measurable j).comp measurable_fst

𝗇 𝔑 𝖶₂
𝗇 𝔒 fun i _ => norm_nonneg _
𝗇 𝔘 R * D * k.factorial * 𝚇₁
/-- A finite level has a genuine bounded coefficient field on every
bounded-row, cube-supported parameter measure. This cap is used only to
justify Bochner integration; the sharper raw-energy estimate is separate. -/
theorem dyadicIncrementKernel_field_norm_bound (C : ModelConstants d)
    [𝔏] (θ : RegressionParameter d) (hθ : 𝙟)
    (j : ℕ) (y : ℝ) (hy : |y| ≤ C.holderBound) (m k : ℕ)
    (row : 𝔈 → 𝔖 𝔐)
    (M : Measure 𝔈) (R : ℝ) (hR : 𝖡₂)
    (hcube : 𝔑)
    (hrow : ∀ᵐ w ∂M, ∑ i, |row w i| ≤ R) :
    ∃ B : ℝ, 𝘶₁ ∧ ∀ᵐ w ∂M, ‖𝔊‖ ≤ B := by
  obtain ⟨D, A, hD, hA, hder⟩ := admissible_dyadic_increment_all_derivative_bound C
  obtain ⟨L, hL, hmap⟩ := incrementPilotCoordinate_uniform_bound j
  let B := 𝔘 * L ^ k
  refine ⟨max 1 B, 𝘏, ?_⟩
  filter_upwards [hcube, hrow] with w hw hr
  apply le_trans _ $ le_max_right ..
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans
  have hd : ‖𝔇‖ ≤ 𝔘 := by
    apply (hder θ hθ j w.1 hw y hy m k $ row w ).trans
    gcongr
  exact mul_le_mul hd ((Finset.prod_le_prod₀ 𝔒 fun i _ => hmap _ hw ).trans_eq 𝖢₄ ) (Finset.prod_nonneg 𝔒) 𝖠₃

theorem dyadicIncrementKernel_weighted_integrable (C : ModelConstants d)
    [𝔏] (θ : RegressionParameter d) (hθ : 𝙟)
    (j : ℕ) (y : ℝ) (hy : |y| ≤ C.holderBound) (m k : ℕ)
    (row : 𝔈 → 𝔖 𝔐)
    (hrowMeas : Measurable row) (M : Measure 𝔈) [IsFiniteMeasure M]
    R (hR : 𝖡₂) (hcube : 𝔑)
    (hrow : ∀ᵐ w ∂M, ∑ i, |row w i| ≤ R) (ν : 𝔈 → ℝ)
    (hν : MemLp ν 2 M) :
    Integrable (fun w => ν w • 𝔊) M := by
  obtain ⟨B, _, hcap⟩ := dyadicIncrementKernel_field_norm_bound C θ hθ j y hy m k row M R hR hcube hrow
  exact (hν.integrable 𝖠₄ ).smul_bdd B
    (dyadicIncrementKernel_field_measurable C θ hθ j y m k row hrowMeas).aestronglyMeasurable hcap
