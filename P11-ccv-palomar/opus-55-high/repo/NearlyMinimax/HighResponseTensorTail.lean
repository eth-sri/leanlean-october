module

public import NearlyMinimax.HighSeparatedScoreBounds
public import NearlyMinimax.HighUnionScore
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Genuine all-count Taylor bounds for arbitrary finite density-response
atom tensors and their true absolute positive reference law. Both ordinary
and fine three-point density selectors are instances of these tensors. -/
𝚸
𝚨
𝚩
𝛈
𝚬

𝗇 𝔅 J × 𝗧₂
𝗇 𝔗 highResponseMarkAtom C q
𝗃 𝔚 coefficientReset c (𝔗 ἀ).2
𝗇 𝔇 𝔚 r (𝔗 r).1
𝗇 𝔘 𝖨 φ
𝗇 𝔊 fun v => 𝔘 v y
𝗇 𝔏 𝙛
𝗇 𝔑 𝙔
𝗇 𝔒 𝘀
𝗇 𝔔 𝔘
𝗇 𝔜 ∑ γ, φ i γ*v γ
𝗇 𝔠 𝙸
𝗇 𝔡 𝗳
𝗇 𝔢 𝔚 e.2 (𝔗 e.2).1
𝗇 𝔣 pPlus^n * highSeparatedDerivativeBudget a ρ
𝗃 𝔥 ἀ q hn C a V η ρ pPlus hC ha hη hρ hηρ hpPlus weights
section
variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

𝗇 𝔙 𝗨₂ A
𝗇 𝔄 ∑ e : J × 𝗧₂, weights e.1 * 𝔙 e.2 * (∏ i, pReset e.1 i) * 𝔘 𝔢 y
𝗇 𝔐 ∏ i, pReset e i
𝗇 𝔟 fun _ => A
theorem responseTensor_slice_all_count_bound q (hn : 𝗚)
    C a V η ρ pPlus (hC : 𝙴) (ha : 𝙆) (hη : 𝗼)
    (hρ : 𝗛₁) (hηρ : η ≤ 𝔠) (hpPlus : 𝗊₂)
    (weights : 𝙝) A (pReset : J → 𝔑)
    (g w : 𝔑) φ c
    (hc : ∑ γ, |c γ| ≤ 𝔡) (hg : ∀ i, |g i| ≤ 𝔠) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : 𝔏, ∑ γ, |v γ| ≤ 𝔡 → ∀ i, |𝔜| ≤ 1)
    (hp : ∀ f , |f| ≤ ρ → 𝔒)
    (hReset : ∀ e i, |pReset e i| ≤ pPlus) y :
    |𝔄| ≤
       𝔣 * 𝚍 * 𝙎 *
        ∑ e : 𝔅, |weights e.1 * 𝔙 e.2| := by
  have he : 𝔄 =
      highDensityResponseAction q C weights 𝔟 c
        (fun e => 𝔐) 𝔊 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro e _
    have hh r :
        weights e * 𝔙 r * 𝔐 *
          𝔔
            𝔇 y =
         weights e*𝔐 * (𝔙 r *
          𝔔
            𝔇 y) := 𝖢₃
    simp only [hh, ← Finset.mul_sum]
    rw [highResponseMark_action q C A c 𝔊]
  rw [he]
  apply (𝔥 high_density_response_product_abs_bound 𝔟 pReset g w φ c hc hg hw hφ hp hReset y).trans_eq
  rw [Fintype.sum_prod_type]
  simp
  simp_rw [← Finset.mul_sum]
  rw [highResponseMark_variation q C A]
  unfold highResponsePacketCost highLocalDerivativeConstant highSeparatedDerivativeBudget
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  ring

end

section Reference
variable {ι J Z : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace Z]

𝗇 𝔖 Z × 𝔅
def responseTensorWeight (q : ℕ) (C : ℝ) (weights : 𝙝)
    (A : Z → ι → 𝔏) (e : 𝔖) : ℝ :=
  weights e.2.1 * 𝗨₂ (A e.1) e.2.2

𝗇 𝔈 responseTensorWeight q C weights A
𝗇 𝔤 𝔚 e.2.2 (𝔗 e.2.2).1
𝗇 𝔉 𝔤
𝗇 𝔍 𝔣 * 𝙒^2 * 𝙎
𝗇 𝔎 ∏ i, pReset e.1 e.2.1 i
𝗇 𝔓 𝔗 r
𝗃 𝔛 ἀ (σ.prod Measure.count) 𝔈
𝗇 𝔞 𝘕₂
/-- Actual absolute-reference all-count raw response action is bounded by
its true variation mass and an η² Taylor factor. The variation is an
integral of the constructed signed atom weights. -/
theorem responseTensor_reference_all_count_bound
    (σ : Measure Z) [IsFiniteMeasure σ] (q : ℕ) (hn : 𝗚)
    (C a V η ρ pPlus : ℝ) (hC : 𝙴) (ha : 𝙆) (hη : 𝗼)
    (hρ : 𝗛₁) (hηρ : η ≤ 𝔠) (hpPlus : 𝗊₂)
    (weights : 𝙝) (A : Z → ι → 𝔏)
    (hm : Measurable 𝔈)
    (hi : Integrable 𝔈 $ σ.prod Measure.count )
    (hpos : 0 < 𝔛 signedMarkMass)
    (pReset : Z → J → 𝔑)
    (hmReset : ∀ e i, Measurable fun ζ => pReset ζ e i )
    (hReset : ∀ ζ e i, |pReset ζ e i| ≤ pPlus)
    (g w : 𝔑) (φ : Fin n → 𝔏) (c : 𝔏)
    (hc : ∑ γ, |c γ| ≤ 𝔡) (hg : ∀ i, |g i| ≤ 𝔠) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : 𝔏, ∑ γ, |v γ| ≤ 𝔡 → ∀ i, |𝔜| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → 𝔒)
    (y : 𝙈) :
    |highMarkedResponseAction
      𝔛 absoluteMarkLaw
      𝔛 absoluteActivation a V η
      (fun e => pReset e.1 e.2.1)
      (fun e => 𝔉)
      g w φ y| ≤
      𝔍 *
        𝔛 signedMarkMass := by
  let ν : Measure 𝔖 := σ.prod Measure.count
  let W := 𝔈
  let Φ : 𝔏 → ℝ := 𝔊
  let O : 𝔖 → ℝ := fun e => 𝔎 *
    Φ 𝔉
  let K := 𝔍
  have hResetJoint i : Measurable fun e : 𝔖 => pReset e.1 e.2.1 i :=
    measurable_from_prod_countable_left fun e => hmReset e.1 i
  have hCoef γ : Measurable fun e : 𝔖 =>
      𝔤 γ :=
    (measurable_of_countable fun e : 𝔅 =>
      𝔢 γ ).comp measurable_snd
  have hO : Measurable O := (Finset.measurable_fun_prod _ fun i _ => hResetJoint i ).mul
    $ highMarkedResponseProduct_measurable a V η _ hCoef g w φ y
  have hΦ (r : 𝗧₂) :
      |Φ 𝔇| ≤ 1 := by
    have hb := coefficientReset_mem_ball C c (𝔓).2
      (𝔓).1 (responseNode_mem_unit q r.2.2) hc
      $ covarianceAtom_mem_ball C hC _ _ _ _
    apply highMarkedResponseProduct_abs_le_one a V η ha.ne' g w φ _
    intro i b
    apply hp _
    have hprof := hφ _ hb i
    have hh : |𝗌₂*(∑ γ, φ i γ*coefficientReset c
        (𝔓).2 (𝔓).1 γ)| ≤ η := by
      rw [abs_mul,abs_mul,abs_of_nonneg hη]
      have := mul_le_mul (hw i) hprof (abs_nonneg _) (by norm_num : 𝙋 ≤ 1)
      nlinarith
    exact (abs_add_le _ _).trans 𝖤₃
  have hOb e : ‖O e‖ ≤ pPlus^n := by
    change |𝔎*Φ _| ≤ _
    rw [abs_mul]
    exact (mul_le_mul (finite_density_product_abs_bound _ pPlus hpPlus $ hReset e.1 e.2.1 )
      (hΦ e.2.2) (abs_nonneg _) 𝖠₃ ).trans_eq $ mul_one _
  have hWO := hi.mul_bdd hO.aestronglyMeasurable $ Filter.Eventually.of_forall hOb
  have hSlice ζ : |∫ e : 𝔅, W 𝔞*O 𝔞 ∂Measure.count| ≤
      K * ∫ e : 𝔅, |W 𝔞| ∂Measure.count := by
    simp only [integral_count]
    simpa only [W,O,Φ,K,responseTensorWeight,mul_assoc] using
      𝔥 responseTensor_slice_all_count_bound (A ζ) (pReset ζ) g w φ c hc hg hw hφ hp (hReset ζ) y
  unfold highMarkedResponseAction
  have he : (fun e => absoluteActivation ν W e * 𝔎 *
      𝔔
        𝔉 y) =
       fun e => absoluteActivation ν W e * O e := 𝖥₄
  rw [he,absoluteMarkLaw_activation_integral ν W hm hpos O,integral_prod _ hWO]
  apply abs_integral_le_integral_abs.trans
  apply (integral_mono hWO.integral_prod_left.abs (hi.abs.integral_prod_left.const_mul K) hSlice).trans_eq
  rw [integral_const_mul, ← integral_prod _ hi.abs]
  rfl
