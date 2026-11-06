module

public import NearlyMinimax.FinePairDensityPacket
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The actual fine-pair density packet tensored with the original finite
response reset measure, retaining the genuine field and scale marks. -/
𝚸
𝚮
𝚨
𝚾
𝚩

abbrev FinePairPacketIndex (ι : Type*) (M q : ℕ) := FinePairDensityIndex M × 𝗧₂

section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

𝗇 𝔇 Z → ι → 𝙛
𝗇 𝔎 FinePairPacketIndex ι M q
𝗃 𝔣 ἀ a b M
𝗇 𝔤 Z × 𝔎
def finePairPacketWeight (a b : ℝ) (M q : ℕ) (C : ℝ) (A : 𝔇)
    (e : 𝔤) : ℝ :=
  𝔣 finePairDensityWeight e.2.1 * 𝗨₂ (A e.1) e.2.2

𝗇 𝔄 𝙚
𝗃 𝔭 𝔣 ἀ q C A
𝗇 𝔅 𝔭 finePairPacketWeight 𝚊
𝗇 𝔧 fun ζ => 𝔅
theorem finePairPacketWeight_slice_measurable a b M q C
    (A : 𝔇) (hA : 𝔄)
    h : Measurable 𝔧 := by
  dsimp [finePairPacketWeight, highResponseMarkWeight, covarianceWeight]
  fun_prop

𝗇 𝔓 𝔭 finePairPacketWeight
𝗇 𝔗 𝔭 finePairPacketWeight_slice_measurable hA
theorem finePairPacketWeight_measurable a b M q C
    (A : 𝔇) (hA : 𝔄) :
    Measurable 𝔓 :=
  measurable_from_prod_countable_left 𝔗

𝗇 𝔍 𝙧
theorem finePairPacketWeight_slice_integrable (σ : Measure Z) a b M q C
    A (hA : 𝔄)
    (hcost : 𝔍) (h : 𝔎) :
    Integrable 𝔧 σ := 𝘒 $ 𝔣 finePairDensityWeight h.1

𝗃 𝔢 ἀ σ a b M q C A hA hcost
theorem finePairPacketWeight_integrable (σ : Measure Z) [IsFiniteMeasure σ]
    a b M q C (A : 𝔇)
    (hA : 𝔄) (hcost : 𝔍) :
    Integrable 𝔓 $ σ.prod Measure.count :=
  joint_finite_integrable σ _ 𝔗
    𝔢 finePairPacketWeight_slice_integrable

def finePairPacketSignedMeasure (σ : Measure Z) (a b : ℝ) (M q : ℕ) (C : ℝ)
    (A : 𝔇) : SignedMeasure 𝔤 :=
  (σ.prod Measure.count).withDensityᵥ 𝔓

𝗇 𝔏 finePairPacketSignedMeasure σ a b M q C A
𝗇 𝔐 𝚊
𝗇 𝔙 𝔢 finePairPacketWeight_integrable
𝗇 𝔚 fun e => hb e.1 e.2
theorem finePairPacketSignedMeasure_integral (σ : Measure Z) [IsFiniteMeasure σ]
    a b M q C A
    (hA : 𝔄) (hcost : 𝔍)
    (f : 𝔤 → ℝ) (hf : ∀ h, Measurable fun ζ => f 𝔐 )
    L (hb : ∀ ζ h, ‖f 𝔐‖ ≤ L) :
     ∫ᵛ e, f e ∂<•𝔏 =
      ∫ ζ, ∑ h : 𝔎, 𝔅 * f 𝔐 ∂σ := by
  have hm := measurable_from_prod_countable_left hf
  have hw := 𝔙
  rw [finePairPacketSignedMeasure, signedDensity_integral _ _ hw
    (𝔭 finePairPacketWeight_measurable hA) f hm L 𝔚,
    integral_prod _ $ hw.mul_bdd hm.aestronglyMeasurable $ Filter.Eventually.of_forall 𝔚 ]
  simp

𝗇 𝔖 𝔣 finePairDensityWeight h
𝗇 𝔥 𝖵
𝗇 𝔦 𝘖
theorem finePairPacketWeight_variation a b M q C
    A (ζ : Z) :
     ∑ h : 𝔎, |𝔅| =
      (∑ h : FinePairDensityIndex M, |𝔖|) *
        (∑ h : Fin 𝔥, |𝘐₁|) * 𝔦 * separatedMatrixCost A ζ := by
  rw [Fintype.sum_prod_type]
  simp only [finePairPacketWeight, abs_mul]
  simp_rw [← Finset.mul_sum, highResponseMark_variation]
  rw [← Finset.sum_mul]
  unfold separatedMatrixCost
  ring

theorem finePairPacketSignedMeasure_totalVariation (σ : Measure Z) [IsFiniteMeasure σ]
    a b M q C (A : 𝔇)
    (hA : 𝔄) (hcost : 𝔍) :
    ((𝔏).variation univ).toReal =
      (∑ h : FinePairDensityIndex M, |𝔖|) *
        (∑ h : Fin 𝔥, |𝘐₁|) * 𝔦 *
           ∫ ζ, separatedMatrixCost A ζ ∂σ := by
  have hw := 𝔙
  rw [finePairPacketSignedMeasure, Measure.variation_withDensityᵥ hw,
    𝚒₂]
  simp
  rw [← integral_norm_eq_lintegral_enorm hw.aestronglyMeasurable, integral_prod _ hw.norm]
  simp only [integral_count, Real.norm_eq_abs, finePairPacketWeight_variation]
  rw [integral_const_mul]

𝗇 𝔟 𝔣 finePairDensityAtom
𝗇 𝔡 highResponseMarkAtom C q
𝗇 𝔩 𝙛
𝗃 𝔫 coefficientReset c (𝔡 ἀ).2
𝗃 𝔮 (𝔡 ἀ).1
def finePairPacketObservable (a b : ℝ) (M q : ℕ) (C : ℝ) (c : 𝔩)
    (G : Z → ℝ → 𝘓) (Φ : 𝔩 → ℝ)
    (e : 𝔤) : ℝ :=
  G e.1 (𝔟 e.2.1).1 (𝔟 e.2.1).2 *
    Φ (𝔫 e.2.2 𝔮 e.2.2)

𝗇 𝔈 G ζ (𝔣 finePairDensityAtom h).1 (𝔣 finePairDensityAtom h).2
𝗇 𝔉 𝗔 (A ζ) c Φ
𝗇 𝔑 𝔫 v 𝔮 v
𝗇 𝔔 ∫ᵛ e, G ζ e.1 e.2 ∂<•𝔣 finePairDensitySignedRule
𝗇 𝔛 𝔣 finePairPacketObservable q C c
𝗇 𝔨 𝗨₂ (A ζ) v
theorem finePairPacketObservable_finite_action a b M q C
    A c G Φ (ζ : Z) :
     ∑ h : 𝔎, 𝔅 *
      𝔛 G Φ 𝔐 =
      𝔔 * 𝔉 := by
  rw [Fintype.sum_prod_type, finePairDensitySignedRule, atomicSignedRule_integral]
  simp only [finePairPacketWeight, finePairPacketObservable]
  have he h v :
      𝔖 * 𝔨 *
      (𝔈 *
        Φ 𝔑) =
       𝔖 * 𝔈 *
        (𝔨 *
          Φ 𝔑) := 𝖢₃
  simp_rw [he, ← Finset.mul_sum, highResponseMark_action]
  rw [← Finset.sum_mul]

𝗇 𝔒 𝔫 h 𝔮 h
𝗃 𝔬 ∫ᵛ e, 𝔛 ἀ Φ e ∂<•𝔏
theorem finePairPacketSignedMeasure_factor_integral (σ : Measure Z) [IsFiniteMeasure σ]
    a b M q C A
    (hA : 𝔄) (hcost : 𝔍)
    c G (hG : ∀ z eps, Measurable fun ζ => G ζ z eps )
    L (hL : 𝘨) (hGbound : ∀ ζ h,
      |𝔈| ≤ L)
    Φ R (hΦ : ∀ h : 𝗧₂,
      |Φ 𝔒| ≤ R) :
    𝔬 G =
      ∫ ζ, 𝔔 * 𝔉 ∂σ := by
  rw [𝔢 finePairPacketSignedMeasure_integral _
     fun h => by
      change Measurable fun ζ => G ζ (𝔟 h.1).1
        (𝔟 h.1).2 *
        Φ (𝔫 h.2 𝔮 h.2)
      fun_prop (L * R) fun ζ h => by
      rw [finePairPacketObservable, Real.norm_eq_abs, abs_mul]
      bound ]
  simp_rw [finePairPacketObservable_finite_action]

𝗇 𝔠 finePairDensityReset a b z eps p $ ψ ζ
𝗇 𝔊 fun ζ z eps => 𝔠 u * 𝔠 v
𝗇 𝔘 p u * p v
𝗇 𝔪 ψ ζ u
𝗇 𝔜 𝔪 * ψ ζ v * 𝔉
𝗇 𝔞 finePairFieldReset_abs_le a b ha hab M p hp ψ hψ 𝔐
theorem finePairPacketSignedMeasure_pair_action (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (ha : 𝙆) (hab : 𝙭) (M q : ℕ) (hM : 𝗜₁) (C : ℝ)
    (A : 𝔇) (hA : 𝔄)
    (hcost : 𝔍) (c : 𝔩)
    (p : U → ℝ) (hp : ∀ u, p u ∈ 𝘔₂) (ψ : Z → U → ℝ)
    (hmψ : ∀ u, Measurable fun ζ => 𝔪 ) (hψ : ∀ ζ u, |𝔪| ≤ 1)
    u v Φ R (hΦ : ∀ h ,
      |Φ 𝔒| ≤ R) :
    𝔬 𝔊 =
      𝔘 * ∫ ζ, 𝔜 ∂σ := by
  have hm z eps u :
      Measurable fun ζ => 𝔠 u := by
    unfold finePairDensityReset
    fun_prop
  rw [𝔢 finePairPacketSignedMeasure_factor_integral c
    𝔊
    (fun z eps => (hm z eps u).mul $ hm z eps v ) 𝘺  𝖠₃  (fun ζ h => by
      rw [abs_mul, pow_two]
      exact mul_le_mul (𝔞 u)
        (𝔞 v) (abs_nonneg _) 𝙬₁) Φ R hΦ]
  simp_rw [finePairDensitySignedRule_pair_exact a b ha hab M hM p]
  have he ζ : 𝔘 * 𝔪 * ψ ζ v * 𝔉 =
      𝔘 * 𝔜 := 𝖢₃
  simp_rw [he]
  exact integral_const_mul ..
