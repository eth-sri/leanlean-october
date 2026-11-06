module

public import NearlyMinimax.HighSeparatedRows
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Prod
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The actual joint signed measure of density, separated-representation,
and response marks used by the high-smoothness local update. -/
𝚫
𝚮
𝚨
𝚩
𝚭

section SignedDensity
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

𝗇 𝔙 fun x => ENNReal.ofReal $ -w x
𝗇 𝔞 Filter.Eventually.of_forall 𝘕
𝗇 𝔠 (integrable_const M).mono' hf.aestronglyMeasurable $ Filter.Eventually.of_forall hbound
/-- Integration against an actual real weighted signed measure, for a
bounded measurable observable. The signed-density integral identity is
derived from its positive and negative parts. -/
theorem signedDensity_integral w (hw : Integrable w μ) (hmw : Measurable w)
    (f : X → ℝ) (hf : Measurable f) M (hbound : ∀ x, ‖f x‖ ≤ M) :
     ∫ᵛ x, f x ∂<• μ.withDensityᵥ w = ∫ x, w x * f x ∂μ := by
  let μp := μ.withDensity fun x => ENNReal.ofReal $ w x
  let μn := μ.withDensity 𝔙
  letI := isFiniteMeasure_withDensity_ofReal hw.hasFiniteIntegral
  letI := isFiniteMeasure_withDensity_ofReal hw.neg.hasFiniteIntegral
  have hp : Integrable f μp := 𝔠
  have hn : Integrable f μn := 𝔠
  have hpv : μp.toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using hp
  have hnv : μn.toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using hn
  rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hw,
    VectorMeasure.integral_sub_vectorMeasure hpv hnv, VectorMeasure.integral_toSignedMeasure,
    VectorMeasure.integral_toSignedMeasure]
  have hmn : Measurable 𝔙 := hmw.neg.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hmw.ennreal_ofReal
    𝔞,
    integral_withDensity_eq_integral_toReal_smul hmn
      𝔞]
  simp only [ENNReal.toReal_ofReal', smul_eq_mul]
  have hnf := hw.neg_part.mul_bdd hf.aestronglyMeasurable $ Filter.Eventually.of_forall hbound
  rw [← integral_sub (hw.pos_part.mul_bdd hf.aestronglyMeasurable $ Filter.Eventually.of_forall hbound ) hnf]
  grind

end SignedDensity

section FiniteProduct
variable {Z I : Type*} [MeasurableSpace Z] [MeasurableSpace I]
  [Fintype I] [MeasurableSingletonClass I]

theorem finite_count_integrable (f : 𝗦₂) : Integrable f Measure.count := by
  simp

𝗇 𝔚 fun ζ => f (ζ, i)
theorem joint_finite_integrable (σ : Measure Z) [IsFiniteMeasure σ] (f : Z × I → ℝ)
    (hf : ∀ i, Measurable 𝔚)
    (hi : ∀ i, Integrable 𝔚 σ) :
    Integrable f $ σ.prod Measure.count := by
  have hm := measurable_from_prod_countable_left hf
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  simp
  exact integrable_finsetSum _ fun i _ => (hi i).norm

end FiniteProduct

abbrev HighDensityMarkIndex (m r D : ℕ) :=
  Fin (m + r + 1) × (Fin r → Fin (derivativeOrder D + 1))

𝗇 𝔎 Fin 𝖵
abbrev HighResponseMarkIndex (ι : Type*) (q : ℕ) := (ι × ι) × (Bool × Bool) × 𝔎

𝗇 𝔛 HighDensityMarkIndex m r D
𝗇 𝔜 𝗧₂
abbrev HighPacketMarkIndex (ι : Type*) (m r D q : ℕ) :=
  𝔛 × 𝔜

section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

𝗇 𝔟 𝙛
def highResponseMarkAtom (C : ℝ) (q : ℕ) (h : 𝔜) :
    ℝ × 𝔟 :=
  (responseNode q h.2.2, covarianceAtom C h.1.1 h.1.2 h.2.1.1 h.2.1.2)

def highResponseMarkWeight (C : ℝ) (q : ℕ) (A : ι → 𝔟)
    (h : 𝔜) : ℝ :=
  responseWeight q h.2.2 * covarianceWeight C A h.1.1 h.1.2 h.2.1.1 h.2.1.2

𝗇 𝔇 𝘷₁
𝗇 𝔊 Z → ι → 𝙛
𝗃 𝔫 ἀ a b m r D
𝗇 𝔥 𝔫 densityPacketWeight
𝗇 𝔬 Z × 𝔇
def highPacketMarkWeight (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : 𝔊) (e : 𝔬) : ℝ :=
  𝔥 e.2.1 * 𝗨₂ (A e.1) e.2.2

𝗇 𝔄 𝙚
𝗃 𝕬 𝔫 ἀ q C A
𝗇 𝔦 𝕬 highPacketMarkWeight
𝗇 𝔅 𝔦 𝚊
𝗇 𝔏 𝔦
𝗇 𝔘 𝕬 highPacketMarkWeight_slice_measurable hA
𝗇 𝔮 fun ζ => 𝔅
section

variable (a)
    (b)
    (m)
    (r)
    (D)
    (q)
    (C)
    (A : 𝔊)
    (hA : 𝔄)

include hA

theorem highPacketMarkWeight_slice_measurable h :
    Measurable 𝔮 := by
  dsimp [highPacketMarkWeight, highResponseMarkWeight, covarianceWeight]
  fun_prop

theorem highPacketMarkWeight_measurable :
    Measurable 𝔏 :=
  measurable_from_prod_countable_left 𝔘

end

𝗇 𝔍 𝙧
theorem highPacketMarkWeight_slice_integrable (σ : Measure Z) a b m r D q C
    A (hA : 𝔄)
    (hcost : 𝔍) (h : 𝔇) :
    Integrable 𝔮 σ := 𝘒 $ 𝔥 h.1

𝗃 𝔪 ἀ σ a b m r D q C A
𝗃 𝔵 𝔪 ἀ hA hcost
theorem highPacketMarkWeight_integrable (σ : Measure Z) [IsFiniteMeasure σ]
    a b m r D q C (A : 𝔊)
    (hA : 𝔄) (hcost : 𝔍) :
    Integrable 𝔏 $ σ.prod Measure.count :=
  joint_finite_integrable σ _ 𝔘
    𝔵 highPacketMarkWeight_slice_integrable

/-- The original joint Xi packet as a genuine signed measure, represented
on the finite atom indices together with the actual positive sigma mark. -/
def highPacketSignedMeasure (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : 𝔊) : SignedMeasure 𝔬 :=
  (σ.prod Measure.count).withDensityᵥ 𝔏

𝗇 𝔩 𝔪 highPacketSignedMeasure
𝗇 𝔈 𝔩
𝗇 𝔐 𝔵 highPacketMarkWeight_integrable
𝗇 𝔢 𝚊
𝗃 𝔴 ∫ᵛ e, ἀ e ∂<• 𝔈
𝗃 𝕭 ∑ h : 𝔇, 𝔅 * ἀ 𝔢
𝗃 𝕮 fun ζ => ἀ 𝔢
theorem highPacketSignedMeasure_integral (σ : Measure Z) [IsFiniteMeasure σ]
    a b m r D q C A
    (hA : 𝔄) (hcost : 𝔍)
    (F : 𝔬 → ℝ)
    (hF : ∀ h, Measurable 𝕮 F) M
    (hBound : ∀ ζ h, ‖F 𝔢‖ ≤ M) :
    𝔴 F =
      ∫ ζ, 𝕭 F ∂σ := by
  have hw := 𝔐
  have hmF := measurable_from_prod_countable_left hF
  have hb : ∀ e , ‖F e‖ ≤ M := fun e => hBound e.1 e.2
  rw [highPacketSignedMeasure, signedDensity_integral _ _ hw
    (𝕬 highPacketMarkWeight_measurable hA) F hmF M hb,
    integral_prod _ $ hw.mul_bdd hmF.aestronglyMeasurable $ Filter.Eventually.of_forall hb ]
  simp

𝗇 𝔨 highResponseMarkAtom C q
𝗃 𝔶 coefficientReset c (𝔨 ἀ).2
𝗇 𝔓 𝔶 h (𝔨 h).1
theorem highResponseMark_action q C A
    c Φ :
     ∑ h : 𝔜, 𝗨₂ A h *
      Φ 𝔓 =
      𝗔 A c Φ := by
  simp only [Fintype.sum_prod_type, highResponseMarkWeight, highResponseMarkAtom,
    responseMatrixAction, covarianceAction, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  grind

𝗇 𝔧 𝔫 densityPacketAtom
𝗇 𝔣 𝔧
def highPacketObservable (a b : ℝ) (m r D q : ℕ) (C : ℝ) (c : 𝔟)
    (G : Z → ℝ → 𝗢 → ℝ) (Φ : 𝔟 → ℝ)
    (e : 𝔬) : ℝ :=
  G e.1 (𝔣 e.2.1).1 (𝔣 e.2.1).2 *
    Φ (𝔶 e.2.2 (𝔨 e.2.2).1)

𝗇 𝔳 𝗔 (A ζ) c Φ
𝗇 𝔑 fun z ε => G ζ z ε * 𝔳
𝗇 𝔒 G ζ (𝔧 h).1 (𝔧 h).2
𝗇 𝔔 𝔫 densityPacketWeight h
𝗇 𝔗 𝔫 highPacketObservable q C c G Φ
𝗇 𝔭 (ζ, (h, v))
theorem highPacketObservable_finite_action a b m r D q C
    A c
    G Φ (ζ : Z) :
    𝕭 𝔗 =
      𝔫 densityPacketAction 𝔑 := by
  rw [Fintype.sum_prod_type]
  have he h :
       ∑ v : 𝔜,
        𝔦 𝔭 *
          𝔗 𝔭 =
      𝔔 *
        (𝔒 *
          𝔳) := by
    rw [← highResponseMark_action q C (A ζ) c Φ]
    simp only [Finset.mul_sum, highPacketMarkWeight, highPacketObservable]
    grind
  simp_rw [he]
  have hi := 𝔫 densityPacketSignedRule_integral
    𝔑
  rw [densityPacketSignedRule, atomicSignedRule_integral] at hi
  exact hi

/-- The joint signed integral equals the actual iterated Xi action used
in the local-row theorem. -/
theorem highPacketSignedMeasure_factor_integral (σ : Measure Z) [IsFiniteMeasure σ]
    a b m r D q C A
    (hA : 𝔄) (hcost : 𝔍)
    c G
    (hG : ∀ z ε, Measurable fun ζ => G ζ z ε ) L (hL : 𝘨)
    (hGbound : ∀ ζ (h : 𝔛),
      |𝔒| ≤ L)
    Φ M
    (hΦ : ∀ h : 𝔜,
      |Φ 𝔓| ≤ M) :
    𝔴 𝔗 =
      𝔪 highSeparatedPacketAction c G Φ := by
  have hmF h :
      Measurable 𝕮 𝔗 := by
    change Measurable fun ζ => G ζ (𝔣 h.1).1
      (𝔣 h.1).2 *
        Φ (𝔶 h.2 (𝔨 h.2).1)
    fun_prop
  rw [𝔵 highPacketSignedMeasure_integral _
    hmF $ L * M ]
  · simp only [highPacketObservable_finite_action, highSeparatedPacketAction]
  · intro ζ h
    rw [highPacketObservable, Real.norm_eq_abs, abs_mul]
    bound

𝗇 𝔤 ((𝔈).variation univ).toReal
theorem highPacketSignedMeasure_variation (σ : Measure Z) [IsFiniteMeasure σ]
    a b m r D q C A
    (hA : 𝔄) (hcost : 𝔍) :
    𝔤 =
      ∫ ζ, ∑ h : 𝔇,
        |𝔅| ∂σ := by
  have hw := 𝔐
  rw [highPacketSignedMeasure, Measure.variation_withDensityᵥ hw,
    𝚒₂]
  simp
  rw [← integral_norm_eq_lintegral_enorm hw.aestronglyMeasurable,
    integral_prod _ hw.norm]
  simp

𝗇 𝔖 𝘖
𝗇 𝔰 𝘐₁
theorem highResponseMark_variation q C A :
     ∑ h : 𝔜, |𝗨₂ A h| =
      (∑ h : 𝔎, |𝔰|) * (𝔖 * ∑ i, ∑ j, |𝘩|) := by
  simp only [highResponseMarkWeight, Fintype.sum_prod_type, abs_mul]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [covariance_weight_variation]

theorem highPacketMarkWeight_variation a b m r D q C
    A (ζ : Z) :
     ∑ h : 𝔇, |𝔅| =
      (∑ h : 𝔛, |𝔔|) *
        (∑ h : 𝔎, |𝔰|) * 𝔖 * separatedMatrixCost A ζ := by
  rw [Fintype.sum_prod_type]
  simp only [highPacketMarkWeight, abs_mul]
  simp_rw [← Finset.mul_sum, highResponseMark_variation]
  rw [← Finset.sum_mul]
  unfold separatedMatrixCost
  ring

𝗇 𝔯 ∫ ζ, separatedMatrixCost A ζ ∂σ
/-- Exact raw-atom variation of Xi: the density packet cost, fixed scalar
response cost and signed covariance cost multiply the actual representation cost. -/
theorem highPacketSignedMeasure_totalVariation (σ : Measure Z) [IsFiniteMeasure σ]
    a b m r D q C (A : 𝔊)
    (hA : 𝔄) (hcost : 𝔍) :
    𝔤 =
      (∑ h : 𝔛, |𝔔|) *
        (∑ h : 𝔎, |𝔰|) * 𝔖 *
          𝔯 := by
  rw [𝔵 highPacketSignedMeasure_variation]
  simp only [highPacketMarkWeight_variation]
  rw [integral_const_mul]

𝗇 𝔡 𝔧
theorem densityPacketAtom_injective a b (hab : 𝙭)
    m r D (hr : 𝘗) : Function.Injective 𝔡 := by
  intro e f he
  apply Prod.ext
  · exact (exteriorNode_strictAnti a b hab (m + r) 𝖡₃ ).injective $ congrArg Prod.fst he
  · funext l
    exact (lobattoNode_strictAnti (derivativeOrder D) $ by unfold derivativeOrder; omega ).injective
      $ congrArg (fun e => e.2 l) he

𝗇 𝔉 exteriorTau 𝖬
𝗇 𝔱 1 + 𝔉
𝗇 𝔲 m * 𝔉
𝗃 𝔷 ἀ a b ha hab m r D hr hD
theorem densityPacketWeight_exponential_cost a b (ha : 𝙆) (hab : 𝙭)
    m r D (hr : 𝘗) (hD : 𝗮) :
     ∑ h : 𝔛, |𝔔| ≤
      (Real.exp 𝔱 * |𝘸₁|) ^ r *
        D ^ r * Real.exp 𝔲 := by
  have he := atomicSignedRule_totalVariation_eq 𝔡
    𝔥 $ densityPacketAtom_injective a b hab m r D hr
  rw [← he]
  exact 𝔷 densityPacketSignedRule_exponential_cost

section

variable (σ : Measure Z)
    [IsFiniteMeasure σ]
    (a)
    (b)

theorem highPacketSignedMeasure_exponential_cost (ha : 𝙆) (hab : 𝙭) m r D q (hr : 𝘗) (hD : 𝗮)
    C (A : 𝔊) (hA : 𝔄)
    (hcost : 𝔍) :
    𝔤 ≤
       (Real.exp 𝔱 * |𝘸₁|) ^ r *
        D ^ r * Real.exp 𝔲 *
          (∑ h : 𝔎, |𝔰|) * 𝔖 *
            𝔯 := by
  rw [𝔵 highPacketSignedMeasure_totalVariation]
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right 𝔷 densityPacketWeight_exponential_cost
        $ Finset.sum_nonneg 𝖢
    · positivity
  · apply integral_nonneg
    intro ζ
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg $ A ζ i j

theorem highPacketSignedMeasure_zero_mass m r D q C (A : 𝔊)
    (hA : 𝔄) (hcost : 𝔍) :
    𝔩 univ = 0 := by
  have hw := 𝔐
  rw [highPacketSignedMeasure, withDensityᵥ_apply hw MeasurableSet.univ, Measure.restrict_univ,
    integral_prod _ hw]
  have hz ζ : ∑ h : 𝔇,
      𝔅 = 0 := by
    have h := 𝕬 highPacketObservable_finite_action 𝖾
      (fun _ _ _ => 1) 𝙃 ζ
    simpa only [highPacketObservable, mul_one, mul_zero, responseMatrixAction_zero_mass,
      densityPacketAction_zero] using h
  simp_all

end

variable {α : Type*} [DecidableEq α]
