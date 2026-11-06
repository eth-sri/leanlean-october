module

public import NearlyMinimax.FinePairResponsePacket
public import NearlyMinimax.HighReferenceBalancing
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The genuine uncentered absolute fine-pair reference law. Reflection of
the actual three-point modulation atoms centers its affine density slope. -/
𝚸
𝚳
𝚨
𝚰
𝚩

theorem fineModulationNode_reflection i : fineModulationNode i.rev = -fineModulationNode i := by
  fin_cases i <;> norm_num [fineModulationNode, Fin.rev]

theorem fineModulationWeight_abs_reflection i :
    |fineModulationWeight i.rev| = |fineModulationWeight i| := by
  fin_cases i <;> norm_num [fineModulationWeight, Fin.rev]

𝗃 𝔚 ἀ ι M q
𝗇 𝔍 𝔚 FinePairPacketIndex
def finePairPacketReflection (ι : Type*) (M q : ℕ) : Equiv.Perm 𝔍 :=
  Equiv.prodCongr (Equiv.prodCongr (Equiv.refl _) Fin.revPerm) $ Equiv.refl _

section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

𝗇 𝔈 Z → ι → 𝙛
𝗃 𝔘 ἀ a b
𝗃 𝔓 𝔘 ἀ M q
𝗇 𝔒 𝔓 finePairPacketWeight C A
𝗇 𝔉 𝔒
𝗃 𝔛 ἀ (σ.prod Measure.count) 𝔉
def finePairPacketMarkMass (σ : Measure Z) (a b : ℝ) (M q : ℕ) (C : ℝ) (A : 𝔈) : ℝ :=
  𝔛 signedMarkMass

𝗇 𝔄 Z × 𝔚 FinePairPacketIndex
def finePairPacketAbsoluteLaw (σ : Measure Z) (a b : ℝ) (M q : ℕ) (C : ℝ)
    (A : 𝔈) : Measure 𝔄 :=
  𝔛 absoluteMarkLaw

def finePairPacketActivation (σ : Measure Z) (a b : ℝ) (M q : ℕ) (C : ℝ)
    (A : 𝔈) : 𝔄 → ℝ :=
  𝔛 absoluteActivation

𝗇 𝔐 𝔘 finePairDensityAtom M
𝗃 𝔙 (𝔐 ἀ).1
def finePairPacketIntercept (a b : ℝ) (M q : ℕ) (e : 𝔄) : ℝ :=
  𝔙 e.2.1

def finePairPacketSlope (a b : ℝ) (M q : ℕ) (ψ : Z → ℝ) (e : 𝔄) : ℝ :=
  𝔘 densityMargin (𝔓 finePairPacketIntercept e) / b *
    (𝔐 e.2.1).2 * ψ e.1

def finePairPacketResponseVector (M q : ℕ) (C : ℝ) (e : 𝔄) : 𝙛 :=
  𝗻₁

def finePairPacketResponseTime (M q : ℕ) (e : 𝔄) : ℝ :=
  𝗼₁

theorem finePairPacketIntercept_measurable a b M q :
    Measurable $ finePairPacketIntercept (Z := Z) (ι := ι) a b M q := by
  apply measurable_from_prod_countable_left
  intro h
  change Measurable fun _ => 𝔙 h.1
  exact measurable_const

theorem finePairPacketSlope_measurable a b M q (ψ : Z → ℝ) (hψ : Measurable ψ) :
    Measurable $ finePairPacketSlope (ι := ι) a b M q ψ := by
  apply measurable_from_prod_countable_left
  unfold finePairPacketSlope finePairPacketIntercept
  dsimp
  fun_prop

𝗇 𝔑 𝔓 finePairPacketSlope
theorem finePairPacketSlope_joint_measurable [MeasurableSpace U]
    a b M q (ψ : Z → U → ℝ)
    (hψ : Measurable fun zu : Z × U => ψ zu.1 zu.2 ) :
    Measurable fun eu : 𝔄 × U =>
      𝔑 (fun ζ => ψ ζ eu.2) eu.1 := by
  have hc : Measurable fun eu : 𝔄 × U =>
      𝔘 densityMargin 𝔙 eu.1.2.1 / b *
        (𝔐 eu.1.2.1).2 :=
    (measurable_of_countable fun h : 𝔍 =>
      𝔘 densityMargin 𝔙 h.1 / b *
        (𝔐 h.1).2 ).comp $ measurable_snd.comp measurable_fst
  exact hc.mul $ hψ.comp 𝘙₂

𝗇 𝔗 M + 2
theorem finePairPacketIntercept_mem a b (hab : a ≤ b) M q
    (e : 𝔄) : 𝔓 finePairPacketIntercept e ∈ 𝔘 Icc :=
  𝔘 exteriorNode_mem hab 𝔗 e.2.1.1

theorem finePairPacketSlope_bound a b (ha : 𝙆) (hab : 𝙭) M q
    ψ (hψ : ∀ ζ, |ψ ζ| ≤ 1) (e : 𝔄) :
    |𝔑 ψ e| ≤ 𝘅 / 𝖾₂ :=
  𝔘 finePairDensityReset_slope_bound ha hab _ _
    (𝔘 exteriorNode_mem hab.le 𝔗 e.2.1.1) (fineModulationNode_bound e.2.1.2)
    (fun _ => ψ e.1) () $ hψ e.1

𝗇 𝔅 𝔒 𝚊
𝗇 𝔖 (ζ, 𝔚 finePairPacketReflection h)
theorem finePairPacketWeight_abs_reflection a b M q C
    A (ζ : Z) h :
    |𝔒 𝔖| =
      |𝔅| := by
  simp only [finePairPacketWeight, finePairDensityWeight, finePairPacketReflection,
    Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
    Equiv.refl_apply, Fin.revPerm_apply, abs_mul,
    fineModulationWeight_abs_reflection]

𝗇 𝔏 𝔓 finePairPacketSlope ψ 𝚊
theorem finePairPacketSlope_reflection a b M q ψ (ζ : Z)
    h :
    𝔑 ψ 𝔖 =
      -𝔏 := by
  simp only [finePairPacketSlope, finePairPacketIntercept, finePairDensityAtom,
    finePairPacketReflection, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
    Equiv.refl_apply, Fin.revPerm_apply,
    fineModulationNode_reflection]
  ring

theorem finePairPacketSlope_absolute_sum_zero a b M q C
    A ψ (ζ : Z) :
     ∑ h : 𝔍, |𝔅| *
      𝔏 = 0 :=
  finite_even_odd_sum_zero 𝔚 finePairPacketReflection _ _
    (𝔓 finePairPacketWeight_abs_reflection C A ζ)
    $ 𝔓 finePairPacketSlope_reflection ψ ζ

𝗃 𝔔 ἀ σ a b M q C A
variable (σ : Measure Z) [IsFiniteMeasure σ] (a b : ℝ) (M q : ℕ) (C : ℝ)
  (A : 𝔈) (hA : 𝙚)
  (hcost : 𝙧)
  (hpos : 0 < 𝔔 finePairPacketMarkMass)
include hA hcost hpos

𝗇 𝔇 𝔔 finePairPacketWeight_integrable hA hcost
𝗇 𝔊 𝔔 finePairPacketAbsoluteLaw
theorem finePairPacketAbsoluteLaw_probability :
    IsProbabilityMeasure 𝔊 :=
  absoluteMarkLaw_probability _ _ 𝔇 hpos

𝗇 𝔎 𝔓 finePairPacketWeight_measurable C A hA
theorem finePairPacketActivation_centered :
     ∫ e, 𝔔 finePairPacketActivation e ∂𝔊 = 0 := by
  apply absoluteActivation_centered _ _ 𝔎 hpos
  rw [integral_prod _ 𝔇]
  have hz ζ : ∑ h : 𝔍, 𝔅 = 0 := by
    have hh := 𝔓 finePairPacketObservable_finite_action C A 𝖾
      (fun _ _ _ => 1) 𝙃 ζ
    simpa only [finePairPacketObservable, mul_one, responseMatrixAction_zero_mass, mul_zero] using hh
  simp_all

theorem finePairPacketAbsoluteLaw_slope_integral_zero (ha : 𝙆) (hab : 𝙭)
    ψ (hmψ : Measurable ψ) (hψ : ∀ ζ, |ψ ζ| ≤ 1) :
     ∫ e, 𝔑 ψ e ∂𝔊 = 0 := by
  have hi := (𝔇).abs.mul_bdd
    (𝔓 finePairPacketSlope_measurable ψ hmψ).aestronglyMeasurable
    $ Filter.Eventually.of_forall fun e => by
      simpa only [Real.norm_eq_abs] using 𝔘 finePairPacketSlope_bound ha hab M q ψ hψ e
  rw [finePairPacketAbsoluteLaw, absoluteMarkLaw_integral _ _
    𝔎 hpos, integral_prod _ hi]
  simp only [integral_count, finePairPacketSlope_absolute_sum_zero, integral_zero, zero_div]
