module

public import NearlyMinimax.HighCenteredMark
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Intercept bounds and actual absolute-packet slope centering, for source
reference-law mean-one balancing. -/
𝚫
𝚳
𝚨
𝚩
set_option maxHeartbeats 200000

𝗇 𝔢 w i * f i
𝗇 𝔇 ∑ i, 𝔢
𝗃 𝔣 ἀ $ e i
theorem finite_even_odd_sum_zero [Fintype I]
    (e : Equiv.Perm I) (w f : 𝗦₂)
    (hw : ∀ i, 𝔣 w = w i) (hf : ∀ i, 𝔣 f = -f i) :
    𝔇 = 0 := by
  have he : 𝔇 = -𝔇 := by
    calc
      _ = ∑ i, 𝔣 w * 𝔣 f := by
        symm
        apply Fintype.sum_equiv e
        intro i
        rfl
      _ = ∑ i, -𝔢 := 𝖤₄
      𝘿 := Finset.sum_neg_distrib _
  linarith

def densityMarkReflection (m r D : ℕ) : Equiv.Perm $ HighDensityMarkIndex m r D :=
  Equiv.prodCongr (Equiv.refl _) $ Equiv.piCongrRight fun _ : Fin r => Fin.revPerm

𝗇 𝔄 𝘷₁
𝗇 𝔙 densityMarkReflection m r D
def packetMarkReflection (ι : Type*) (m r D q : ℕ) : Equiv.Perm 𝔄 :=
  Equiv.prodCongr 𝔙 $ Equiv.refl _

𝗃 𝔥 ἀ a b
𝗃 𝔗 𝔥 ἀ m r D
𝗇 𝔖 𝔗 densityPacketWeight
𝗇 𝔛 m + r
𝗇 𝔜 densityDerivativeWeight D (h.2 l).rev
theorem densityPacketWeight_abs_reflection a b m r D
    h :
    |𝔖 (𝔙 h)| =
      |𝔖 h| := by
  change |𝔥 densityPacketPrefactor r * 𝔥 exteriorWeight 𝔛 h.1 *
      (∏ l, 𝔜)| = _
  simp only [densityPacketWeight, abs_mul, Finset.abs_prod]
  have hp : ∏ l, |𝔜| =
      ∏ l, |densityDerivativeWeight D (h.2 l)| := by
    apply Finset.prod_congr rfl
    intro l hl
    exact lobattoDerivativeWeight_abs_reflection ((D - 1) / 2) $ h.2 l
  rw [hp]

section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

𝗇 𝔈 𝔗 densityPacketAtom e.2.1
def highPacketIntercept (a b : ℝ) (m r D q : ℕ)
    (e : Z × 𝔄) : ℝ :=
  (𝔈).1

def highPacketSlope (a b : ℝ) (m r D q : ℕ) (B : Z → 𝗢)
    (e : Z × 𝔄) : ℝ :=
  𝔥 densityMargin (𝔗 highPacketIntercept q e) / (𝗥₂ * b) *
    ∑ l, (𝔈).2 l * B e.1 l

theorem highPacketIntercept_measurable a b m r D q :
    Measurable $ highPacketIntercept (Z := Z) (ι := ι) a b m r D q := by
  apply measurable_from_prod_countable_left
  intro h
  change Measurable fun _ => (𝔗 densityPacketAtom h.1).1
  exact measurable_const

𝗇 𝔅 ∀ l, Measurable fun ζ => B ζ l
theorem highPacketSlope_measurable a b m r D q (B : Z → 𝗢)
    (hB : 𝔅) :
    Measurable $ highPacketSlope (ι := ι) a b m r D q B := by
  apply measurable_from_prod_countable_left
  unfold highPacketSlope highPacketIntercept
  dsimp
  fun_prop

𝗇 𝔍 𝘅 / 𝖾₂
𝗇 𝔔 𝔗 highPacketSlope q B
𝗇 𝔚 𝔥 densityPacketAtom_mem hab.le m r D e.2.1
𝗇 𝔞 B ζ l
theorem highPacketSlope_bound a b (ha : 𝙆) (hab : 𝙭)
    m r D q (hr : 𝘗) B (hB : ∀ ζ l, |𝔞| ≤ 1)
    (e : Z × 𝔄) :
    |𝔔 e| ≤ 𝔍 :=
  𝔥 localDensityReset_slope_bound ha hab r hr
    (𝔈).1
    (𝔚).1
    (𝔈).2
    (𝔚).2
    (fun _ l => B e.1 l) () $ hB e.1

𝗃 𝔤 𝔗 ἀ q C A
𝗇 𝔉 𝔤 highPacketMarkWeight 𝚊
𝗇 𝔡 packetMarkReflection ι m r D q
𝗇 𝔓 (ζ, 𝔡 h)
theorem highPacketMarkWeight_abs_reflection a b m r D q C
    A (ζ : Z) h :
    |𝔤 highPacketMarkWeight 𝔓| =
      |𝔉| := by
  change |𝔖 (𝔙 h.1) *
      𝗨₂ (A ζ) h.2| = _
  rw [abs_mul, densityPacketWeight_abs_reflection, highPacketMarkWeight, abs_mul]

𝗇 𝔎 𝔗 highPacketSlope q B 𝚊
theorem highPacketSlope_reflection a b m r D q B
    (ζ : Z) h :
    𝔔 𝔓 =
      -𝔎 := by
  change 𝔥 densityMargin (𝔥 exteriorNode 𝔛 h.1.1) / (r * b) *
       ∑ l, lobattoNode (derivativeOrder D) (h.1.2 l).rev * 𝔞 = _
  simp_rw [lobattoNode_reflection (derivativeOrder D) $ by unfold derivativeOrder; omega ]
  aesop

theorem highPacketSlope_absolute_finite_sum_zero a b m r D q C
    A B (ζ : Z) :
     ∑ h : 𝔄,
      |𝔉| * 𝔎 = 0 :=
  finite_even_odd_sum_zero 𝔡 _ _
    (𝔤 highPacketMarkWeight_abs_reflection ζ)
    $ 𝔗 highPacketSlope_reflection q B ζ

𝗇 𝔟 signedMarkMass μ w
theorem absoluteMarkLaw_integral [MeasurableSpace E]
    μ w (hmw : Measurable w)
    (hpos : 0 < 𝔟) (F : 𝙏) :
     ∫ e, F e ∂absoluteMarkLaw μ w = (∫ e, |w e| * F e ∂μ) / 𝔟 := by
  rw [absoluteMarkLaw, integral_withDensity_eq_integral_toReal_smul
    (hmw.abs.div_const _).ennreal_ofReal
    $ Filter.Eventually.of_forall 𝘕 ]
  have he : (fun e => (ENNReal.ofReal $ |w e| / 𝔟 ).toReal • F e) =
       fun e => |w e| * F e / 𝔟 := by
    funext e
    rw [ENNReal.toReal_ofReal $ div_nonneg (abs_nonneg $ w e ) hpos.le , smul_eq_mul]
    ring
  rw [he, integral_div]

𝗇 𝔊 𝙚
𝗇 𝔏 𝔥 highPacketSlope_bound ha hab m r D q hr B hB e
𝗃 𝔘 ἀ σ a b m r D q C A
𝗇 𝔐 0 < 𝔘 highPacketMarkMass
𝗇 𝔑 𝔘 highPacketAbsoluteLaw
𝗇 𝔒 (𝔗 highPacketSlope_measurable q B hmB).aestronglyMeasurable
𝗇 𝔠 Z → ι → 𝙛
theorem highPacketSlope_integrable (σ : Measure Z) [IsFiniteMeasure σ]
    a b (ha : 𝙆) (hab : 𝙭) m r D q (hr : 𝘗) C
    (A : 𝔠) (hA : 𝔊)
    (hcost : 𝙧)
    (hpos : 𝔐)
    B (hmB : 𝔅)
    (hB : ∀ ζ l, |𝔞| ≤ 1) :
    Integrable 𝔔 𝔑 := by
  letI := 𝔘 highPacketAbsoluteLaw_probability hA hcost hpos
  apply (integrable_const 𝔍).mono'
    𝔒
  exact Filter.Eventually.of_forall fun e => by
    simpa only [Real.norm_eq_abs] using 𝔏

/-- Absolute derivative-rule reflection kills the actual affine slope under
the genuine normalized absolute packet law. No desired slope mean is supplied. -/
theorem highPacketAbsoluteLaw_slope_integral_zero (σ : Measure Z) [IsFiniteMeasure σ]
    a b (ha : 𝙆) (hab : 𝙭) m r D q (hr : 𝘗) C
    (A : 𝔠) (hA : 𝔊)
    (hcost : 𝙧)
    (hpos : 𝔐)
    B (hmB : 𝔅)
    (hB : ∀ ζ l, |𝔞| ≤ 1) :
     ∫ e, 𝔔 e ∂𝔑 = 0 := by
  have hi := (𝔘 highPacketMarkWeight_integrable hA hcost).abs.mul_bdd
    𝔒
    $ Filter.Eventually.of_forall fun e => by
      simpa only [Real.norm_eq_abs] using 𝔏
  rw [highPacketAbsoluteLaw, absoluteMarkLaw_integral _ _
    (𝔤 highPacketMarkWeight_measurable hA) hpos,
    integral_prod _ hi]
  simp only [integral_count, highPacketSlope_absolute_finite_sum_zero, integral_zero, zero_div]
