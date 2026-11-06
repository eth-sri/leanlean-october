module

public import NearlyMinimax.HigherBandActivity
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The actual finite family of nonzero legal higher-target ordinary
rows. Zero signed rows are omitted, as in the manuscript. -/
𝚫
𝚪
𝚨
𝚩
𝚾

def higherBandTargetScale (d r : ℕ) (N μ : ℝ) : ℝ :=
  N * (μ * 𝘵)^((𝗥₂-2)/𝙊)

𝗇 𝔈 Fin 𝘐 × Bool
def higherBandFamilyTarget (i : 𝔈) : ℕ := i.1.val + 3
def higherBandFamilyGuardDegree (M : ℕ) (i : 𝔈) : ℕ :=
  if i.2 then M else D
𝗇 𝔉 higherBandTargetScale d (higherBandFamilyTarget i) N μ
def higherBandFamilyUpper (d : ℕ) (ℓ N μ : ℝ) (i : 𝔈) : ℝ :=
  if i.2 then 𝔉
  else min ℓ 𝔉

𝗇 𝔐 higherBandFamilyUpper d ℓ N μ
def HigherBandFamilySelected (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) (i : 𝔈) : Prop :=
  1 ≤ 𝔐 i ∧
  (i.2 = true → ℓ < 𝔉) ∧
  higherBandFamilyTarget i ≤ higherBandFamilyGuardDegree M i ∧
  0 < 𝗤₂ (𝔐 i) i.2

𝗃 𝔎 ἀ d D M q a b C lam ℓ N μ
abbrev HigherBandFamilyIndex (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) :=
  {i : 𝔈 // 𝔎 HigherBandFamilySelected i}

𝗇 𝔅 𝔎 HigherBandFamilyIndex
instance higherBandFamilyIndex_fintype (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    Fintype 𝔅 := by
  classical
  infer_instance

𝗇 𝔍 𝚁
def HigherBandFamilyMark (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : 𝔅) : Type :=
  HigherBandRowMark d (higherBandFamilyTarget i.val) 𝔍 D q i.val.2

𝗇 𝔇 𝔎 HigherBandFamilyMark
instance higherBandFamilyMark_measurable (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : 𝔅) :
    MeasurableSpace $ 𝔇 i := by
  dsimp [HigherBandFamilyMark]
  infer_instance

instance higherBandFamilyMark_standardBorel (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : 𝔅) :
    StandardBorelSpace $ 𝔇 i := by
  letI : StandardBorelSpace $ HigherBandCarrier d (higherBandFamilyTarget i.val) i.val.2 :=
    higherBandCarrier_standardBorel ..
  letI : StandardBorelSpace $ HighPacketMarkIndex 𝙮
      𝔍 (higherBandFamilyTarget i.val) D q := by infer_instance
  dsimp [HigherBandFamilyMark]
  infer_instance

def higherBandFamilyComponent (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : 𝔅) :
    𝙭₁ Unit fun _ => 𝔇 i :=
  higherBandRowData d k (higherBandFamilyTarget i.val) 𝔍 D q
    a b C lam ℓ (𝔐 i.val) i.val.2

𝗃 𝔑 ἀ d k D M q a b C lam ℓ N μ
𝗇 𝔄 𝔑 higherBandFamilyComponent i
def higherBandFamilyData (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    𝙭₁ 𝔅
      𝔇 where
  rowLaw := fun i => (𝔄).rowLaw ()
  rowMass := fun i => (𝔄).rowMass ()
  rowActivation := fun i => (𝔄).rowActivation ()
  rowIntercept := fun i => (𝔄).rowIntercept ()
  rowSlope := fun j i => (𝔄).rowSlope j ()
  rowVector := fun i => (𝔄).rowVector ()
  rowTime := fun i => (𝔄).rowTime ()

theorem higherBandFamily_target_bounds d D M q a b C lam ℓ N μ
    (i : 𝔅) :
    3 ≤ higherBandFamilyTarget i.val ∧ higherBandFamilyTarget i.val ≤ D := by
  dsimp [higherBandFamilyTarget]
  omega

theorem higherBandFamily_mass_positive d k D M q a b C lam ℓ N μ
    i :
    0 < (𝔑 higherBandFamilyData).rowMass i := i.property.2.2.2

𝗃 𝔏 ἀ d r m D q a b C lam L T
𝗇 𝔊 𝔏 higherBandSignedRow fine
𝗃 𝔒 ἀ d r D lam fine
theorem higherBand_zero_mass_signed_zero d r m D q a b C lam L T
    (hT : 𝖹) fine (hz : 𝔏 higherBandRowMass fine = 0) :
    𝔊 = 0 := by
  letI := higherBandCarrierMeasure_finite d r L T hT fine
  rw [𝔏 higherBandRowMass_eq_variation hT fine] at hz
  have hi := highPacketMarkWeight_integrable (higherBandCarrierMeasure d r L T fine) a b m r D q C
    𝔒 higherBandCarrierAmplitude
    𝔒 higherBandCarrierAmplitude_measurable
    𝚜₁
  have hv : (𝔊).variation univ ≠ ⊤ := by
    rw [higherBandSignedRow, highPacketSignedMeasure, Measure.variation_withDensityᵥ hi]
    rw [𝚒₂, Measure.restrict_univ]
    exact ne_of_lt hi.hasFiniteIntegral
  have hzero :=
    (ENNReal.toReal_eq_zero_iff _).mp hz |>.resolve_right hv
  simp_all
