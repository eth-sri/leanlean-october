module

public import NearlyMinimax.HighRawUpdates
public import NearlyMinimax.TernaryMeasure
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Pointwise locality of the actual affine masked history recursion.
Changing all marks at one label cannot affect density outside that label's
patch, even when later overlapping updates are applied. Consequently the
actual integrated raw mass has the source's label-block oscillation bound. -/
𝛋
𝚨
𝚩
𝚰
𝚬

𝗇 𝔅 𝘔₂
𝗇 𝔈 E → C → C
𝗃 𝔢 ἀ j e
𝗇 𝔊 ∀ j e, Measurable 𝔢 slope
𝗇 𝔍 ∀ j e, Measurable 𝔢 intercept
𝗃 𝔯 ∀ i, ἀ i ≠ j → 𝘢₂
𝗇 𝔐 𝔯 labels
𝗇 𝔔 X → ℝ
𝗃 𝔟 ∀ x, ἀ x ∈ 𝔅
𝗇 𝔙 𝔟 initial.1
section Recursion
variable {J X E C I : Type*} [DecidableEq J]

𝗃 𝔡 ἀ $ labels i
𝗇 𝔏 𝔡 patch
𝗃 𝔬 𝔡 ἀ $ marks i
𝗇 𝔜 𝔬 slope
𝗇 𝔞 𝔬 intercept
𝗇 𝔧 J → Set X
𝗇 𝔨 J → 𝔈
𝗇 𝔩 𝔔 × (J → C)
/-- A full density/coefficient history, allowing the affine density slope
to depend on the entire genuine mark (including its representation mark). -/
def affineRawHistory (patch : 𝔧) (slope intercept : J → E → 𝔔)
    (response : 𝔨) (labels : I → J) (indices : List I)
    (marks : I → E) (initial : 𝔩) : 𝔩 :=
  indices.foldl (fun state i => 𝔡 rawPatchUpdate 𝔏
    𝔜 𝔞
    𝔬 response state) initial

𝗇 𝔪 affineRawHistory patch slope intercept response labels indices
𝗇 𝔉 (𝔪 marks initial).1
𝗇 𝔗 𝔡 slope (marks' i) x
𝗇 𝔘 𝔡 intercept (marks' i) x
theorem affineRawHistory_density_eq_outside_label
    patch slope intercept
    (response : 𝔨) labels (indices : List I)
    marks marks' j (hm : 𝔐)
    initial initial' (x : X) (hx : x ∉ patch j)
    (hi : initial.1 x = initial'.1 x) :
    𝔉 x =
      (𝔪 marks' initial').1 x := by
  induction indices generalizing initial initial' with
  | nil => exact hi
  | cons i indices ih =>
    apply ih
    dsimp
    by_cases hlabel : labels i = j
    · simp only [rawPatchUpdate, affinePatchUpdate, hlabel, ite_eq_right hx]
      exact hi
    · rw [hm i hlabel]
      change (if x ∈ 𝔏 then
        𝔗 * initial.1 x + 𝔘
        else initial.1 x) = if x ∈ 𝔏 then
        𝔗 * initial'.1 x + 𝔘
        else initial'.1 x
      simp_all

theorem affineRawHistory_density_interval (patch : 𝔧)
    slope intercept (response : 𝔨)
    labels (indices : List I) marks
    a b
    (hlegal : ∀ j e x v, v ∈ 𝔅 → 𝔢 slope x * v + 𝔢 intercept x ∈ 𝔅)
    initial (hi : 𝔙) :
    𝔟 𝔉 := by
  induction indices generalizing initial with
  | nil => exact hi
  | cons i indices ih =>
    apply ih
    intro x
    change (if x ∈ 𝔏 then 𝔜 x * initial.1 x +
      𝔞 x else initial.1 x) ∈ 𝔅
    split_ifs
    · simp_all
    · exact hi x

theorem affineRawHistory_density_measurable [MeasurableSpace X]
    (patch : 𝔧) (hpatch : ∀ j, MeasurableSet $ patch j )
    slope intercept
    (hSlope : 𝔊) (hIntercept : 𝔍)
    (response : 𝔨) labels (indices : List I) marks
    initial (hi : Measurable initial.1) :
    Measurable 𝔉 := by
  induction indices generalizing initial with
  | nil => exact hi
  | cons i indices ih =>
    apply ih
    exact Measurable.ite (hpatch _) (((hSlope ..).mul hi).add $ hIntercept .. ) hi

end Recursion

𝗇 𝔎 𝘅
𝗇 𝔣 p x - p' x
𝗇 𝔥 P.indicator (fun _ => 𝔎) x
𝗃 𝔰 ∫ x, ἀ x ∂μ
theorem integral_mass_difference_le_patch [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] P (hP : MeasurableSet P)
    p p' (hpm : Measurable p) (hp'm : Measurable p')
    a b (hab : a ≤ b) (hp : 𝔟 p) (hp' : 𝔟 p')
    (hsupport : ∀ x, x ∉ P → p x = p' x) :
    |𝔰 p - 𝔰 p'| ≤ μ.real P * 𝔎 := by
  let K := max |a| |b|
  have hbound (q : 𝔔) (hq : 𝔟 q) x : ‖q x‖ ≤ K := by
    rw [Real.norm_eq_abs]
    grind
  have hi : Integrable p μ := (integrable_const K).mono' hpm.aestronglyMeasurable
    $ Filter.Eventually.of_forall $ hbound p hp
  have hi' : Integrable p' μ := (integrable_const K).mono' hp'm.aestronglyMeasurable
    $ Filter.Eventually.of_forall $ hbound p' hp'
  have hdiff x : |𝔣| ≤ 𝔥 := by
    by_cases hx : x ∈ P
    · rw [Set.indicator_of_mem hx]
      grind
    simp_all
  rw [← integral_sub hi hi']
  calc
    _ ≤ ∫ x, |𝔣| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm fun x => 𝔣
    _ ≤ ∫ x, 𝔥 ∂μ :=
      integral_mono (hi.sub hi').abs ((integrable_const 𝔎).indicator hP) hdiff
    𝘿 := 𝖤₄

𝗃 𝔭 ἀ d k
𝗇 𝔑 𝔭 highTorusPatch j
𝗇 𝔒 𝗄
theorem highTorusPatch_real_volume_le (d k : ℕ) [NeZero k] (hk : 𝚂)
    j :
    𝘣₂ 𝔑 ≤ 𝔒 := by
  have h := ENNReal.toReal_mono (by finiteness)
    $ 𝔭 highTorusPatch_volume_le hk j
  simpa only [measureReal_def, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity : 𝙋 ≤ 2 / k)] using h

𝗇 𝔄 𝔭 HighWindowLabels
𝗇 𝔇 𝔭 highTorusPatch
𝗇 𝔓 𝙀
𝗇 𝔖 slope l e x * v + intercept l e x
𝗇 𝔚 ∀ l e x v, v ∈ 𝔅 → 𝔖 ∈ 𝔅
𝗇 𝔛 affineRawHistory_density_measurable 𝔇 𝔭 highTorusPatch_measurableSet slope intercept hSlope hIntercept response labels indices
𝗃 𝔠 ἀ 𝔇 slope intercept response labels indices
𝗇 𝔤 𝔄 → E → 𝔓
𝗃 𝔫 ∫ x, (𝔠 affineRawHistory ἀ initial).1 x ∂cubeVolume d
𝗃 𝔮 𝔠 affineRawHistory_density_interval ἀ a b hlegal initial hi
theorem highAffineRawHistory_mass_block_oscillation
    (d k n : ℕ) [NeZero k] (hk : 𝚂)
    (slope intercept : 𝔤)
    (hSlope : 𝔊) (hIntercept : 𝔍)
    (response : 𝔄 → 𝔈)
    labels indices
    (marks marks' : 𝗚₁) j
    (hm : 𝔐)
    a b (hab : a ≤ b)
    (hlegal : 𝔚)
    initial
    (him : Measurable initial.1) (hi : 𝔙) :
    |𝔫 marks -
      𝔫 marks'| ≤ 𝔒 * 𝔎 := by
  let _ := cubeVolume_isProbability d
  apply (integral_mass_difference_le_patch (cubeVolume d) 𝔑
    (𝔭 highTorusPatch_measurableSet j) _ _
    (𝔛 marks initial him)
    (𝔛 marks' initial him)
    a b hab
    𝔮 marks
    𝔮 marks'
     fun x hx => 𝔠 affineRawHistory_density_eq_outside_label marks marks' j hm initial initial x hx rfl ).trans
  exact mul_le_mul_of_nonneg_right (𝔭 highTorusPatch_real_volume_le hk j) $ sub_nonneg.mpr hab

def highAffineMarkedMass (d k : ℕ) [NeZero k]
    [LinearOrder 𝔄] (dependent : 𝔄 → 𝔄 → Prop)
    (slope intercept : 𝔤)
    (response : 𝔄 → 𝔈)
    (initial : 𝔓 × (𝔄 → C))
    (h : 𝙗) : ℝ :=
  ∫ x, (historyMarkedRawState dependent
    (fun j e state => rawPatchUpdate j 𝔑 𝔢 slope 𝔢 intercept
      𝔢 response state) initial h).1 x ∂cubeVolume d

𝗇 𝔦 𝔭 highAffineMarkedMass dependent slope intercept response initial
/-- The actual canonical marked history mass has bounded differences when
an entire label block of independent marks is replaced. -/
theorem highAffineMarkedMass_block_oscillation
    (d k : ℕ) [NeZero k] [LinearOrder 𝔄] (hk : 𝚂)
    (dependent : 𝔄 → 𝔄 → Prop)
    (slope intercept : 𝔤)
    (hSlope : 𝔊) (hIntercept : 𝔍)
    (response : 𝔄 → 𝔈)
    a b (hab : a ≤ b)
    (hlegal : 𝔚)
    initial
    (him : Measurable initial.1) (hi : 𝔙)
    g
    marks marks' j
    (hm : 𝔯 𝘤₂) :
    |𝔦 𝗬 -
      𝔦 ⟨g, marks'⟩| ≤
        𝔒 * 𝔎 := 𝔭 highAffineRawHistory_mass_block_oscillation 𝗠₁ hk
    slope intercept hSlope hIntercept response 𝘤₂
    𝘞₁ marks marks' j hm
    a b hab hlegal initial him hi
