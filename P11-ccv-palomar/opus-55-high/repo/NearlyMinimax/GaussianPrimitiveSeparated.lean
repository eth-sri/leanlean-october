module

public import NearlyMinimax.GaussianAffineRepresentation
public import NearlyMinimax.HighSeparatedRows
public import NearlyMinimax.ActualSeparatedPacket
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! A genuine positive Gaussian separated representation of the exact
two-observation affine covariance building block, with bounded factors and
uniform integrated coefficient cost. -/
open MeasureTheory ProbabilityTheory Set MvPolynomial
𝚮
𝚨
𝚩
𝚽

abbrev GaussianPrimitiveIndex (d : ℕ) := (Fin d × Fin d) × (Bool × Bool) × Bool
abbrev GaussianPrimitiveMark (d : ℕ) := Covariate d × GaussianPrimitiveIndex d

def gaussianPrimitiveMeasure (d : ℕ) : Measure $ GaussianPrimitiveMark d :=
  (standardGaussianPi d).prod Measure.count

𝗇 𝔞 2 * lam * t
𝗃 𝔩 gaussianPhase (fun l => Real.sqrt 𝔞 * ἀ l) Z
𝗇 𝔈 𝔩 x
def gaussianTrig (lam t : ℝ) (Z x : Covariate d) (s : Bool) : ℝ :=
  if s then Real.sin 𝔈
  else Real.cos 𝔈

𝗃 𝔟 ἀ lam t
𝗇 𝔙 𝔟 gaussianTrig
𝗇 𝔠 abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
theorem gaussianTrig_abs_le_one lam t (Z x : Covariate d) s :
    |𝔙 Z x s| ≤ 1 := by
  cases s <;> simp only [gaussianTrig]
  · exact 𝔠
  · exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩

𝗇 𝔄 gaussianPhase (𝔟 gaussianSpatialFrequency x y) Z
theorem gaussianTrig_cos_difference lam t (Z x y : Covariate d) :
    Real.cos 𝔄 =
      ∑ s : Bool, 𝔙 Z x s * 𝔙 Z y s := by
  have he : 𝔄 =
      𝔩 y -
      𝔈 := by
    simp only [gaussianPhase, gaussianSpatialFrequency]
    rw [← Finset.sum_sub_distrib]
    grind
  rw [he, Real.cos_sub]
  simp only [Fintype.sum_bool, gaussianTrig, Bool.false_eq_true, ite_false, ite_true]
  ring

def gaussianAffinePolynomial (a : Fin d) (s : Bool) : 𝙣 :=
  if s then C (-8) * X a else C 2

def gaussianAffineFactor (a : Fin d) (s : Bool) (y : Covariate d) : ℝ :=
  if s then 1 else y a / 2

𝗇 𝔥 gaussianAffineFactor a s y
theorem gaussianAffineFactor_abs_le_one a s (y : Covariate d)
    (hy : |y a| ≤ 2) : |𝔥| ≤ 1 := by
  cases s
  · simp only [gaussianAffineFactor, Bool.false_eq_true, ite_false, abs_div]
    linarith
  · simp [gaussianAffineFactor]

𝗇 𝔑 y a - x a
theorem spatialCardinalAffine_gaussian_expansion x y :
    spatialCardinalAffine x y =
      ∑ a : Fin d, C 𝔑 *
        ∑ s : Bool, C 𝔥 * gaussianAffinePolynomial a s := by
  apply Finset.sum_congr rfl
  simp only [Fintype.sum_bool, gaussianAffineFactor, gaussianAffinePolynomial]
  grind

𝗇 𝔅 𝔥 * (gaussianAffinePolynomial a s).coeff β
𝗇 𝔖 (spatialCardinalAffine x y).coeff
𝗇 𝔚 ∑ s : Bool, 𝔅
theorem spatialCardinalAffine_gaussian_coeff x y β :
    𝔖 β =
      ∑ a : Fin d, 𝔑 *
        𝔚 := by
  rw [spatialCardinalAffine_gaussian_expansion]
  simp only [coeff_sum, coeff_C_mul]

def gaussianPrimitiveLeft (lam t : ℝ) (e : GaussianPrimitiveMark d) (x : Covariate d) : ℝ :=
  𝔙 e.1 x e.2.2.2

𝗇 𝔡 gaussianAffineFactor e.2.1.1 e.2.2.1.1 y
𝗇 𝔢 gaussianAffineFactor e.2.1.2 e.2.2.1.2 y
def gaussianPrimitiveRight (lam t : ℝ) (e : GaussianPrimitiveMark d) (y : Covariate d) : ℝ :=
  𝔙 e.1 y e.2.2.2 *
    𝔡 * 𝔢

𝗇 𝔗 lam / 2
def gaussianPrimitiveAmplitude (lam : ℝ) (e : GaussianPrimitiveMark d)
    (β β' : 𝖨₁) : ℝ :=
  𝔗 * gaussianHermite e.2.1.1 e.2.1.2 e.1 *
    (gaussianAffinePolynomial e.2.1.1 e.2.2.1.1).coeff β *
      (gaussianAffinePolynomial e.2.1.2 e.2.2.1.2).coeff β'

𝗇 𝔦 𝔟 gaussianPrimitiveLeft e x
theorem gaussianPrimitiveLeft_bound lam t e (x : Covariate d) :
    |𝔦| ≤ 1 := gaussianTrig_abs_le_one ..

𝗇 𝔣 𝔟 gaussianTrig_abs_le_one e.1 y e.2.2.2
𝗇 𝔧 𝔟 gaussianPrimitiveRight e y
theorem gaussianPrimitiveRight_bound lam t e
    (y : Covariate d) (hy : ∀ a, |y a| ≤ 2) : |𝔧| ≤ 1 := by
  unfold gaussianPrimitiveRight
  rw [abs_mul, abs_mul]
  have h1 := 𝔣
  have h2 := gaussianAffineFactor_abs_le_one e.2.1.1 e.2.2.1.1 y $ hy _
  have h3 := gaussianAffineFactor_abs_le_one e.2.1.2 e.2.2.1.2 y $ hy _
  bound

𝗃 𝔨 Measurable fun e : GaussianPrimitiveMark d => ἀ
𝗃 𝔫 fun Z => 𝔙 Z ἀ h.2.2
theorem gaussianPrimitiveLeft_measurable lam t x :
    𝔨 𝔦 := by
  apply measurable_from_prod_countable_left
  intro h
  change Measurable 𝔫 x
  cases h.2.2 <;> simp only [gaussianTrig, Bool.false_eq_true, ite_false, ite_true] <;>
    unfold gaussianPhase <;> fun_prop

theorem gaussianPrimitiveRight_measurable lam t y :
    𝔨 𝔧 := by
  apply measurable_from_prod_countable_left
  intro h
  unfold gaussianPrimitiveRight
  dsimp
  have hm : Measurable 𝔫 y := by
    cases h.2.2 <;> simp only [gaussianTrig, Bool.false_eq_true, ite_false, ite_true] <;>
      unfold gaussianPhase <;> fun_prop
  fun_prop

𝗃 𝔬 gaussianPrimitiveAmplitude lam ἀ β β'
𝗇 𝔒 𝔬 e
theorem gaussianPrimitiveAmplitude_measurable lam β β' :
    𝔨 𝔒 := by
  apply measurable_from_prod_countable_left
  intro h
  unfold gaussianPrimitiveAmplitude
  dsimp
  have hm : Measurable $ gaussianHermite h.1.1 h.1.2 :=
    measurable_const.sub $ (measurable_pi_apply _).mul $ measurable_pi_apply _
  fun_prop

𝗇 𝔓 (Z, h)
theorem gaussianPrimitiveAmplitude_slice_integrable lam
    β β' h :
    Integrable (fun Z => 𝔬 𝔓) $ standardGaussianPi d := by
  change Integrable (fun Z => 𝔗 * gaussianHermite h.1.1 h.1.2 Z *
    (gaussianAffinePolynomial h.1.1 h.2.1.1).coeff β *
    (gaussianAffinePolynomial h.1.2 h.2.1.2).coeff β') $ standardGaussianPi d
  exact (((gaussianHermite_integrable h.1.1 h.1.2).const_mul _).mul_const _).mul_const _

theorem gaussianPrimitiveAmplitude_integrable lam β β' :
    Integrable (fun e => 𝔒)
      $ gaussianPrimitiveMeasure d :=
  joint_finite_integrable _ _
    (fun h => (gaussianPrimitiveAmplitude_measurable lam β β').comp
      $ measurable_id.prodMk measurable_const )
    $ gaussianPrimitiveAmplitude_slice_integrable lam β β'

theorem finite_injective_indicator_sum_le_one {I X : Type*} [Fintype I] [DecidableEq X]
    (f : I → X) (hf : Function.Injective f) x :
    (∑ i, if x = f i then 𝙠 else 0) ≤ 1 := by
  classical
  by_cases hx : ∃ i, f i = x
  · obtain ⟨i, hi⟩ := hx
    have he j : x = f j ↔ j = i := by
      grind
    simp_all
  · have he j : x ≠ f j := by bound
    simp_all

𝗇 𝔇 (Z, ((a, b), ((s, s'), p)))
𝗇 𝔊 gaussianAffineFactor b s' y * (gaussianAffinePolynomial b s').coeff β'
𝗇 𝔍 ∑ s : Bool, gaussianAffineFactor b s y * (gaussianAffinePolynomial b s).coeff β'
𝗇 𝔔 gaussianHermite a b Z
𝗇 𝔛 𝔗 * 𝔔 * Real.cos 𝔄
theorem gaussianPrimitive_finite_action lam t x y Z
    β β' :
     ∑ h : GaussianPrimitiveIndex d,
      𝔟 gaussianPrimitiveLeft 𝔓 x * 𝔟 gaussianPrimitiveRight 𝔓 y *
        𝔬 𝔓 =
      𝔗 * ∑ a : Fin d, ∑ b : Fin d,
        𝔔 *
          𝔚 *
          𝔍 *
          Real.cos 𝔄 := by
  classical
  simp only [Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hphase s s' :
       ∑ p : Bool, 𝔟 gaussianPrimitiveLeft 𝔇 x *
        𝔟 gaussianPrimitiveRight 𝔇 y *
          𝔬 𝔇 =
      𝔛 *
          𝔅 *
          𝔊 := by
    rw [gaussianTrig_cos_difference]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    unfold gaussianPrimitiveLeft gaussianPrimitiveRight gaussianPrimitiveAmplitude
    ring
  simp_rw [hphase]
  have he := Fintype.sum_mul_sum
    (fun s => 𝔅)
     fun s' => 𝔊
  calc
    _ = 𝔛 *
         ∑ s : Bool, ∑ s' : Bool,
          𝔅 *
          𝔊 := by
      simp
      ring
    𝘿 := 𝖤₃

𝗇 𝔘 gaussianAffineFactor h.1.1 h.2.1.1 y * gaussianAffineFactor h.1.2 h.2.1.2 y
𝗇 𝔉 𝔦 * 𝔧
theorem gaussianPrimitive_observable_integrable lam t x y
    β β' :
    Integrable (fun e => 𝔉 * 𝔒)
      $ gaussianPrimitiveMeasure d := by
  let L := ∑ h : GaussianPrimitiveIndex d,
    |𝔘|
  have hm : Measurable fun e =>
      𝔉 :=
    (𝔟 gaussianPrimitiveLeft_measurable x).mul $ 𝔟 gaussianPrimitiveRight_measurable y
  have hb e :
      ‖𝔉‖ ≤ L := by
    unfold gaussianPrimitiveLeft gaussianPrimitiveRight
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
    have htrig := mul_le_mul (𝔟 gaussianTrig_abs_le_one e.1 x e.2.2.2)
      𝔣 (abs_nonneg _) 𝖠₄
    have hl : |𝔡| *
        |𝔢| ≤ L := by
      rw [← abs_mul]
      exact Finset.single_le_sum (fun h _ => abs_nonneg
        𝔘)
        $ Finset.mem_univ e.2
    calc
      _ = |𝔙 e.1 x e.2.2.2| * |𝔙 e.1 y e.2.2.2| *
          (|𝔡| * |𝔢|) := 𝖢₃
      𝖦 := (mul_le_mul_of_nonneg_right htrig $ mul_nonneg (abs_nonneg _) $ abs_nonneg _ ).trans
        $ by simpa using hl
  have hi := (gaussianPrimitiveAmplitude_integrable lam β β').mul_bdd hm.aestronglyMeasurable
    $ Filter.Eventually.of_forall hb
  grind

𝗇 𝔎 t * lam ^ 2 * Real.exp (-(t * lam * 𝖬₁))
𝗇 𝔜 𝔔 * va a * vb b * Real.cos 𝔄
theorem gaussianAffine_coefficient_bilinear lam t (hlam : 𝖺) (ht : 𝘈)
    x y (va vb : Fin d → ℝ) :
    𝔎 *
      (∑ a, 𝔑 * va a) * ∑ b, (y b - x b) * vb b =
      𝔗 * ∑ a : Fin d, ∑ b : Fin d,
        ∫ Z, 𝔜 ∂standardGaussianPi d := by
  simp_rw [standardGaussian_hermite_cos_integral_const,
    𝔟 gaussianSpatialFrequency_squared hlam ht x y]
  unfold gaussianSpatialFrequency
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 𝔞)
  grind

/-- Exact coefficientwise positive separated representation of the original
G_t affine covariance. All Fourier, Fubini, and coefficient identities are
derived from the actual Gaussian product law. -/
theorem gaussianPrimitive_separated_exact lam t (hlam : 𝖺) (ht : 𝘈)
    x y β β' :
    𝔎 *
      𝔖 β * 𝔖 β' =
      ∫ e, 𝔉 *
        𝔒 ∂gaussianPrimitiveMeasure d := by
  rw [gaussianPrimitiveMeasure, integral_prod _ $ 𝔟 gaussianPrimitive_observable_integrable x y β β' ]
  simp only [integral_count, gaussianPrimitive_finite_action]
  let va := fun a => 𝔚
  let vb := fun b => 𝔍
  have hi a b : Integrable (fun Z => 𝔜) $ standardGaussianPi d := by
    have hm : Measurable fun Z => Real.cos
        𝔄 := by
      unfold gaussianPhase
      fun_prop
    exact (((gaussianHermite_integrable a b).mul_const $ va a ).mul_const $ vb b ).mul_bdd
      hm.aestronglyMeasurable $ Filter.Eventually.of_forall fun Z => 𝔠
  rw [integral_const_mul, integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hi a b ]
  simp_rw [integral_finsetSum _ fun b _ => hi _ b ]
  rw [spatialCardinalAffine_gaussian_coeff, spatialCardinalAffine_gaussian_coeff]
  exact 𝔟 gaussianAffine_coefficient_bilinear hlam ht x y va vb

instance gaussianPrimitiveMeasure_finite (d : ℕ) : IsFiniteMeasure $ gaussianPrimitiveMeasure d := by
  unfold gaussianPrimitiveMeasure
  infer_instance

𝗇 𝔏 ℝ × Covariate d
𝗇 𝔐 (measurable_fst.prodMk $ measurable_fst.comp measurable_snd ).prodMk $ measurable_snd.comp measurable_snd
𝗇 𝔤 gaussianTrig lam z.1 z.2
𝗃 𝔪 fun z : 𝔏 => 𝔤 ἀ h.2.2
theorem gaussianPrimitiveLeft_scale_measurable lam x :
    Measurable fun z : ℝ × GaussianPrimitiveMark d => gaussianPrimitiveLeft lam z.1 z.2 x := by
  have hm : Measurable fun z : 𝔏 × GaussianPrimitiveIndex d =>
      gaussianPrimitiveLeft lam z.1.1 (z.1.2, z.2) x := by
    apply measurable_from_prod_countable_left
    intro h
    change Measurable 𝔪 x
    cases h.2.2 <;> simp only [gaussianTrig, Bool.false_eq_true, ite_false, ite_true] <;>
      unfold gaussianPhase <;> fun_prop
  exact hm.comp 𝔐

theorem gaussianPrimitiveRight_scale_measurable lam y :
    Measurable fun z : ℝ × GaussianPrimitiveMark d => gaussianPrimitiveRight lam z.1 z.2 y := by
  have hm : Measurable fun z : 𝔏 × GaussianPrimitiveIndex d =>
      gaussianPrimitiveRight lam z.1.1 (z.1.2, z.2) y := by
    apply measurable_from_prod_countable_left
    intro h
    change Measurable fun z : 𝔏 => 𝔤 y h.2.2 *
      gaussianAffineFactor h.1.1 h.2.1.1 y * gaussianAffineFactor h.1.2 h.2.1.2 y
    have ht : Measurable 𝔪 y := by
      cases h.2.2 <;> simp only [gaussianTrig, Bool.false_eq_true, ite_false, ite_true] <;>
        unfold gaussianPhase <;> fun_prop
    fun_prop
  exact hm.comp 𝔐
