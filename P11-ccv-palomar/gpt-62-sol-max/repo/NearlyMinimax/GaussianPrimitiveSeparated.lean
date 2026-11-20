module

public import NearlyMinimax.GaussianAffineRepresentation
public import NearlyMinimax.HighSeparatedRows
public import NearlyMinimax.ActualSeparatedPacket

@[expose] public section

/-! A genuine positive Gaussian separated representation of the exact
two-observation affine covariance building block, with bounded factors and
uniform integrated coefficient cost. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set MvPolynomial
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

abbrev GaussianPrimitiveIndex (d : ℕ) := (Fin d × Fin d) × (Bool × Bool) × Bool
abbrev GaussianPrimitiveMark (d : ℕ) := Covariate d × GaussianPrimitiveIndex d

def gaussianPrimitiveMeasure (d : ℕ) : Measure (GaussianPrimitiveMark d) :=
  (standardGaussianPi d).prod Measure.count

def gaussianTrig {d : ℕ} (lam t : ℝ) (Z x : Covariate d) (s : Bool) : ℝ :=
  if s then Real.sin (gaussianPhase (fun l => Real.sqrt (2 * lam * t) * x l) Z)
  else Real.cos (gaussianPhase (fun l => Real.sqrt (2 * lam * t) * x l) Z)

section
variable {d : ℕ} (lam t : ℝ)

theorem gaussianTrig_abs_le_one (Z x : Covariate d) (s : Bool) :
    |gaussianTrig lam t Z x s| ≤ 1 := by
  cases s <;> simp only [gaussianTrig, Bool.false_eq_true, ite_false, ite_true]
  · exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  · exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩

theorem gaussianTrig_cos_difference (Z x y : Covariate d) :
    Real.cos (gaussianPhase (gaussianSpatialFrequency lam t x y) Z) =
      ∑ s : Bool, gaussianTrig lam t Z x s * gaussianTrig lam t Z y s := by
  have he : gaussianPhase (gaussianSpatialFrequency lam t x y) Z =
      gaussianPhase (fun l => Real.sqrt (2 * lam * t) * y l) Z -
      gaussianPhase (fun l => Real.sqrt (2 * lam * t) * x l) Z := by
    simp only [gaussianPhase, gaussianSpatialFrequency]
    rw [← Finset.sum_sub_distrib] <;> grind
  rw [he, Real.cos_sub]
  simp only [Fintype.sum_bool, gaussianTrig, Bool.false_eq_true, ite_false, ite_true]
  ring

end

def gaussianAffinePolynomial {d : ℕ} (a : Fin d) (s : Bool) : MvPolynomial (Fin d) ℝ :=
  if s then C (-8) * X a else C 2

def gaussianAffineFactor {d : ℕ} (a : Fin d) (s : Bool) (y : Covariate d) : ℝ :=
  if s then 1 else y a / 2

section
variable {d : ℕ}

theorem gaussianAffineFactor_abs_le_one (a : Fin d) (s : Bool) (y : Covariate d)
    (hy : |y a| ≤ 2) : |gaussianAffineFactor a s y| ≤ 1 := by
  grind [gaussianAffineFactor]

section
variable (x y : Covariate d)

theorem spatialCardinalAffine_gaussian_expansion :
    spatialCardinalAffine x y =
      ∑ a : Fin d, C (y a - x a) *
        ∑ s : Bool, C (gaussianAffineFactor a s y) * gaussianAffinePolynomial a s := by
  unfold spatialCardinalAffine
  apply Finset.sum_congr rfl
  intro a ha
  simp only [Fintype.sum_bool, gaussianAffineFactor, gaussianAffinePolynomial,
    Bool.false_eq_true, ite_false, ite_true]
  rw [← C_mul]
  have hy : y a / 2 * 2 = y a := by ring
  simp [hy] <;> ring

theorem spatialCardinalAffine_gaussian_coeff (β : Fin d →₀ ℕ) :
    (spatialCardinalAffine x y).coeff β =
      ∑ a : Fin d, (y a - x a) *
        ∑ s : Bool, gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff β := by
  rw [spatialCardinalAffine_gaussian_expansion]
  simp only [coeff_sum, coeff_C_mul]

end

end

def gaussianPrimitiveLeft {d : ℕ} (lam t : ℝ) (e : GaussianPrimitiveMark d) (x : Covariate d) : ℝ :=
  gaussianTrig lam t e.1 x e.2.2.2

def gaussianPrimitiveRight {d : ℕ} (lam t : ℝ) (e : GaussianPrimitiveMark d) (y : Covariate d) : ℝ :=
  gaussianTrig lam t e.1 y e.2.2.2 *
    gaussianAffineFactor e.2.1.1 e.2.2.1.1 y * gaussianAffineFactor e.2.1.2 e.2.2.1.2 y

def gaussianPrimitiveAmplitude {d : ℕ} (lam : ℝ) (e : GaussianPrimitiveMark d)
    (β β' : Fin d →₀ ℕ) : ℝ :=
  lam / 2 * gaussianHermite e.2.1.1 e.2.1.2 e.1 *
    (gaussianAffinePolynomial e.2.1.1 e.2.2.1.1).coeff β *
      (gaussianAffinePolynomial e.2.1.2 e.2.2.1.2).coeff β'

section
variable {d : ℕ}

section
variable (lam t : ℝ) (e : GaussianPrimitiveMark d)

theorem gaussianPrimitiveLeft_bound (x : Covariate d) :
    |gaussianPrimitiveLeft lam t e x| ≤ 1 := gaussianTrig_abs_le_one _ _ _ _ _

theorem gaussianPrimitiveRight_bound
    (y : Covariate d) (hy : ∀ a, |y a| ≤ 2) : |gaussianPrimitiveRight lam t e y| ≤ 1 := by
  unfold gaussianPrimitiveRight
  rw [abs_mul, abs_mul]
  have h1 := gaussianTrig_abs_le_one lam t e.1 y e.2.2.2
  have h2 := gaussianAffineFactor_abs_le_one e.2.1.1 e.2.2.1.1 y (hy _)
  have h3 := gaussianAffineFactor_abs_le_one e.2.1.2 e.2.2.1.2 y (hy _)
  exact (mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)) h3
    (abs_nonneg _) (by norm_num)).trans_eq (by ring)

end

section
variable (lam : ℝ)

theorem gaussianPrimitiveLeft_scale_measurable (x : Covariate d) :
    Measurable (fun z : ℝ × GaussianPrimitiveMark d => gaussianPrimitiveLeft lam z.1 z.2 x) := by
  unfold gaussianPrimitiveLeft gaussianTrig gaussianPhase
  refine Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const) ?_ ?_ <;> fun_prop

theorem gaussianPrimitiveRight_scale_measurable (y : Covariate d) :
    Measurable (fun z : ℝ × GaussianPrimitiveMark d => gaussianPrimitiveRight lam z.1 z.2 y) :=
  ((gaussianPrimitiveLeft_scale_measurable lam y).mul
    ((measurable_of_countable (fun h : GaussianPrimitiveIndex d => gaussianAffineFactor h.1.1 h.2.1.1 y)).comp
      (measurable_snd.comp measurable_snd))).mul
    ((measurable_of_countable (fun h : GaussianPrimitiveIndex d => gaussianAffineFactor h.1.2 h.2.1.2 y)).comp
      (measurable_snd.comp measurable_snd))

theorem gaussianPrimitiveAmplitude_measurable (β β' : Fin d →₀ ℕ) :
    Measurable (fun e : GaussianPrimitiveMark d => gaussianPrimitiveAmplitude lam e β β') := by
  apply measurable_from_prod_countable_left
  intro h
  unfold gaussianPrimitiveAmplitude
  dsimp only
  have hm : Measurable (fun Z : Covariate d => gaussianHermite h.1.1 h.1.2 Z) :=
    measurable_const.sub ((measurable_pi_apply _).mul (measurable_pi_apply _))
  exact ((hm.const_mul _).mul_const _).mul_const _

theorem gaussianPrimitiveAmplitude_slice_integrable
    (β β' : Fin d →₀ ℕ) (h : GaussianPrimitiveIndex d) :
    Integrable (fun Z => gaussianPrimitiveAmplitude lam (Z, h) β β') (standardGaussianPi d) := by
  change Integrable (fun Z => lam / 2 * gaussianHermite h.1.1 h.1.2 Z *
    (gaussianAffinePolynomial h.1.1 h.2.1.1).coeff β *
    (gaussianAffinePolynomial h.1.2 h.2.1.2).coeff β') (standardGaussianPi d)
  exact (((gaussianHermite_integrable h.1.1 h.1.2).const_mul _).mul_const _).mul_const _

theorem gaussianPrimitiveAmplitude_integrable (β β' : Fin d →₀ ℕ) :
    Integrable (fun e : GaussianPrimitiveMark d => gaussianPrimitiveAmplitude lam e β β')
      (gaussianPrimitiveMeasure d) :=
  joint_finite_integrable _ _
    (fun h => (gaussianPrimitiveAmplitude_measurable lam β β').comp
      (measurable_id.prodMk measurable_const))
    (gaussianPrimitiveAmplitude_slice_integrable lam β β')

end

end

theorem finite_injective_indicator_sum_le_one {I X : Type*} [Fintype I] [DecidableEq X]
    (f : I → X) (hf : Function.Injective f) (x : X) :
    (∑ i, if x = f i then (1 : ℝ) else 0) ≤ 1 := by
  classical
  by_cases hx : ∃ i, f i = x
  · obtain ⟨i, hi⟩ := hx
    have he (j : I) : x = f j ↔ j = i := by
      grind
    simp_rw [he]
    simp
  · have he (j : I) : x ≠ f j := by grind
    simp only [ite_eq_right (he _), Finset.sum_const_zero]
    norm_num

section
variable {d : ℕ} (lam t : ℝ)

theorem gaussianPrimitive_finite_action (x y Z : Covariate d)
    (β β' : Fin d →₀ ℕ) :
    (∑ h : GaussianPrimitiveIndex d,
      gaussianPrimitiveLeft lam t (Z, h) x * gaussianPrimitiveRight lam t (Z, h) y *
        gaussianPrimitiveAmplitude lam (Z, h) β β') =
      lam / 2 * ∑ a : Fin d, ∑ b : Fin d,
        gaussianHermite a b Z *
          (∑ s : Bool, gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff β) *
          (∑ s : Bool, gaussianAffineFactor b s y * (gaussianAffinePolynomial b s).coeff β') *
          Real.cos (gaussianPhase (gaussianSpatialFrequency lam t x y) Z) := by
  classical
  simp only [Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hphase (s s' : Bool) :
      (∑ p : Bool, gaussianPrimitiveLeft lam t (Z, ((a, b), ((s, s'), p))) x *
        gaussianPrimitiveRight lam t (Z, ((a, b), ((s, s'), p))) y *
          gaussianPrimitiveAmplitude lam (Z, ((a, b), ((s, s'), p))) β β') =
      (lam / 2 * gaussianHermite a b Z * Real.cos
        (gaussianPhase (gaussianSpatialFrequency lam t x y) Z)) *
          (gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff β) *
          (gaussianAffineFactor b s' y * (gaussianAffinePolynomial b s').coeff β') := by
    rw [gaussianTrig_cos_difference]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    unfold gaussianPrimitiveLeft gaussianPrimitiveRight gaussianPrimitiveAmplitude
    dsimp only
    ring
  simp_rw [hphase]
  have he := Fintype.sum_mul_sum
    (fun s : Bool => gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff β)
    (fun s' : Bool => gaussianAffineFactor b s' y * (gaussianAffinePolynomial b s').coeff β')
  calc
    _ = (lam / 2 * gaussianHermite a b Z * Real.cos
        (gaussianPhase (gaussianSpatialFrequency lam t x y) Z)) *
        (∑ s : Bool, ∑ s' : Bool,
          (gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff β) *
          (gaussianAffineFactor b s' y * (gaussianAffinePolynomial b s').coeff β')) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro s' hs'
      ring
    _ = _ := by rw [← he]; ring

theorem gaussianPrimitive_observable_integrable (x y : Covariate d)
    (β β' : Fin d →₀ ℕ) :
    Integrable (fun e : GaussianPrimitiveMark d => gaussianPrimitiveLeft lam t e x *
      gaussianPrimitiveRight lam t e y * gaussianPrimitiveAmplitude lam e β β')
      (gaussianPrimitiveMeasure d) := by
  let L := ∑ h : GaussianPrimitiveIndex d,
    |gaussianAffineFactor h.1.1 h.2.1.1 y * gaussianAffineFactor h.1.2 h.2.1.2 y|
  have hm : Measurable (fun e : GaussianPrimitiveMark d =>
      gaussianPrimitiveLeft lam t e x * gaussianPrimitiveRight lam t e y) :=
    ((gaussianPrimitiveLeft_scale_measurable lam x).comp (measurable_const.prodMk measurable_id)).mul
      ((gaussianPrimitiveRight_scale_measurable lam y).comp (measurable_const.prodMk measurable_id))
  have hb (e : GaussianPrimitiveMark d) :
      ‖gaussianPrimitiveLeft lam t e x * gaussianPrimitiveRight lam t e y‖ ≤ L := by
    unfold gaussianPrimitiveLeft gaussianPrimitiveRight
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
    have htrig := mul_le_mul (gaussianTrig_abs_le_one lam t e.1 x e.2.2.2)
      (gaussianTrig_abs_le_one lam t e.1 y e.2.2.2) (abs_nonneg _) (by norm_num)
    have hl : |gaussianAffineFactor e.2.1.1 e.2.2.1.1 y| *
        |gaussianAffineFactor e.2.1.2 e.2.2.1.2 y| ≤ L := by
      simpa only [← abs_mul] using Finset.single_le_sum (fun h _ => abs_nonneg
              (gaussianAffineFactor h.1.1 h.2.1.1 y * gaussianAffineFactor h.1.2 h.2.1.2 y))
              (Finset.mem_univ e.2)
    calc
      _ = (|gaussianTrig lam t e.1 x e.2.2.2| * |gaussianTrig lam t e.1 y e.2.2.2|) *
          (|gaussianAffineFactor e.2.1.1 e.2.2.1.1 y| * |gaussianAffineFactor e.2.1.2 e.2.2.1.2 y|) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_right htrig (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans
        (by simpa using hl)
  have hi := (gaussianPrimitiveAmplitude_integrable lam β β').mul_bdd hm.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)
  convert hi using 1
  funext e
  ring

section
variable (hlam : 0 ≤ lam) (ht : 0 ≤ t)
    (x y : Covariate d)
include hlam ht

theorem gaussianAffine_coefficient_bilinear (va vb : Fin d → ℝ) :
    t * lam ^ 2 * Real.exp (-(t * lam * spatialSquaredDistance x y)) *
      (∑ a, (y a - x a) * va a) * (∑ b, (y b - x b) * vb b) =
      lam / 2 * ∑ a : Fin d, ∑ b : Fin d,
        ∫ Z, gaussianHermite a b Z * va a * vb b *
          Real.cos (gaussianPhase (gaussianSpatialFrequency lam t x y) Z) ∂standardGaussianPi d := by
  simp_rw [standardGaussian_hermite_cos_integral_const,
    gaussianSpatialFrequency_squared lam t hlam ht x y]
  have he : -(2 * lam * t * spatialSquaredDistance x y) / 2 =
      -(t * lam * spatialSquaredDistance x y) := by ring
  rw [he]
  unfold gaussianSpatialFrequency
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 2 * lam * t)
  grind

/-- Exact coefficientwise positive separated representation of the original
G_t affine covariance. All Fourier, Fubini, and coefficient identities are
derived from the actual Gaussian product law. -/
theorem gaussianPrimitive_separated_exact (β β' : Fin d →₀ ℕ) :
    t * lam ^ 2 * Real.exp (-(t * lam * spatialSquaredDistance x y)) *
      (spatialCardinalAffine x y).coeff β * (spatialCardinalAffine x y).coeff β' =
      ∫ e, gaussianPrimitiveLeft lam t e x * gaussianPrimitiveRight lam t e y *
        gaussianPrimitiveAmplitude lam e β β' ∂gaussianPrimitiveMeasure d := by
  rw [gaussianPrimitiveMeasure, integral_prod _ (gaussianPrimitive_observable_integrable lam t x y β β')]
  simp only [integral_count, gaussianPrimitive_finite_action]
  let va := fun a : Fin d => ∑ s : Bool, gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff β
  let vb := fun b : Fin d => ∑ s : Bool, gaussianAffineFactor b s y * (gaussianAffinePolynomial b s).coeff β'
  have hi (a b : Fin d) : Integrable (fun Z : Covariate d => gaussianHermite a b Z * va a * vb b *
      Real.cos (gaussianPhase (gaussianSpatialFrequency lam t x y) Z)) (standardGaussianPi d) := by
    have hm : Measurable (fun Z : Covariate d => Real.cos
        (gaussianPhase (gaussianSpatialFrequency lam t x y) Z)) := by
      unfold gaussianPhase
      fun_prop
    exact (((gaussianHermite_integrable a b).mul_const (va a)).mul_const (vb b)).mul_bdd
      hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun Z => abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩))
  change _ = ∫ Z, lam / 2 * ∑ a : Fin d, ∑ b : Fin d,
    gaussianHermite a b Z * va a * vb b * Real.cos
      (gaussianPhase (gaussianSpatialFrequency lam t x y) Z) ∂standardGaussianPi d
  rw [integral_const_mul, integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hi a b))]
  simpa only [integral_finsetSum _ (fun b _ => hi _ b), spatialCardinalAffine_gaussian_coeff] using gaussianAffine_coefficient_bilinear lam t hlam ht x y va vb

end

end

instance gaussianPrimitiveMeasure_finite (d : ℕ) : IsFiniteMeasure (gaussianPrimitiveMeasure d) := by
  unfold gaussianPrimitiveMeasure
  infer_instance

end NearlyMinimax
