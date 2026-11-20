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

section
variable (d : ℕ)

abbrev GaussianPrimitiveIndex := (Fin d × Fin d) × (Bool × Bool) × Bool
abbrev GaussianPrimitiveMark := Covariate d × GaussianPrimitiveIndex d

def gaussianPrimitiveMeasure : Measure (GaussianPrimitiveMark d) :=
  (standardGaussianPi d).prod Measure.count

end

section
variable {d : ℕ} (lam t : ℝ) (e : GaussianPrimitiveMark d) (Z x y : Covariate d) (β β' : Fin d →₀ ℕ)

def gaussianTrig (s : Bool) : ℝ :=
  if s then Real.sin (gaussianPhase (fun l => Real.sqrt (2 * lam * t) * x l) Z)
  else Real.cos (gaussianPhase (fun l => Real.sqrt (2 * lam * t) * x l) Z)

theorem gaussianTrig_abs_le_one (s : Bool) :
    |gaussianTrig lam t Z x s| ≤ 1 := by
  cases s <;> simp only [gaussianTrig, Bool.false_eq_true, ite_false, ite_true]
  · exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  · exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩

theorem gaussianTrig_cos_difference :
    Real.cos (gaussianPhase (gaussianSpatialFrequency lam t x y) Z) =
      ∑ s, gaussianTrig lam t Z x s * gaussianTrig lam t Z y s := by
  have he : gaussianPhase (gaussianSpatialFrequency lam t x y) Z =
      gaussianPhase (fun l => Real.sqrt (2 * lam * t) * y l) Z -
      gaussianPhase (fun l => Real.sqrt (2 * lam * t) * x l) Z := by
    simp [gaussianPhase, gaussianSpatialFrequency]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [he, Real.cos_sub]
  simp [gaussianTrig] <;> ring

def gaussianAffinePolynomial (a : Fin d) (s : Bool) : MvPolynomial (Fin d) ℝ :=
  if s then C (-8) * X a else C 2

def gaussianAffineFactor (a : Fin d) (s : Bool) (y : Covariate d) : ℝ :=
  if s then 1 else y a / 2

theorem gaussianAffineFactor_abs_le_one {a : Fin d} (s : Bool) {y : Covariate d}
    (hy : |y a| ≤ 2) : |gaussianAffineFactor a s y| ≤ 1 := by
  grind [gaussianAffineFactor]

theorem spatialCardinalAffine_gaussian_expansion :
    spatialCardinalAffine x y =
      ∑ a, C (y a - x a) *
        ∑ s, C (gaussianAffineFactor a s y) * gaussianAffinePolynomial a s := by
  apply Finset.sum_congr rfl
  intro a ha
  simp only [Fintype.sum_bool, gaussianAffineFactor, gaussianAffinePolynomial,
    Bool.false_eq_true, ite_false, ite_true]
  rw [← C_mul]
  have hy : y a / 2 * 2 = y a := by ring
  rw [hy]
  simp only [C_1, one_mul]
  simp
  ring

theorem spatialCardinalAffine_gaussian_coeff :
    (spatialCardinalAffine x y).coeff β =
      ∑ a, (y a - x a) *
        ∑ s, gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff β := by
  rw [spatialCardinalAffine_gaussian_expansion]
  simp only [coeff_sum, coeff_C_mul]

def gaussianPrimitiveLeft : ℝ :=
  gaussianTrig lam t e.1 x e.2.2.2

def gaussianPrimitiveRight : ℝ :=
  gaussianTrig lam t e.1 y e.2.2.2 *
    gaussianAffineFactor e.2.1.1 e.2.2.1.1 y * gaussianAffineFactor e.2.1.2 e.2.2.1.2 y

def gaussianPrimitiveAmplitude : ℝ :=
  lam / 2 * gaussianHermite e.2.1.1 e.2.1.2 e.1 *
    (gaussianAffinePolynomial e.2.1.1 e.2.2.1.1).coeff β *
      (gaussianAffinePolynomial e.2.1.2 e.2.2.1.2).coeff β'

theorem gaussianPrimitiveRight_bound
    {y : Covariate d} (hy : ∀ a, |y a| ≤ 2) : |gaussianPrimitiveRight lam t e y| ≤ 1 := by
  unfold gaussianPrimitiveRight
  rw [abs_mul, abs_mul]
  bound [gaussianTrig_abs_le_one lam t e.1 y e.2.2.2, gaussianAffineFactor_abs_le_one (a := e.2.1.1) e.2.2.1.1 (hy _), gaussianAffineFactor_abs_le_one (a := e.2.1.2) e.2.2.1.2 (hy _)]

end

variable {d : ℕ} (lam t : ℝ) (x y : Covariate d) (β β' : Fin d →₀ ℕ)

theorem gaussianPrimitiveLeft_measurable :
    Measurable (fun e => gaussianPrimitiveLeft lam t e x) := by
  apply measurable_from_prod_countable_left
  intro h
  change Measurable (fun Z => gaussianTrig lam t Z x h.2.2)
  cases h.2.2 <;> simp [gaussianTrig] <;>
    unfold gaussianPhase <;> fun_prop

theorem gaussianPrimitiveRight_measurable :
    Measurable (fun e => gaussianPrimitiveRight lam t e y) := by
  apply measurable_from_prod_countable_left
  intro h
  unfold gaussianPrimitiveRight
  dsimp
  have hm : Measurable (fun Z => gaussianTrig lam t Z y h.2.2) := by
    cases h.2.2 <;> simp [gaussianTrig] <;>
      unfold gaussianPhase <;> fun_prop
  fun_prop

theorem gaussianPrimitiveAmplitude_measurable :
    Measurable (fun e => gaussianPrimitiveAmplitude lam e β β') := by
  apply measurable_from_prod_countable_left
  intro h
  unfold gaussianPrimitiveAmplitude
  dsimp
  have hm : Measurable (fun Z => gaussianHermite h.1.1 h.1.2 Z) :=
    measurable_const.sub ((measurable_pi_apply _).mul (measurable_pi_apply _))
  fun_prop

theorem gaussianPrimitiveAmplitude_slice_integrable (h : GaussianPrimitiveIndex d) :
    Integrable (fun Z => gaussianPrimitiveAmplitude lam (Z, h) β β') (standardGaussianPi d) := by
  change Integrable (fun Z => lam / 2 * gaussianHermite h.1.1 h.1.2 Z *
    (gaussianAffinePolynomial h.1.1 h.2.1.1).coeff β *
    (gaussianAffinePolynomial h.1.2 h.2.1.2).coeff β') (standardGaussianPi d)
  exact (((gaussianHermite_integrable h.1.1 h.1.2).const_mul _).mul_const _).mul_const _

theorem gaussianPrimitiveAmplitude_integrable :
    Integrable (fun e => gaussianPrimitiveAmplitude lam e β β')
      (gaussianPrimitiveMeasure d) :=
  joint_finite_integrable
    (fun h => (gaussianPrimitiveAmplitude_measurable lam β β').comp
      (measurable_id.prodMk measurable_const))
    (gaussianPrimitiveAmplitude_slice_integrable lam β β')

theorem finite_injective_indicator_sum_le_one {I X : Type*} [Fintype I] [DecidableEq X]
    {f : I → X} (hf : Function.Injective f) (x : X) :
    (∑ i, if x = f i then (1 : ℝ) else 0) ≤ 1 := by
  classical
  by_cases hx : ∃ i, f i = x
  · obtain ⟨i, hi⟩ := hx
    have he j : x = f j ↔ j = i := by
      aesop
    simp_rw [he]
    simp
  · have he j : x ≠ f j := by bound
    simp_all

theorem gaussianPrimitive_finite_action (Z : Covariate d)
    (β β' : Fin d →₀ ℕ) :
    (∑ h,
      gaussianPrimitiveLeft lam t (Z, h) x * gaussianPrimitiveRight lam t (Z, h) y *
        gaussianPrimitiveAmplitude lam (Z, h) β β') =
      lam / 2 * ∑ a, ∑ b,
        gaussianHermite a b Z *
          (∑ s, gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff β) *
          (∑ s, gaussianAffineFactor b s y * (gaussianAffinePolynomial b s).coeff β') *
          Real.cos (gaussianPhase (gaussianSpatialFrequency lam t x y) Z) := by
  classical
  simp only [Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hphase s s' :
      (∑ p, gaussianPrimitiveLeft lam t (Z, ((a, b), ((s, s'), p))) x *
        gaussianPrimitiveRight lam t (Z, ((a, b), ((s, s'), p))) y *
          gaussianPrimitiveAmplitude lam (Z, ((a, b), ((s, s'), p))) β β') =
      (lam / 2 * gaussianHermite a b Z * Real.cos
        (gaussianPhase (gaussianSpatialFrequency lam t x y) Z)) *
          (gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff β) *
          (gaussianAffineFactor b s' y * (gaussianAffinePolynomial b s').coeff β') := by
    rw [gaussianTrig_cos_difference]
    simp [gaussianPrimitiveLeft, gaussianPrimitiveRight, gaussianPrimitiveAmplitude] <;> ring
  simp_rw [hphase]
  simp <;> ring

theorem gaussianPrimitive_observable_integrable :
    Integrable (fun e => gaussianPrimitiveLeft lam t e x *
      gaussianPrimitiveRight lam t e y * gaussianPrimitiveAmplitude lam e β β')
      (gaussianPrimitiveMeasure d) := by
  let L := ∑ h : GaussianPrimitiveIndex d,
    |gaussianAffineFactor h.1.1 h.2.1.1 y * gaussianAffineFactor h.1.2 h.2.1.2 y|
  have hm : Measurable (fun e =>
      gaussianPrimitiveLeft lam t e x * gaussianPrimitiveRight lam t e y) :=
    (gaussianPrimitiveLeft_measurable lam t x).mul (gaussianPrimitiveRight_measurable ..)
  have hb e :
      ‖gaussianPrimitiveLeft lam t e x * gaussianPrimitiveRight lam t e y‖ ≤ L := by
    unfold gaussianPrimitiveLeft gaussianPrimitiveRight
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
    have htrig := mul_le_mul (gaussianTrig_abs_le_one lam t e.1 x e.2.2.2)
      (gaussianTrig_abs_le_one lam t e.1 y e.2.2.2) (abs_nonneg _) (by norm_num)
    let affineFactor := gaussianAffineFactor e.2.1.1 e.2.2.1.1 y
    have hl : |affineFactor| *
        |gaussianAffineFactor e.2.1.2 e.2.2.1.2 y| ≤ L := by
      rw [← abs_mul]
      exact Finset.single_le_sum (fun h _ => abs_nonneg
        (gaussianAffineFactor h.1.1 h.2.1.1 y * gaussianAffineFactor h.1.2 h.2.1.2 y))
        (Finset.mem_univ e.2)
    calc
      _ = (|gaussianTrig lam t e.1 x e.2.2.2| * |gaussianTrig lam t e.1 y e.2.2.2|) *
          (|affineFactor| * |gaussianAffineFactor e.2.1.2 e.2.2.1.2 y|) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_right htrig (by positivity)).trans
        (by simpa using hl)
  convert ((gaussianPrimitiveAmplitude_integrable lam β β').mul_bdd hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)) using 1
  funext e
  ring

theorem gaussianAffine_coefficient_bilinear (hlam : 0 ≤ lam) (ht : 0 ≤ t)
    (x y : Covariate d) (va vb : Fin d → ℝ) :
    t * lam ^ 2 * Real.exp (-(t * lam * spatialSquaredDistance x y)) *
      (∑ a, (y a - x a) * va a) * (∑ b, (y b - x b) * vb b) =
      lam / 2 * ∑ a, ∑ b,
        ∫ Z, gaussianHermite a b Z * va a * vb b *
          Real.cos (gaussianPhase (gaussianSpatialFrequency lam t x y) Z) ∂standardGaussianPi d := by
  simp_rw [standardGaussian_hermite_cos_integral_const,
    (by unfold gaussianSpatialFrequency spatialSquaredDistance; simp_rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * lam * t)]; rw [Finset.mul_sum] : ∑ l, gaussianSpatialFrequency lam t x y l ^ 2 = 2 * lam * t * spatialSquaredDistance x y)]
  have he : -(2 * lam * t * spatialSquaredDistance x y) / 2 =
      -(t * lam * spatialSquaredDistance x y) := by ring
  unfold gaussianSpatialFrequency
  simp [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  grind [Real.sq_sqrt (by positivity : 0 ≤ 2 * lam * t)]

/-- Exact coefficientwise positive separated representation of the original
G_t affine covariance. All Fourier, Fubini, and coefficient identities are
derived from the actual Gaussian product law. -/
theorem gaussianPrimitive_separated_exact {lam t : ℝ} (hlam : 0 ≤ lam) (ht : 0 ≤ t)
    (x y : Covariate d) (β β' : Fin d →₀ ℕ) :
    t * lam ^ 2 * Real.exp (-(t * lam * spatialSquaredDistance x y)) *
      (spatialCardinalAffine x y).coeff β * (spatialCardinalAffine x y).coeff β' =
      ∫ e, gaussianPrimitiveLeft lam t e x * gaussianPrimitiveRight lam t e y *
        gaussianPrimitiveAmplitude lam e β β' ∂gaussianPrimitiveMeasure d := by
  rw [gaussianPrimitiveMeasure, integral_prod _ (gaussianPrimitive_observable_integrable ..)]
  simp only [integral_count, gaussianPrimitive_finite_action]
  let va := fun a => ∑ s, gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff β
  let vb := fun b => ∑ s, gaussianAffineFactor b s y * (gaussianAffinePolynomial b s).coeff β'
  have hi a b : Integrable (fun Z => gaussianHermite a b Z * va a * vb b *
      Real.cos (gaussianPhase (gaussianSpatialFrequency lam t x y) Z)) (standardGaussianPi d) := by
    have hm : Measurable (fun Z => Real.cos
        (gaussianPhase (gaussianSpatialFrequency lam t x y) Z)) := by
      unfold gaussianPhase
      fun_prop
    exact (((gaussianHermite_integrable a b).mul_const (va a)).mul_const (vb b)).mul_bdd
      hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun Z => abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩))
  rw [integral_const_mul, integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hi a b))]
  simp_rw [integral_finsetSum _ (fun b _ => hi _ b)]
  rw [spatialCardinalAffine_gaussian_coeff, spatialCardinalAffine_gaussian_coeff]
  solve_by_elim [gaussianAffine_coefficient_bilinear]

theorem gaussianPrimitiveMeasure_finite (d : ℕ) : IsFiniteMeasure (gaussianPrimitiveMeasure d) := by
  unfold gaussianPrimitiveMeasure
  infer_instance

theorem gaussianPrimitiveLeft_scale_measurable :
    Measurable (fun z : ℝ × GaussianPrimitiveMark d => gaussianPrimitiveLeft lam z.1 z.2 x) := by
  have hm : Measurable (fun z : (ℝ × Covariate d) × GaussianPrimitiveIndex d =>
      gaussianPrimitiveLeft lam z.1.1 (z.1.2, z.2) x) := by
    apply measurable_from_prod_countable_left
    intro h
    change Measurable (fun z : ℝ × Covariate d => gaussianTrig lam z.1 z.2 x h.2.2)
    cases h.2.2 <;> simp [gaussianTrig] <;>
      unfold gaussianPhase <;> fun_prop
  exact hm.comp ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
    (measurable_snd.comp measurable_snd))

theorem gaussianPrimitiveRight_scale_measurable :
    Measurable (fun z : ℝ × GaussianPrimitiveMark d => gaussianPrimitiveRight lam z.1 z.2 y) := by
  have hm : Measurable (fun z : (ℝ × Covariate d) × GaussianPrimitiveIndex d =>
      gaussianPrimitiveRight lam z.1.1 (z.1.2, z.2) y) := by
    apply measurable_from_prod_countable_left
    intro h
    change Measurable (fun z : ℝ × Covariate d => gaussianTrig lam z.1 z.2 y h.2.2 *
      gaussianAffineFactor h.1.1 h.2.1.1 y * gaussianAffineFactor h.1.2 h.2.1.2 y)
    have ht : Measurable (fun z : ℝ × Covariate d => gaussianTrig lam z.1 z.2 y h.2.2) := by
      cases h.2.2 <;> simp [gaussianTrig] <;>
        unfold gaussianPhase <;> fun_prop
    fun_prop
  exact hm.comp ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
    (measurable_snd.comp measurable_snd))

end NearlyMinimax
