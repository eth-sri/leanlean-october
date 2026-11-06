module
public import FiniteAmplifier
public import CenteredMixedTrace
import WeylPort.Analytic.RealLaplace

@[expose] public section

noncomputable section
open Finset MeasureTheory InnerProductSpace Set
open scoped InnerProductSpace ComplexOrder
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def finiteMatrixOperator (A : Matrix ι ι ℂ) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  (Matrix.toEuclideanLin A).toContinuousLinearMap

section
variable (A : Matrix ι ι ℂ)
include A
theorem finite_matrix_operator_apply (z : EuclideanSpace ℂ ι) (i : ι) :
    finiteMatrixOperator A z i = ∑ j, A i j*z j := rfl

theorem finite_matrix_operator_basis (i j : ι) :
    finiteMatrixOperator A (EuclideanSpace.basisFun ι ℂ j) i = A i j := by
  simp [finite_matrix_operator_apply,EuclideanSpace.basisFun_apply,PiLp.single_apply]
end

section
variable (A B : Matrix ι ι ℂ)
include A B
theorem finite_matrix_operator_mul :
    finiteMatrixOperator (A*B) = finiteMatrixOperator A*finiteMatrixOperator B := by
  ext z i
  simp only [finite_matrix_operator_apply,mul_apply_eq_comp,
    Matrix.mul_apply,sum_mul,mul_sum,mul_assoc]
  rw [sum_comm]

theorem finite_matrix_operator_sub :
    finiteMatrixOperator (A-B) = finiteMatrixOperator A-finiteMatrixOperator B := by
  ext z i
  simp [finite_matrix_operator_apply,sub_mul,sum_sub_distrib]
end

theorem finite_matrix_operator_trace (A : Matrix ι ι ℂ) :
    (∑ i, inner ℂ (EuclideanSpace.basisFun ι ℂ i)
      (finiteMatrixOperator A (EuclideanSpace.basisFun ι ℂ i))) = Matrix.trace A := by
  simp only [EuclideanSpace.basisFun_inner,finite_matrix_operator_basis,Matrix.trace,Matrix.diag]

/-- Literal frequency vector in the finite time Hilbert space. -/
def finiteTimePhase (W : Finset ℝ) (ξ : ℝ) : EuclideanSpace ℂ W :=
  WithLp.toLp 2 (fun t : W => GuthMaynard.Improvement.phase ((t:ℝ)*ξ))

theorem finite_time_phase_measurable (W : Finset ℝ) : Measurable (finiteTimePhase W) := by
  unfold finiteTimePhase
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  apply Measurable.of_eval
  intro t
  exact phase_measurable.comp (measurable_const.mul measurable_id)

theorem finite_time_phase_norm_sq (W : Finset ℝ) (ξ : ℝ) :
    ‖finiteTimePhase W ξ‖^2 = (W.card:ℝ) := by
  simp [PiLp.norm_sq_eq_of_L2,finiteTimePhase,phase_norm]

def finiteContinuousIntegral (a : ℝ → ℝ) (L : ℝ) (W : Finset ℝ) :
    EuclideanSpace ℂ W →L[ℂ] EuclideanSpace ℂ W :=
  operatorIntegral volume (fun x => ((L*a x:ℝ):ℂ) • finiteTimePhase W (mellinFrequency x))
    (fun x => finiteTimePhase W (mellinFrequency x))

section
variable {a : ℝ → ℝ} (ha : Integrable a)
include a ha
theorem finite_continuous_integrable (L : ℝ) (W : Finset ℝ) :
    Integrable (fun x => rankOne ℂ (((L*a x:ℝ):ℂ) • finiteTimePhase W (mellinFrequency x))
      (finiteTimePhase W (mellinFrequency x))) := by
  have hm : AEStronglyMeasurable (fun x => finiteTimePhase W (mellinFrequency x)) volume := by
    apply ((finite_time_phase_measurable W).comp ?_).aestronglyMeasurable
    unfold mellinFrequency
    fun_prop
  apply operatorIntegral_integrable volume
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable
      (ha.aestronglyMeasurable.const_mul L)).smul hm) hm
  have he (x : ℝ) : ‖((L*a x:ℝ):ℂ) • finiteTimePhase W (mellinFrequency x)‖ *
      ‖finiteTimePhase W (mellinFrequency x)‖ = ‖L*a x‖*(W.card:ℝ) := by
    rw [norm_smul,Complex.norm_real,mul_assoc,← pow_two,finite_time_phase_norm_sq]
  change Integrable (fun x => ‖((L*a x:ℝ):ℂ) • finiteTimePhase W (mellinFrequency x)‖ *
      ‖finiteTimePhase W (mellinFrequency x)‖)
  pm_8935 ha.const_mul

theorem finite_continuous_positive (h0 : ∀ x, 0 ≤ a x)
    {L : ℝ} (hL : 0 ≤ L) (W : Finset ℝ) : (finiteContinuousIntegral a L W).IsPositive := by
  apply operator_integral_positive volume (finite_continuous_integrable ha L W)
  filter_upwards with x
  rw [map_smul,smul_apply]
  pm_8593 h0

/-- Coefficients of the actual Bochner continuous correction. -/
theorem finite_continuous_entry (L : ℝ) (W : Finset ℝ)
    (t u : W) :
    finiteContinuousIntegral a L W (EuclideanSpace.basisFun W ℂ u) t =
      (L:ℂ)*∫ x, (a x:ℂ)*GuthMaynard.Improvement.phase (((t:ℝ)-u)*mellinFrequency x) := by
  have hi := finite_continuous_integrable ha L W
  have hi' : Integrable (fun x => rankOne ℂ
      (((L*a x:ℝ):ℂ) • finiteTimePhase W (mellinFrequency x))
      (finiteTimePhase W (mellinFrequency x)) (EuclideanSpace.basisFun W ℂ u)) :=
    (ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ W) (EuclideanSpace.basisFun W ℂ u)).integrable_comp hi
  rw [← EuclideanSpace.basisFun_inner,finiteContinuousIntegral,operatorIntegral,
    ContinuousLinearMap.integral_apply hi,← integral_inner hi']
  have he (x : ℝ) : inner ℂ (EuclideanSpace.basisFun W ℂ t)
      (rankOne ℂ (((L*a x:ℝ):ℂ) • finiteTimePhase W (mellinFrequency x))
        (finiteTimePhase W (mellinFrequency x)) (EuclideanSpace.basisFun W ℂ u)) =
      (L:ℂ)*((a x:ℂ)*GuthMaynard.Improvement.phase (((t:ℝ)-u)*mellinFrequency x)) := by
    rw [rankOne_apply,inner_smul_right,inner_smul_right,
      ← inner_conj_symm _ (EuclideanSpace.basisFun W ℂ u),EuclideanSpace.basisFun_inner,
      EuclideanSpace.basisFun_inner]
    simp only [finiteTimePhase,
      operator_phase_conj,Complex.ofReal_mul]
    rw [show (((t:ℝ)-u)*mellinFrequency x) = (t:ℝ)*mellinFrequency x+(-((u:ℝ)*mellinFrequency x)) by ring,phase_add]
    ring
  simp_rw [he]
  rw [integral_const_mul]
end

section
variable (w : MathCollab.Density.ReflectionCutoff)
include w
theorem reflection_square_integrable :
    Integrable (fun x : ℝ => w x^2) := by
  apply (w.smooth.continuous.pow 2).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro isCompact_Icc
  pm_4496
  simp [hz]

/-- Whole-space and positive-half-line cutoff normalizations agree exactly. -/
theorem cutoff_integral_whole (s : ℝ) :
    (∫ x, (w x:ℂ)*GuthMaynard.Improvement.phase (s*mellinFrequency x)) =
      MathCollab.Density.cutoffIntegral w s := by
  unfold MathCollab.Density.cutoffIntegral
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    have hz : w x=0 := image_eq_zero_of_notMem_tsupport (fun hh => by
      have hpos := (w.support hh).1
      exact hx (by change 0 < x; linarith))
    simp [hz])]
  apply integral_congr_ae
  filter_upwards with x
  pm_8451 mellinFrequency_phase MathCollab.Density.dirichletPhase

theorem finite_continuous_cutoff_entry (L : ℝ)
    (W : Finset ℝ) (t u : W) :
    finiteContinuousIntegral (fun x => w x^2) L W (EuclideanSpace.basisFun W ℂ u) t =
      cutoffContinuousMatrix w L W t u := by
  rw [finite_continuous_entry (reflection_square_integrable w)]
  change (L:ℂ)*(∫ x, ((reflectionSquare w) x:ℂ)*
    GuthMaynard.Improvement.phase (((t:ℝ)-u)*mellinFrequency x)) = _
  rw [cutoff_integral_whole]
  rfl

/-- The finite divisor construction has the same natural-number Gram entries
as the separately formalized reflection matrix. -/
theorem finite_cutoff_gram_natural_entry
    {L : ℝ} (hL : 0 < L) (W : Finset ℝ) (t u : W) :
    finiteCutoffGram w L (1/2) 5 W (EuclideanSpace.basisFun W ℂ u) t =
      cutoffGramMatrix w L W t u := by
  rw [finite_cutoff_gram_entry]
  have he := centeredKernel_eq_density_hKernel (reflectionSquare w) hL ((t:ℝ)-u)
  unfold centeredKernel MathCollab.Density.hKernel at he
  simp_rw [logModulated_eq_phase] at he
  rw [cutoff_integral_whole] at he
  have hh := sub_left_inj.mp he
  simpa only [reflectionSquare,Complex.ofReal_pow,cutoffGramMatrix] using hh

theorem finite_cutoff_gram_eq
    {L : ℝ} (hL : 0 < L) (W : Finset ℝ) :
    finiteMatrixOperator (cutoffGramMatrix w L W) = finiteCutoffGram w L (1/2) 5 W := by
  pm_5492 finite_cutoff_gram_natural_entry hL

theorem finite_cutoff_continuous_eq
    (L : ℝ) (W : Finset ℝ) :
    finiteMatrixOperator (cutoffContinuousMatrix w L W) =
      finiteContinuousIntegral (fun x => w x^2) L W := by
  pm_5492 finite_continuous_cutoff_entry L

/-- Positivity of both actual finite Gram matrices is proved from their
constructed feature maps and positive continuous frequency integral. -/
theorem cutoff_matrix_operators_positive
    {L : ℝ} (hL : 0 < L) (W : Finset ℝ) :
    (finiteMatrixOperator (cutoffGramMatrix w L W)).IsPositive ∧
      (finiteMatrixOperator (cutoffContinuousMatrix w L W)).IsPositive := by
  rw [finite_cutoff_gram_eq w hL W,finite_cutoff_continuous_eq]
  exact ⟨ContinuousLinearMap.isPositive_self_comp_adjoint _,
    finite_continuous_positive (reflection_square_integrable w) (fun _ => sq_nonneg _) hL.le W⟩
end

/-- Finite Schur bound, proved directly on the quadratic form. -/
theorem finite_matrix_schur_quadratic (A : Matrix ι ι ℂ) {B : ℝ}
    (hr : ∀ i, ∑ j, ‖A i j‖ ≤ B) (hc : ∀ j, ∑ i, ‖A i j‖ ≤ B)
    (z : EuclideanSpace ℂ ι) :
    (inner ℂ z (finiteMatrixOperator A z)).re ≤ B*‖z‖^2 := by
  have hfirst : (∑ i, ∑ j, ‖A i j‖*‖z i‖^2) ≤ B*‖z‖^2 := by
    pm_5946 i hr
  have hsecond : (∑ i, ∑ j, ‖A i j‖*‖z j‖^2) ≤ B*‖z‖^2 := by
    rw [sum_comm]
    pm_5946 j hc
  have he : inner ℂ z (finiteMatrixOperator A z) = ∑ i, ∑ j, star (z i)*A i j*z j := by
    pm_94 PiLp.inner_apply finite_matrix_operator_apply RCLike.inner_apply sum_mul starRingEnd_apply
    pm_156 sum_congr i j
    ring
  rw [he]
  calc
    _ ≤ ‖∑ i, ∑ j, star (z i)*A i j*z j‖ := Complex.re_le_norm _
    _ ≤ ∑ i, ∑ j, ‖star (z i)*A i j*z j‖ :=
      (norm_sum_le _ _).trans (sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ i, ∑ j, (‖A i j‖*‖z i‖^2+‖A i j‖*‖z j‖^2)/2 := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro j _
      simp only [norm_mul,norm_star]
      nlinarith [mul_nonneg (norm_nonneg (A i j)) (sq_nonneg (‖z i‖-‖z j‖))]
    _ = ((∑ i, ∑ j, ‖A i j‖*‖z i‖^2)+(∑ i, ∑ j, ‖A i j‖*‖z j‖^2))/2 := by
      pm_1444 div_eq_mul_inv add_mul Finset.sum_add_distrib Finset.sum_mul
    _ ≤ _ := by linarith

/-- Uniform operator norm of the actual continuous matrix on a separated W. -/
theorem cutoff_continuous_operator_norm (w : MathCollab.Density.ReflectionCutoff) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ L : ℝ, 0 < L → ∀ W : Finset ℝ,
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      ‖finiteMatrixOperator (cutoffContinuousMatrix w L W)‖ ≤ B*L := by
  pm_102 B hB h cutoff_continuous_schur w
  intro L hL W hsep
  obtain ⟨hr,hc⟩ := h L hL.le W hsep
  exact operator_positive_norm_of_quadratic _ (cutoff_matrix_operators_positive w hL W).2
    (mul_nonneg hB hL.le) (finite_matrix_schur_quadratic _ hr hc)

theorem finite_matrix_operator_one : finiteMatrixOperator (1 : Matrix ι ι ℂ) = 1 := by
  ext z i
  simp [finite_matrix_operator_apply,Matrix.one_apply]

theorem finite_matrix_operator_pow (A : Matrix ι ι ℂ) (n : ℕ) :
    finiteMatrixOperator (A^n) = (finiteMatrixOperator A)^n := by
  induction n with
  | zero => simp only [pow_zero,finite_matrix_operator_one]
  | succ n ih => rw [pow_succ,finite_matrix_operator_mul,ih,pow_succ]

end Montgomery.RationalMoment
