module

public import NearlyMinimax.FinePairReference
public import NearlyMinimax.BoundedHyperplaneField
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section

/-! The fine density packet with the actual bounded hyperplane field,
and the genuine Lebesgue-time/field carrier of the coarse and fine rows. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

abbrev FinePairFieldMark (d : ℕ) := partitionFieldMark (Covariate d × ℝ)

theorem boundedHyperplaneFieldValue_section_measurable (d : ℕ) (u : Covariate d) :
    Measurable (fun z : FinePairFieldMark d => boundedHyperplaneFieldValue z u) :=
  (boundedHyperplaneFieldValue_measurable d).comp (measurable_id.prodMk measurable_const)

def finePairFieldKernel (d : ℕ) : Kernel ℝ (FinePairFieldMark d) where
  toFun := boundedHyperplaneFieldLaw d
  measurable' := boundedHyperplaneFieldLaw_measurable d

instance finePairFieldKernel_markov (d : ℕ) [NeZero d] : IsMarkovKernel (finePairFieldKernel d) :=
  ⟨fun T => boundedHyperplaneFieldLaw_probability d T⟩

def finePairTimeFieldMeasure (d : ℕ) (lo hi : ℝ) : Measure (ℝ × FinePairFieldMark d) :=
  (volume.restrict (Icc lo hi)).compProd (finePairFieldKernel d)

instance finePairTimeFieldMeasure_finite (d : ℕ) [NeZero d] (lo hi : ℝ) :
    IsFiniteMeasure (finePairTimeFieldMeasure d lo hi) := by
  unfold finePairTimeFieldMeasure
  infer_instance

theorem finePairTimeFieldMeasure_integral (d : ℕ) [NeZero d] (lo hi : ℝ)
    (f : ℝ × FinePairFieldMark d → ℝ) (hf : Integrable f (finePairTimeFieldMeasure d lo hi)) :
    (∫ e, f e ∂finePairTimeFieldMeasure d lo hi) =
      ∫ T in Icc lo hi, ∫ z, f (T,z) ∂boundedHyperplaneFieldLaw d T :=
  Measure.integral_compProd hf

def finePairTimeFieldValue {d : ℕ} (e : ℝ × FinePairFieldMark d) (u : Covariate d) : ℝ :=
  boundedHyperplaneFieldValue e.2 u

theorem finePairTimeFieldValue_measurable (d : ℕ) :
    Measurable (fun ex : (ℝ × FinePairFieldMark d) × Covariate d =>
      finePairTimeFieldValue ex.1 ex.2) :=
  (boundedHyperplaneFieldValue_measurable d).comp
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

section
variable {d : ℕ}

theorem finePairTimeFieldValue_section_measurable (u : Covariate d) :
    Measurable (fun e : ℝ × FinePairFieldMark d => finePairTimeFieldValue e u) :=
  (boundedHyperplaneFieldValue_section_measurable d u).comp measurable_snd

theorem finePairTimeFieldValue_abs (e : ℝ × FinePairFieldMark d) (u : Covariate d) :
    |finePairTimeFieldValue e u| = 1 := boundedHyperplaneFieldValue_abs _ _

end

section
variable (d : ℕ) [NeZero d] (lo hi : ℝ)

theorem finePairTimeFieldMeasure_ae_time :
    ∀ᵐ e ∂finePairTimeFieldMeasure d lo hi, e.1 ∈ Icc lo hi :=
  Measure.ae_compProd_of_ae_fst (finePairFieldKernel d) measurableSet_Icc
    (ae_restrict_mem measurableSet_Icc)

theorem finePairTimeFieldMeasure_fst_integrable :
    Integrable (fun e : ℝ × FinePairFieldMark d => e.1) (finePairTimeFieldMeasure d lo hi) := by
  apply (integrable_const (max |lo| |hi|)).mono' measurable_fst.aestronglyMeasurable
  filter_upwards [finePairTimeFieldMeasure_ae_time d lo hi] with e he
  exact abs_le.mpr ⟨by linarith [neg_abs_le lo, le_max_left |lo| |hi|, he.1],
      by linarith [le_abs_self hi, le_max_right |lo| |hi|, he.2]⟩

theorem finePairTimeFieldMeasure_fst_integral :
    (∫ e : ℝ × FinePairFieldMark d, e.1 ∂finePairTimeFieldMeasure d lo hi) =
      ∫ T in Icc lo hi, T := by
  simp [finePairTimeFieldMeasure_integral d lo hi _ (finePairTimeFieldMeasure_fst_integrable d lo hi)]

end

section Matrix
variable {ι : Type*} [Fintype ι]

def finePairTimeMatrix (d : ℕ) (A : ι → ι → ℝ) (e : ℝ × FinePairFieldMark d) : ι → ι → ℝ :=
  fun i j => e.1 * A i j

section
variable (d : ℕ)

section
variable (A : ι → ι → ℝ)

theorem finePairTimeMatrix_measurable (i j : ι) :
    Measurable (fun e => finePairTimeMatrix d A e i j) := measurable_fst.mul_const _

theorem finePairTimeMatrix_cost (e : ℝ × FinePairFieldMark d) :
    separatedMatrixCost (finePairTimeMatrix d A) e =
      |e.1| * (∑ i, ∑ j, |A i j|) := by
  simp only [separatedMatrixCost, finePairTimeMatrix, abs_mul, Finset.mul_sum]

end

theorem finePairTimeMatrix_integrable [NeZero d] (lo hi : ℝ) (A : ι → ι → ℝ) :
    SeparatedMatrixIntegrable (finePairTimeFieldMeasure d lo hi) (finePairTimeMatrix d A) := by
  classical
  exact .of_entries (finePairTimeMatrix_measurable d A)
    (fun i j => (finePairTimeFieldMeasure_fst_integrable d lo hi).mul_const (A i j))

end

end Matrix

section
variable (d : ℕ) [NeZero d] (lo hi : ℝ)

theorem finePairTimeFieldValue_weighted_pair_integrable
    (u v : Covariate d) :
    Integrable (fun e => e.1 * (finePairTimeFieldValue e u * finePairTimeFieldValue e v))
      (finePairTimeFieldMeasure d lo hi) := by
  refine (finePairTimeFieldMeasure_fst_integrable d lo hi).mul_bdd (c := 1)
    ((finePairTimeFieldValue_section_measurable u).mul
      (finePairTimeFieldValue_section_measurable v)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e => by
      change ‖finePairTimeFieldValue e u * finePairTimeFieldValue e v‖ ≤ 1
      simp only [Real.norm_eq_abs, abs_mul, finePairTimeFieldValue_abs, one_mul, le_refl]))

theorem finePairTimeFieldValue_weighted_covariance
    (hlo : 0 ≤ lo) (u v : Covariate d) (hu : u ∈ hyperplaneCube d) (hv : v ∈ hyperplaneCube d) :
    (∫ e, e.1 * (finePairTimeFieldValue e u * finePairTimeFieldValue e v)
      ∂finePairTimeFieldMeasure d lo hi) =
      ∫ T in Icc lo hi, T * Real.exp (-T * euclideanNorm (fun r => u r - v r)) := by
  rw [finePairTimeFieldMeasure_integral d lo hi _
    (finePairTimeFieldValue_weighted_pair_integrable d lo hi u v)]
  simp only [finePairTimeFieldValue, integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
  rw [boundedHyperplaneField_covariance d T (hlo.trans hT.1) u v hu hv]

end

end NearlyMinimax
