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

section
variable (d : ℕ)

abbrev FinePairFieldMark := partitionFieldMark (Covariate d × ℝ)

theorem boundedHyperplaneFieldValue_section_measurable {d : ℕ} (u : Covariate d) :
    Measurable (fun z => boundedHyperplaneFieldValue z u) :=
  (boundedHyperplaneFieldValue_measurable d).comp (measurable_id.prodMk measurable_const)

def finePairFieldKernel : Kernel ℝ (FinePairFieldMark d) where
  toFun := boundedHyperplaneFieldLaw d
  measurable' := boundedHyperplaneFieldLaw_measurable d

instance finePairFieldKernel_markov [NeZero d] : IsMarkovKernel (finePairFieldKernel d) :=
  ⟨fun T => boundedHyperplaneFieldLaw_probability d T⟩

def finePairTimeFieldMeasure (lo hi : ℝ) : Measure (ℝ × FinePairFieldMark d) :=
  (volume.restrict (Icc lo hi)).compProd (finePairFieldKernel d)

instance finePairTimeFieldMeasure_finite [NeZero d] (lo hi : ℝ) :
    IsFiniteMeasure (finePairTimeFieldMeasure d lo hi) := by
  unfold finePairTimeFieldMeasure
  infer_instance

end

theorem finePairTimeFieldMeasure_integral {d : ℕ} [NeZero d] {lo hi : ℝ}
    {f : ℝ × FinePairFieldMark d → ℝ} (hf : Integrable f (finePairTimeFieldMeasure d lo hi)) :
    (∫ e, f e ∂finePairTimeFieldMeasure d lo hi) =
      ∫ T in Icc lo hi, ∫ z, f (T,z) ∂boundedHyperplaneFieldLaw d T :=
  Measure.integral_compProd hf

section
variable {d : ℕ} (e : ℝ × FinePairFieldMark d) (u : Covariate d)

def finePairTimeFieldValue : ℝ :=
  boundedHyperplaneFieldValue e.2 u

theorem finePairTimeFieldValue_abs :
    |finePairTimeFieldValue e u| = 1 := boundedHyperplaneFieldValue_abs _ _

end

section
variable (d : ℕ) [NeZero d] (lo hi : ℝ)

theorem finePairTimeFieldMeasure_fst_integrable :
    Integrable (fun e => e.1) (finePairTimeFieldMeasure d lo hi) := by
  apply (integrable_const (max |lo| |hi|)).mono' measurable_fst.aestronglyMeasurable
  filter_upwards [(Measure.ae_compProd_of_ae_fst (finePairFieldKernel d) measurableSet_Icc
      (ae_restrict_mem measurableSet_Icc))] with e he
  exact abs_le.mpr ⟨by linarith [neg_abs_le lo, le_max_left |lo| |hi|, he.1],
    by linarith [le_abs_self hi, le_max_right |lo| |hi|, he.2]⟩

theorem finePairTimeFieldMeasure_fst_integral :
    (∫ e, e.1 ∂finePairTimeFieldMeasure d lo hi) =
      ∫ T in Icc lo hi, T := by
  rw [finePairTimeFieldMeasure_integral (finePairTimeFieldMeasure_fst_integrable d lo hi)]
  simp

end

section Matrix
variable {ι : Type*} [Fintype ι]

variable (d : ℕ) (A : ι → ι → ℝ)

def finePairTimeMatrix (e : ℝ × FinePairFieldMark d) : ι → ι → ℝ :=
  fun i j => e.1 * A i j

theorem finePairTimeMatrix_measurable (i j : ι) :
    Measurable (fun e => finePairTimeMatrix d A e i j) := measurable_fst.mul_const _

theorem finePairTimeMatrix_cost (e : ℝ × FinePairFieldMark d) :
    separatedMatrixCost (finePairTimeMatrix d A) e =
      |e.1| * (∑ i, ∑ j, |A i j|) := by
  simp only [separatedMatrixCost, finePairTimeMatrix, abs_mul, Finset.mul_sum]

theorem finePairTimeMatrix_cost_integrable [NeZero d] (lo hi : ℝ) (A : ι → ι → ℝ) :
    Integrable (separatedMatrixCost (finePairTimeMatrix d A)) (finePairTimeFieldMeasure d lo hi) := by
  change Integrable (fun e => separatedMatrixCost (finePairTimeMatrix d A) e) _
  simp [finePairTimeMatrix_cost]
  exact (finePairTimeFieldMeasure_fst_integrable d lo hi).abs.mul_const _

end Matrix

variable {d : ℕ} [NeZero d] (lo hi : ℝ)

theorem finePairTimeFieldValue_weighted_pair_integrable
    (u v : Covariate d) :
    Integrable (fun e => e.1 * (finePairTimeFieldValue e u * finePairTimeFieldValue e v))
      (finePairTimeFieldMeasure d lo hi) := by
  have hm (u : Covariate d) : Measurable (fun e =>
      finePairTimeFieldValue e u) :=
    (boundedHyperplaneFieldValue_section_measurable u).comp measurable_snd
  exact (finePairTimeFieldMeasure_fst_integrable d lo hi).mul_bdd (c := 1)
    ((hm u).mul (hm v)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e => by
      simp [Real.norm_eq_abs, abs_mul, finePairTimeFieldValue_abs, one_mul, le_refl]))

theorem finePairTimeFieldValue_weighted_covariance
    (hlo : 0 ≤ lo) {u v : Covariate d} (hu : u ∈ hyperplaneCube d) (hv : v ∈ hyperplaneCube d) :
    (∫ e, e.1 * (finePairTimeFieldValue e u * finePairTimeFieldValue e v)
      ∂finePairTimeFieldMeasure d lo hi) =
      ∫ T in Icc lo hi, T * Real.exp (-T * euclideanNorm (fun r => u r - v r)) := by
  rw [finePairTimeFieldMeasure_integral
    (finePairTimeFieldValue_weighted_pair_integrable lo hi u v)]
  simp only [finePairTimeFieldValue, integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
  rw [boundedHyperplaneField_covariance (hlo.trans hT.1) hu hv]

end NearlyMinimax
