module

public import NearlyMinimax.FinePairReference
public import NearlyMinimax.BoundedHyperplaneField
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The fine density packet with the actual bounded hyperplane field,
and the genuine Lebesgue-time/field carrier of the coarse and fine rows. -/
open Set MeasureTheory ProbabilityTheory
𝚳
𝚨
𝚩
𝚰

abbrev FinePairFieldMark (d : ℕ) := partitionFieldMark 𝚛

theorem boundedHyperplaneFieldValue_section_measurable d u :
    Measurable fun z : FinePairFieldMark d => boundedHyperplaneFieldValue z u :=
  (boundedHyperplaneFieldValue_measurable d).comp $ measurable_id.prodMk measurable_const

def finePairFieldKernel (d : ℕ) : Kernel ℝ $ FinePairFieldMark d where
  toFun := boundedHyperplaneFieldLaw d
  measurable' := boundedHyperplaneFieldLaw_measurable d

instance finePairFieldKernel_markov (d : ℕ) [NeZero d] : IsMarkovKernel $ finePairFieldKernel d :=
  ⟨ boundedHyperplaneFieldLaw_probability d ⟩

𝗇 𝔅 𝙺₂
𝗇 𝔉 Icc lo hi
def finePairTimeFieldMeasure (d : ℕ) (lo hi : ℝ) : Measure 𝔅 :=
  (volume.restrict 𝔉).compProd $ finePairFieldKernel d

𝗃 𝔎 ἀ d lo hi
𝗇 𝔄 𝔎 finePairTimeFieldMeasure
instance finePairTimeFieldMeasure_finite (d : ℕ) [NeZero d] (lo hi : ℝ) :
    IsFiniteMeasure 𝔄 := by
  unfold finePairTimeFieldMeasure
  infer_instance

theorem finePairTimeFieldMeasure_integral (d : ℕ) [NeZero d] lo hi
    (f : 𝔅 → ℝ) (hf : Integrable f 𝔄) :
     ∫ e, f e ∂𝔄 =
      ∫ T in 𝔉, ∫ z, f (T,z) ∂boundedHyperplaneFieldLaw d T :=
  Measure.integral_compProd hf

def finePairTimeFieldValue (e : 𝔅) (u : Covariate d) : ℝ :=
  boundedHyperplaneFieldValue e.2 u

theorem finePairTimeFieldValue_measurable d :
    Measurable fun ex : 𝔅 × Covariate d =>
      finePairTimeFieldValue ex.1 ex.2 :=
  (boundedHyperplaneFieldValue_measurable d).comp
    $ (measurable_snd.comp measurable_fst).prodMk measurable_snd

theorem finePairTimeFieldValue_abs e (u : Covariate d) :
    |finePairTimeFieldValue e u| = 1 := boundedHyperplaneFieldValue_abs ..

𝗇 𝔍 𝔎 finePairTimeFieldMeasure_fst_integrable
section

variable (d : ℕ)
    [NeZero d]
    (lo)
    (hi)

include d lo hi

theorem finePairTimeFieldMeasure_ae_time :
    ∀ᵐ e ∂𝔄, e.1 ∈ 𝔉 :=
  Measure.ae_compProd_of_ae_fst (finePairFieldKernel d) measurableSet_Icc
    $ ae_restrict_mem measurableSet_Icc

theorem finePairTimeFieldMeasure_fst_integrable :
    Integrable (fun e => e.1) 𝔄 := by
  apply (integrable_const $ max |lo| |hi| ).mono' measurable_fst.aestronglyMeasurable
  filter_upwards [𝔎 finePairTimeFieldMeasure_ae_time] with e he
  rw [Real.norm_eq_abs]
  grind

theorem finePairTimeFieldMeasure_fst_integral :
     ∫ e : 𝔅, e.1 ∂𝔄 =
      ∫ T in 𝔉, T := by
  rw [𝔎 finePairTimeFieldMeasure_integral _ 𝔍]
  simp

end

section Matrix
variable {ι : Type*} [Fintype ι]

𝗇 𝔇 ι → 𝙛
def finePairTimeMatrix (d : ℕ) (A : 𝔇) (e : 𝔅) : 𝔇 :=
  fun i j => e.1 * 𝘩

𝗇 𝔈 finePairTimeMatrix d A
theorem finePairTimeMatrix_measurable d A (i j : ι) :
    Measurable fun e => 𝔈 e i j := measurable_fst.mul_const _

theorem finePairTimeMatrix_cost d (A : 𝔇) e :
    separatedMatrixCost 𝔈 e =
      |e.1| * ∑ i, ∑ j, |𝘩| := by
  simp only [separatedMatrixCost, finePairTimeMatrix, abs_mul, Finset.mul_sum]

theorem finePairTimeMatrix_cost_integrable (d : ℕ) [NeZero d] lo hi (A : 𝔇) :
    Integrable (separatedMatrixCost 𝔈) 𝔄 := by
  change Integrable (fun e => separatedMatrixCost 𝔈 e) _
  simp only [finePairTimeMatrix_cost]
  exact (𝔍).abs.mul_const _

end Matrix

𝗇 𝔊 e.1 * (finePairTimeFieldValue e u * finePairTimeFieldValue e v)
theorem finePairTimeFieldValue_weighted_pair_integrable (d : ℕ) [NeZero d] lo hi
    u v :
    Integrable (fun e => 𝔊)
      𝔄 := by
  have hm u : Measurable fun e =>
      finePairTimeFieldValue e u :=
    (boundedHyperplaneFieldValue_section_measurable d u).comp measurable_snd
  exact (𝔍).mul_bdd (c := 1)
    ((hm u).mul $ hm v ).aestronglyMeasurable
    $ Filter.Eventually.of_forall fun e => by
      simp only [Real.norm_eq_abs, abs_mul, finePairTimeFieldValue_abs, one_mul, le_refl]

theorem finePairTimeFieldValue_weighted_covariance (d : ℕ) [NeZero d] lo hi
    (hlo : 0 ≤ lo) u v (hu : u ∈ hyperplaneCube d) (hv : v ∈ hyperplaneCube d) :
     ∫ e, 𝔊
      ∂𝔄 =
      ∫ T in 𝔉, T * Real.exp (-T * euclideanNorm 𝖤₂) := by
  rw [𝔎 finePairTimeFieldMeasure_integral _
    $ 𝔎 finePairTimeFieldValue_weighted_pair_integrable u v ]
  simp only [finePairTimeFieldValue, integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
  rw [boundedHyperplaneField_covariance d T (hlo.trans hT.1) u v hu hv]
