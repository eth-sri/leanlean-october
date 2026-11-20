module

public import NearlyMinimax.Model
public import NearlyMinimax.Ternary
public import NearlyMinimax.Moments

@[expose] public section

/-! The finite response calculations are genuine integrals against an actual
probability measure on the real response space, and instantiate the model. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace NearlyMinimax

/-- A nonnegative observable with finite-valued conditional marks is
integrable as soon as its conditional expectation is integrable. -/
theorem finiteKernel_integrable_integral {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Finite β] [MeasurableSingletonClass β] (μ : Measure α) [SFinite μ]
    (κ : Kernel α β) [IsMarkovKernel κ] {H : α × β → ℝ} {E : α → ℝ}
    (hH : Measurable H) (hn : ∀ z, 0 ≤ H z)
    (hEq : ∀ x, (∫ y, H (x,y) ∂κ x) = E x) (hE : Integrable E μ) :
    Integrable H (μ.compProd κ) ∧ (∫ z, H z ∂μ.compProd κ) = ∫ x, E x ∂μ := by
  have hnorm z : ‖H z‖ = H z := Real.norm_of_nonneg (hn z)
  have hi : Integrable H (μ.compProd κ) := (Measure.integrable_compProd_iff hH.aestronglyMeasurable).2
    ⟨.of_forall fun _ => .of_finite, by simpa only [hnorm, hEq] using hE⟩
  exact ⟨hi, by simp only [Measure.integral_compProd hi, hEq]⟩

section Atoms
variable {I β : Type*} [Fintype I] [MeasurableSpace β]

/-- A finite weighted law, allowing repeated atom locations. -/
def weightedAtomMeasure (w : I → ℝ) (g : I → β) : Measure β :=
  ∑ i, ENNReal.ofReal (w i) • Measure.dirac (g i)

theorem weightedAtomMeasure_probability (w : I → ℝ) (g : I → β)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) :
    IsProbabilityMeasure (weightedAtomMeasure w g) := by
  constructor
  simp [weightedAtomMeasure, Measure.finsetSum_apply, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i), hs]

variable [MeasurableSingletonClass β]

section
variable (w : I → ℝ) (g : I → β)

theorem weightedAtomMeasure_integrable (H : β → ℝ) :
    Integrable H (weightedAtomMeasure w g) :=
  integrable_finsetSum_measure.mpr fun _ _ => (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

theorem weightedAtomMeasure_integral (hw : ∀ i, 0 ≤ w i) (H : β → ℝ) :
    (∫ z, H z ∂weightedAtomMeasure w g) = ∑ i, w i * H (g i) := by
  rw [weightedAtomMeasure, integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul, ENNReal.toReal_ofReal (hw _)]
  · exact fun _ _ => (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

end

end Atoms

section AtomKernel
variable {I α β : Type*} [Fintype I] [MeasurableSpace α] [MeasurableSpace β]
    (w : α → I → ℝ) (g : α → I → β)
    (hw : ∀ i, Measurable fun x => w x i) (hg : ∀ i, Measurable fun x => g x i)

def weightedAtomKernel : Kernel α β where
  toFun x := weightedAtomMeasure (w x) (g x)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [weightedAtomMeasure, Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply' _ hs, smul_eq_mul]
    exact Finset.measurable_sum _ fun i _ =>
      (ENNReal.measurable_ofReal.comp (hw i)).mul (measurable_const.indicator ((hg i) hs))

theorem weightedAtomKernel_markov (hn : ∀ x i, 0 ≤ w x i) (hs : ∀ x, ∑ i, w x i = 1) :
    IsMarkovKernel (weightedAtomKernel w g hw hg) :=
  ⟨fun x => weightedAtomMeasure_probability _ _ (hn x) (hs x)⟩

end AtomKernel

def ternaryMeasure (a f V : ℝ) : Measure ℝ :=
  weightedAtomMeasure (ternaryMass a f V) (ternaryValue a)

section
variable (a f V : ℝ)

theorem ternaryMeasure_integrable (g : ℝ → ℝ) :
    Integrable g (ternaryMeasure a f V) := weightedAtomMeasure_integrable _ _ _

theorem ternaryMeasure_isProbability (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a f V y) :
    IsProbabilityMeasure (ternaryMeasure a f V) :=
  weightedAtomMeasure_probability _ _ hp (ternary_normalized a f V)

theorem ternaryMeasure_integral
    (hp : ∀ y, 0 ≤ ternaryMass a f V y) (g : ℝ → ℝ) :
    (∫ y, g y ∂ternaryMeasure a f V) = ternaryExpectation a f V g :=
  weightedAtomMeasure_integral _ _ hp g

section
variable (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a f V y)
include ha hp

theorem ternaryMeasure_mean :
    (∫ y, y ∂ternaryMeasure a f V) = f := by
  rw [ternaryMeasure_integral a f V hp]
  exact ternary_mean a f V ha

theorem ternaryMeasure_variance :
    (∫ y, (y - f) ^ 2 ∂ternaryMeasure a f V) = V := by
  rw [ternaryMeasure_integral a f V hp]
  exact ternary_variance a f V ha

theorem ternaryMeasure_fourthMoment :
    (∫ y, (y - f) ^ 4 ∂ternaryMeasure a f V) =
      a ^ 2 * V + (6 * V - 3 * a ^ 2) * f ^ 2 + 3 * f ^ 4 := by
  rw [ternaryMeasure_integral a f V hp]
  exact ternary_fourth_central_moment a f V ha

end

end

section
variable (d : ℕ)

theorem unitCube_eq_pi :
    unitCube d = Set.univ.pi (fun _ : Fin d => Set.Icc (0 : ℝ) 1) := by
  ext x
  simp only [unitCube, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_Icc]

theorem cubeVolume_univ : cubeVolume d Set.univ = 1 := by
  rw [cubeVolume, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, unitCube_eq_pi,
    volume_pi, Measure.pi_pi]
  simp

theorem cubeVolume_isProbability : IsProbabilityMeasure (cubeVolume d) :=
  ⟨cubeVolume_univ d⟩

end

section
variable {d : ℕ}

theorem multiPartial_zero (γ : Fin d → ℕ) :
    multiPartial (fun _ : Covariate d => (0 : ℝ)) γ = 0 := by
  have hc (i : Fin d) : coordinatePartial i (fun _ : Covariate d => (0 : ℝ)) = 0 := by
    funext x
    simp [coordinatePartial]
  unfold multiPartial
  generalize ((List.finRange d).flatMap (fun i => List.replicate (γ i) i)) = xs
  induction xs with
  | nil => rfl
  | cons i xs ih =>
      rw [List.foldl_cons, hc]
      convert ih using 1

theorem holderNorm_zero (U : Set (Covariate d)) (ℓ : ℕ) (α : ℝ) :
    holderNorm U (fun _ : Covariate d => (0 : ℝ)) ℓ α = 0 := by
  simp [holderNorm, multiPartial_zero, derivativeSup, holderSeminorm]

end

def uniformZeroParameter (d : ℕ) (a V : ℝ) (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a 0 V y) : RegressionParameter d := by
  letI := ternaryMeasure_isProbability a 0 V ha hp
  exact {
    density := fun _ => 1
    regression := fun _ => 0
    variance := V
    errors := Kernel.const _ (ternaryMeasure a 0 V)
    errors_markov := inferInstance }

section
variable {d : ℕ} (C : ModelConstants d)

section
variable (a V : ℝ) (ha : 0 < a) (hV : C.varianceLower ≤ V)
    (hVupper : V ≤ C.varianceUpper)
include ha hV hVupper

theorem uniformZeroParameter_legal
    (hfourth : a ^ 2 * V ≤ C.fourthBound)
    (hp : ∀ y, 0 ≤ ternaryMass a 0 V y) :
    Admissible C (uniformZeroParameter d a V ha.ne' hp) := by
  let θ := uniformZeroParameter d a V ha.ne' hp
  change Admissible C θ
  refine ⟨measurable_const, measurable_const, ?_, ?_, ?_, hV, hVupper, ?_⟩
  · exact Filter.Eventually.of_forall (fun x =>
      ⟨C.densityLower_lt_one.le, C.one_lt_densityUpper.le⟩)
  · simp only [θ, uniformZeroParameter, ENNReal.ofReal_one, lintegral_const, one_mul]
    exact cubeVolume_univ d
  · refine ⟨fun _ => 0, fun _ _ => rfl, contDiffOn_const, ?_⟩
    simp [holderNorm_zero]
  · apply Filter.Eventually.of_forall
    intro x
    simp only [θ, uniformZeroParameter, Kernel.const_apply]
    refine ⟨ternaryMeasure_integrable a 0 V _, ternaryMeasure_integrable a 0 V _,
      ternaryMeasure_integrable a 0 V _, ternaryMeasure_mean a 0 V ha.ne' hp, ?_, ?_⟩
    · simpa using ternaryMeasure_variance a 0 V ha.ne' hp
    · have he := ternaryMeasure_fourthMoment a 0 V ha.ne' hp
      simp_all

theorem uniformZeroParameter_admissible (hVa : V < a ^ 2)
    (hfourth : a ^ 2 * V ≤ C.fourthBound) :
    ∃ θ : RegressionParameter d, Admissible C θ ∧ θ.variance = V := by
  have hVp := C.varianceLower_pos.trans_le hV
  have hp : ∀ y, 0 ≤ ternaryMass a 0 V y := by
    apply fun y => (ternary_mass_positive a 0 V ha (by simp_all)
      (by simp_all) y).le
  exact ⟨_, uniformZeroParameter_legal C a V ha hV hVupper hfourth hp, rfl⟩

end

section
variable (θ : RegressionParameter d) (hθ : Admissible C θ)
include hθ

/-- The conditional fourth-moment constraint gives the effective variance bound. -/
theorem admissible_variance_sq_le_fourth :
    θ.variance ^ 2 ≤ C.fourthBound := by
  letI := designLaw_isProbability C θ hθ
  obtain ⟨x, hx⟩ := hθ.2.2.2.2.2.2.2.exists
  obtain ⟨_, _, hi4, _, hi2, hbound⟩ := hx
  have hi4' : Integrable (fun u : ℝ => (u ^ 2) ^ 2) (θ.errors x) := by
    convert hi4 using 1
    ring
  have hl2 :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr hi4'
  have hj := second_moment_sq_le_fourth_moment hl2
  simpa [hi2] using hj.trans hbound

theorem admissible_variance_effective_interval :
    θ.variance ∈ Icc C.varianceLower (min C.varianceUpper (Real.sqrt C.fourthBound)) := by
  exact ⟨hθ.2.2.2.2.2.1, le_min hθ.2.2.2.2.2.2.1
    (Real.le_sqrt_of_sq_le (admissible_variance_sq_le_fourth C θ hθ))⟩

end

theorem effective_variance_interval_nondegenerate :
    C.varianceLower < min C.varianceUpper (Real.sqrt C.fourthBound) := by
  apply lt_min C.variance_interval
  have h4pos := (sq_nonneg _).trans_lt C.fourth_margin
  have he := Real.sq_sqrt h4pos.le
  nlinarith [Real.sqrt_nonneg C.fourthBound, C.varianceLower_pos, C.fourth_margin]

end

/-- The admissible submodel used for the parametric lower bound is a genuine
continuous uniform design independent of the ternary response. -/
theorem uniformZeroParameter_observationLaw (d : ℕ) (a V : ℝ) (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a 0 V y) :
    observationLaw (uniformZeroParameter d a V ha hp) =
      (cubeVolume d).prod (ternaryMeasure a 0 V) := by
  letI := cubeVolume_isProbability d
  letI := ternaryMeasure_isProbability a 0 V ha hp
  unfold observationLaw designLaw uniformZeroParameter
  simp_all [Measure.compProd_const]

/-- Covariate array and ternary response-index array for the same sample. -/
abbrev TernarySample (d n : ℕ) := (Fin n → Covariate d) × (Fin n → Fin 3)

end NearlyMinimax
