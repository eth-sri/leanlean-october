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

def ternaryMeasure (a f V : ℝ) : Measure ℝ :=
  ∑ y, ENNReal.ofReal (ternaryMass a f V y) •
    Measure.dirac (ternaryValue a y)

theorem ternaryMeasure_integrable (a f V : ℝ) (g : ℝ → ℝ) :
    Integrable g (ternaryMeasure a f V) := by
  apply integrable_finset_sum_measure.mpr
  intro y hy
  exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

section
variable (d : ℕ) {a f V : ℝ} (ha : a ≠ 0) (hp : ∀ y, 0 ≤ ternaryMass a f V y)

include ha hp in
theorem ternaryMeasure_isProbability :
    IsProbabilityMeasure (ternaryMeasure a f V) := by
  constructor
  simp [ternaryMeasure]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => hp y), ternary_normalized f V ha]
  simp

include hp in
theorem ternaryMeasure_integral (g : ℝ → ℝ) :
    (∫ y, g y ∂ternaryMeasure a f V) = ternaryExpectation a f V g := by
  unfold ternaryMeasure
  rw [integral_finset_sum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
      ENNReal.toReal_ofReal (hp _), ternaryExpectation]
  · intro y hy
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

include ha hp in
theorem ternaryMeasure_variance :
    (∫ y, (y - f) ^ 2 ∂ternaryMeasure a f V) = V := by
  rw [ternaryMeasure_integral hp]
  exact ternary_variance a f V ha

include ha hp in
theorem ternaryMeasure_fourthMoment :
    (∫ y, (y - f) ^ 4 ∂ternaryMeasure a f V) =
      a ^ 2 * V + (6 * V - 3 * a ^ 2) * f ^ 2 + 3 * f ^ 4 := by
  rw [ternaryMeasure_integral hp]
  exact ternary_fourth_central_moment a f V ha

theorem unitCube_eq_pi :
    unitCube d = Set.univ.pi (fun _ => Set.Icc 0 1) := by
  grind [unitCube]

theorem cubeVolume_univ : cubeVolume d Set.univ = 1 := by
  rw [cubeVolume, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, unitCube_eq_pi,
    volume_pi, Measure.pi_pi]
  simp

theorem cubeVolume_isProbability : IsProbabilityMeasure (cubeVolume d) :=
  ⟨cubeVolume_univ d⟩

theorem multiPartial_zero {d : ℕ} (γ : Fin d → ℕ) :
    multiPartial (fun _ => 0) γ = 0 := by
  have hc (i : Fin d) : coordinatePartial i (fun _ => 0) = 0 := by
    funext x
    simp [coordinatePartial]
  unfold multiPartial
  generalize ((List.finRange d).flatMap (fun i => List.replicate (γ i) i)) = xs
  induction xs with
  | nil => rfl
  | cons i xs ih =>
      aesop

theorem holderNorm_zero {d : ℕ} (U : Set (Covariate d)) (ℓ : ℕ) (α : ℝ) :
    holderNorm U (fun _ => 0) ℓ α = 0 := by
  simp [holderNorm, multiPartial_zero, derivativeSup, holderSeminorm]

def uniformZeroParameter
    (hp : ∀ y, 0 ≤ ternaryMass a 0 V y) : RegressionParameter d := by
  letI := ternaryMeasure_isProbability ha hp
  exact {
    density := fun _ => 1
    regression := fun _ => 0
    variance := V
    errors := Kernel.const _ (ternaryMeasure a 0 V)
    errors_markov := inferInstance }

end

section
variable {d : ℕ} {C : ModelConstants d} {a V : ℝ} (ha : 0 < a) (hV : C.varianceLower ≤ V)
    (hVupper : V ≤ C.varianceUpper) (hVa : V < a ^ 2) (hfourth : a ^ 2 * V ≤ C.fourthBound)

include hV hVupper hfourth in
theorem ternary_submodel_admissible
    (hp : ∀ y, 0 ≤ ternaryMass a 0 V y) :
    Admissible C (uniformZeroParameter d ha.ne' hp) := by
  let θ := uniformZeroParameter d ha.ne' hp
  refine ⟨measurable_const, measurable_const, ?_, ?_, ?_, hV, hVupper, ?_⟩
  · exact Filter.Eventually.of_forall (fun x =>
      ⟨C.densityLower_lt_one.le, C.one_lt_densityUpper.le⟩)
  · simp [uniformZeroParameter]
    exact cubeVolume_univ d
  · refine ⟨fun _ => 0, fun _ _ => rfl, contDiffOn_const, ?_⟩
    rw [holderNorm_zero]
    exact zero_le
  · apply Filter.Eventually.of_forall
    intro x
    simp [uniformZeroParameter]
    refine ⟨ternaryMeasure_integrable a 0 V _, ternaryMeasure_integrable a 0 V _,
      ternaryMeasure_integrable a 0 V _, (by rw [ternaryMeasure_integral hp]; exact ternary_mean _ _ _ ha.ne'), ?_, ?_⟩
    · simpa using ternaryMeasure_variance ha.ne' hp
    · have he := ternaryMeasure_fourthMoment ha.ne' hp
      grind

include ha hV hVupper hVa hfourth in
theorem uniformZeroParameter_admissible :
    ∃ θ : RegressionParameter d, Admissible C θ ∧ θ.variance = V := by
  have hp : ∀ y, 0 ≤ ternaryMass a 0 V y := by
    apply fun y => (ternary_mass_positive a 0 V ha (by simpa using hVa)
      (by simpa using (C.varianceLower_pos.trans_le hV)) y).le
  exact ⟨_, ternary_submodel_admissible ha hV hVupper hfourth hp, rfl⟩

/-- The conditional fourth-moment constraint gives the effective variance bound. -/
theorem admissible_variance_sq_le_fourth
    {θ : RegressionParameter d} (hθ : Admissible C θ) :
    θ.variance ^ 2 ≤ C.fourthBound := by
  letI := designLaw_isProbability C θ hθ
  obtain ⟨x, hx⟩ := hθ.2.2.2.2.2.2.2.exists
  obtain ⟨_, _, hi4, _, hi2, hbound⟩ := hx
  have hi4' : Integrable (fun u => (u ^ 2) ^ 2) (θ.errors x) := by
    convert hi4 using 1
    ring
  grind [second_moment_sq_le_fourth_moment ((memLp_two_iff_integrable_sq (by fun_prop)).mpr hi4')]

theorem admissible_variance_effective_interval
    {θ : RegressionParameter d} (hθ : Admissible C θ) :
    θ.variance ∈ Icc C.varianceLower (min C.varianceUpper (Real.sqrt C.fourthBound)) := ⟨hθ.2.2.2.2.2.1, le_min hθ.2.2.2.2.2.2.1
    (Real.le_sqrt_of_sq_le (admissible_variance_sq_le_fourth hθ))⟩

theorem effective_variance_interval_nondegenerate (C : ModelConstants d) :
    C.varianceLower < min C.varianceUpper (Real.sqrt C.fourthBound) := by
  apply lt_min C.variance_interval
  have he := Real.sq_sqrt ((sq_nonneg _).trans_lt C.fourth_margin).le
  nlinarith [Real.sqrt_nonneg C.fourthBound, C.varianceLower_pos, C.fourth_margin]

end

/-- The admissible submodel used for the parametric lower bound is a genuine
continuous uniform design independent of the ternary response. -/
theorem uniformZeroParameter_observationLaw (d : ℕ) (a V : ℝ) (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a 0 V y) :
    observationLaw (uniformZeroParameter d ha hp) =
      (cubeVolume d).prod (ternaryMeasure a 0 V) := by
  letI := cubeVolume_isProbability d
  letI := ternaryMeasure_isProbability ha hp
  unfold observationLaw designLaw uniformZeroParameter
  simp

end NearlyMinimax
