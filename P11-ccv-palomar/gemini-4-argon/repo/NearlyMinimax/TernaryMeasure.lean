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
  ∑ y : Fin 3, ENNReal.ofReal (ternaryMass a f V y) •
    Measure.dirac (ternaryValue a y)

theorem ternaryMeasure_integrable (a f V : ℝ) (g : ℝ → ℝ) :
    Integrable g (ternaryMeasure a f V) := by
  apply integrable_finset_sum_measure.mpr
  intro y hy
  exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

theorem ternaryMeasure_isProbability (a f V ) (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a f V y) :
    IsProbabilityMeasure (ternaryMeasure a f V) := by
  constructor
  simp only [ternaryMeasure, Measure.finset_sum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => hp y), ternary_normalized a f V ha]
  simp

theorem ternaryMeasure_integral (a f V )
    (hp : ∀ y, 0 ≤ ternaryMass a f V y) (g ) :
    (∫ y, g y ∂ternaryMeasure a f V) = ternaryExpectation a f V g := by
  unfold ternaryMeasure
  rw [integral_finset_sum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
      ENNReal.toReal_ofReal (hp _), ternaryExpectation]
  · intro y hy
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

theorem ternaryMeasure_mean (a f V ) (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a f V y) :
    (∫ y, y ∂ternaryMeasure a f V) = f := by
  rw [ternaryMeasure_integral a f V hp]
  exact ternary_mean a f V ha

theorem ternaryMeasure_variance (a f V ) (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a f V y) :
    (∫ y, (y - f) ^ 2 ∂ternaryMeasure a f V) = V := by
  rw [ternaryMeasure_integral a f V hp]
  exact ternary_variance a f V ha

theorem ternaryMeasure_fourthMoment (a f V ) (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a f V y) :
    (∫ y, (y - f) ^ 4 ∂ternaryMeasure a f V) =
      a ^ 2 * V + (6 * V - 3 * a ^ 2) * f ^ 2 + 3 * f ^ 4 := by
  rw [ternaryMeasure_integral a f V hp]
  exact ternary_fourth_central_moment a f V ha

theorem unitCube_eq_pi (d ) :
    unitCube d = Set.univ.pi (fun _ => Set.Icc 0 1) := by
  ext x
  simp only [unitCube, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_Icc]

theorem cubeVolume_univ (d ) : cubeVolume d Set.univ = 1 := by
  rw [cubeVolume, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, unitCube_eq_pi,
    volume_pi, Measure.pi_pi]
  simp

theorem cubeVolume_isProbability (d ) : IsProbabilityMeasure (cubeVolume d) :=
  ⟨cubeVolume_univ d⟩

theorem holderNorm_zero {d : ℕ} (U : Set (Covariate d)) (ℓ : ℕ) (α : ℝ) :
    holderNorm U (fun _ : Covariate d => ↑0) ℓ α = 0 := by
  have h_multiPartial_zero (γ : Fin d → ℕ) : multiPartial (fun _ : Covariate d => ↑0) γ = 0 := by
    have hc (i : Fin d) : coordinatePartial i (fun _ : Covariate d => ↑0) = 0 := by
      funext x
      simp [coordinatePartial]
    unfold multiPartial
    generalize ((List.finRange d).flatMap (fun i => List.replicate (γ i) i)) = xs
    induction xs with
    | nil => rfl
    | cons i xs ih =>
        rw [List.foldl_cons, hc]
        convert ih using 1
  simp [holderNorm, h_multiPartial_zero, derivativeSup, holderSeminorm]

def uniformZeroParameter (d a V) (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a 0 V y) : RegressionParameter d := by
  letI := ternaryMeasure_isProbability a 0 V ha hp
  exact {
    density := fun _ => 1
    regression := fun _ => 0
    variance := V
    errors := Kernel.const _ (ternaryMeasure a 0 V)
    errors_markov := inferInstance }

theorem admissible_variance_effective_interval  (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    θ.variance ∈ Icc C.varianceLower (min C.varianceUpper (Real.sqrt C.fourthBound)) := by
  letI := designLaw_isProbability C θ hθ
  obtain ⟨x, hx⟩ := hθ.2.2.2.2.2.2.2.exists
  obtain ⟨_, _, hi4, _, hi2, hbound⟩ := hx
  have hi4' : Integrable (fun u => (u ^ 2) ^ 2) (θ.errors x) := by
    convert hi4 using 1
    funext u
    ring
  have hl2  :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr hi4'
  have hj := second_moment_sq_le_fourth_moment hl2
  exact ⟨hθ.2.2.2.2.2.1, le_min hθ.2.2.2.2.2.2.1
    (Real.le_sqrt_of_sq_le (by rw [hi2] at hj; exact hj.trans hbound))⟩

theorem effective_variance_interval_nondegenerate  (C : ModelConstants d) :
    C.varianceLower < min C.varianceUpper (Real.sqrt C.fourthBound) := by
  apply lt_min C.variance_interval
  have := Real.sq_sqrt ((sq_nonneg _).trans_lt C.fourth_margin).le
  nlinarith [Real.sqrt_nonneg C.fourthBound, C.varianceLower_pos, C.fourth_margin]

/-- The admissible submodel used for the parametric lower bound is a genuine
continuous uniform design independent of the ternary response. -/
theorem uniformZeroParameter_observationLaw (d a V ha hp) :
    observationLaw (uniformZeroParameter d a V ha hp) =
      (cubeVolume d).prod (ternaryMeasure a 0 V) := by
  letI := cubeVolume_isProbability d
  letI := ternaryMeasure_isProbability a 0 V ha hp
  unfold observationLaw designLaw uniformZeroParameter
  simp only [ENNReal.ofReal_one, withDensity_const, one_smul, zero_add]
  change ((cubeVolume d).compProd (Kernel.const _ (ternaryMeasure a 0 V))).map id = _
  rw [Measure.map_id, Measure.compProd_const]

end NearlyMinimax
