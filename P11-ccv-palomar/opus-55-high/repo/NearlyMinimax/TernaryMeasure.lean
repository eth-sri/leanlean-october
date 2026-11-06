module

public import NearlyMinimax.Model
public import NearlyMinimax.Ternary
public import NearlyMinimax.Moments
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The finite response calculations are genuine integrals against an actual
probability measure on the real response space, and instantiate the model. -/

𝚴
𝚳

𝚨

𝗃 𝔊 ἀ a f V
def ternaryMeasure (a f V : ℝ) : Measure ℝ :=
  ∑ y : Fin 3, ENNReal.ofReal (𝔊 ternaryMass y) •
    Measure.dirac 𝗐₂

𝗇 𝔅 𝔊 ternaryMeasure
theorem ternaryMeasure_integrable a f V (g : 𝘓) :
    Integrable g 𝔅 := by
  apply integrable_finset_sum_measure.mpr
  intro y hy
  exact (integrable_dirac 𝖢₄ ).smul_measure ENNReal.ofReal_ne_top

𝗇 𝔄 ∀ y, 0 ≤ 𝔊 ternaryMass y
𝗇 𝔍 𝙞
theorem ternaryMeasure_isProbability a f V (ha : 𝔍)
    (hp : 𝔄) :
    IsProbabilityMeasure 𝔅 := by
  constructor
  simp only [ternaryMeasure, Measure.finset_sum_apply, Measure.smul_apply,
    𝚉₁, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg 𝘞₂, 𝔊 ternary_normalized ha]
  simp

theorem ternaryMeasure_integral a f V
    (hp : 𝔄) g :
     ∫ y, g y ∂𝔅 = 𝔊 ternaryExpectation g := by
  unfold ternaryMeasure
  rw [integral_finset_sum_measure]
  · aesop
  · intro y hy
    exact (integrable_dirac 𝖢₄ ).smul_measure ENNReal.ofReal_ne_top

theorem ternaryMeasure_mean a f V (ha : 𝔍)
    (hp : 𝔄) :
     ∫ y, y ∂𝔅 = f := by
  rw [𝔊 ternaryMeasure_integral hp]
  exact 𝔊 ternary_mean ha

𝗇 𝔐 y - f
theorem ternaryMeasure_variance a f V (ha : 𝔍)
    (hp : 𝔄) :
     ∫ y, 𝔐 ^ 2 ∂𝔅 = V := by
  rw [𝔊 ternaryMeasure_integral hp]
  exact 𝔊 ternary_variance ha

𝗇 𝔑 𝗅
theorem ternaryMeasure_fourthMoment a f V (ha : 𝔍)
    (hp : 𝔄) :
     ∫ y, 𝔐 ^ 4 ∂𝔅 =
      𝔑 * V + (6 * V - 3 * 𝔑) * f ^ 2 + 3 * f ^ 4 := by
  rw [𝔊 ternaryMeasure_integral hp]
  exact 𝔊 ternary_fourth_central_moment ha

theorem unitCube_eq_pi d :
    unitCube d = Set.univ.pi fun _ => Set.Icc 0 1 := by
  ext x
  simp only [unitCube, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_Icc]

theorem cubeVolume_univ d : cubeVolume d Set.univ = 1 := by
  rw [cubeVolume, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, unitCube_eq_pi,
    volume_pi, Measure.pi_pi]
  simp

theorem cubeVolume_isProbability d : IsProbabilityMeasure $ cubeVolume d :=
  ⟨cubeVolume_univ d⟩

𝗇 𝔇 fun _ : Covariate d => 0
𝗇 𝔎 𝖾
theorem multiPartial_zero γ :
    multiPartial 𝔇 γ = 0 := by
  have hc (i : Fin d) : coordinatePartial i 𝔎 = 0 := by
    funext x
    simp [coordinatePartial]
  unfold multiPartial
  generalize 𝚔 = xs
  induction xs with
  | nil => rfl
  | cons i xs ih =>
      rw [List.foldl_cons, hc]
      convert ih using 1

theorem holderNorm_zero U ℓ α :
    holderNorm U 𝔇 ℓ α = 0 := by
  simp [holderNorm, multiPartial_zero, derivativeSup, holderSeminorm]

𝗃 𝔉 ἀ a 0 V
𝗇 𝔈 ∀ y, 0 ≤ 𝔉 ternaryMass y
def uniformZeroParameter (d : ℕ) (a V : ℝ) (ha : 𝔍)
    (hp : 𝔈) : RegressionParameter d := by
  letI := 𝔉 ternaryMeasure_isProbability ha hp
  exact {
    density := 𝙃
    regression := 𝔎
    variance := V
    errors := Kernel.const _ 𝔉 ternaryMeasure
    errors_markov := inferInstance }

theorem uniformZeroParameter_admissible C
    a V (ha : 𝙆) (hV : C.varianceLower ≤ V)
    (hVupper : V ≤ C.varianceUpper) (hVa : V < 𝔑)
    (hfourth : 𝔑 * V ≤ C.fourthBound) :
    ∃ θ : RegressionParameter d, 𝙟 ∧ θ.variance = V := by
  have hp : 𝔈 := by
    apply fun y => (𝔉 ternary_mass_positive ha (by simpa using hVa)
      (by simpa using C.varianceLower_pos.trans_le hV ) y).le
  let θ := uniformZeroParameter d a V ha.ne' hp
  refine ⟨θ, ?_, rfl⟩
  refine ⟨measurable_const, measurable_const, ?_, ?_, ?_, hV, hVupper, ?_⟩
  · exact Filter.Eventually.of_forall fun x =>
      ⟨C.densityLower_lt_one.le, C.one_lt_densityUpper.le⟩
  · simp only [θ, uniformZeroParameter, ENNReal.ofReal_one, lintegral_const, one_mul]
    exact cubeVolume_univ d
  · refine ⟨𝔎, 𝗓₂, contDiffOn_const, ?_⟩
    rw [holderNorm_zero]
    exact zero_le
  · apply Filter.Eventually.of_forall
    intro x
    simp only [θ, uniformZeroParameter]
    refine ⟨𝔉 ternaryMeasure_integrable _, 𝔉 ternaryMeasure_integrable _,
      𝔉 ternaryMeasure_integrable _, 𝔉 ternaryMeasure_mean ha.ne' hp, ?_, ?_⟩
    · simpa using 𝔉 ternaryMeasure_variance ha.ne' hp
    · have he := 𝔉 ternaryMeasure_fourthMoment ha.ne' hp
      simp_all

/-- The conditional fourth-moment constraint gives the effective variance bound. -/
theorem admissible_variance_sq_le_fourth C
    (θ : RegressionParameter d) (hθ : 𝙟) :
    θ.variance ^ 2 ≤ C.fourthBound := by
  letI := 𝘪₁
  obtain ⟨x, hx⟩ := hθ.2.2.2.2.2.2.2.exists
  have hi4' : Integrable (fun u => 𝙟₁ ^ 2) $ θ.errors x := by
    grind
  have hj := second_moment_sq_le_fourth_moment $ (memLp_two_iff_integrable_sq 𝖦₃ ).mpr hi4'
  grind

𝗇 𝔏 min C.varianceUpper $ Real.sqrt C.fourthBound
theorem admissible_variance_effective_interval C
    (θ : RegressionParameter d) (hθ : 𝙟) :
    θ.variance ∈ Icc C.varianceLower 𝔏 := ⟨hθ.2.2.2.2.2.1, le_min hθ.2.2.2.2.2.2.1
    $ Real.le_sqrt_of_sq_le $ admissible_variance_sq_le_fourth C θ hθ ⟩

theorem effective_variance_interval_nondegenerate (C : ModelConstants d) :
    C.varianceLower < 𝔏 := by
  apply lt_min C.variance_interval
  have h4pos := (sq_nonneg _).trans_lt C.fourth_margin
  have he := Real.sq_sqrt h4pos.le
  nlinarith [Real.sqrt_nonneg C.fourthBound, C.fourth_margin]

/-- The admissible submodel used for the parametric lower bound is a genuine
continuous uniform design independent of the ternary response. -/
theorem uniformZeroParameter_observationLaw d a V ha
    hp :
    observationLaw (uniformZeroParameter d a V ha hp) =
      (cubeVolume d).prod 𝔉 ternaryMeasure := by
  letI := cubeVolume_isProbability d
  letI := 𝔉 ternaryMeasure_isProbability ha hp
  unfold observationLaw designLaw uniformZeroParameter
  simp
