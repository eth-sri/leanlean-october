module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsKernel
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelTheorem
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomyPhysicalSemigroup
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsActual

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic SectionTwo Set MeasureTheory Filter
open scoped ENNReal

/-- Regularized absolute value with squared regularization parameter. -/
def velocityConvexProfile (R v : ℝ) : ℝ := Real.sqrt (R + v ^ 2)

/-- First derivative of the convex profile. -/
theorem velocityConvexProfile_hasDerivAt {R : ℝ} (hR : 0 < R) (v : ℝ) :
    HasDerivAt (velocityConvexProfile R) (v / Real.sqrt (R + v ^ 2)) v := by
  have hd : HasDerivAt (fun w => R + w ^ 2) (2 * v) v := by
    have hpow : HasDerivAt (fun w => w ^ 2) (2 * v) v := by
      simpa using hasDerivAt_pow 2 v
    exact hpow.const_add R
  convert (hd.sqrt (ne_of_gt (add_pos_of_pos_of_nonneg hR (sq_nonneg v)))) using 1
  · rfl
  · field_simp


/-- Second derivative of the convex profile. -/
theorem velocityConvexProfile_second_deriv {R : ℝ} (hR : 0 < R) (v : ℝ) :
    deriv (deriv (velocityConvexProfile R)) v =
      R / Real.sqrt (R + v ^ 2) ^ 3  := by
  have velocityConvexProfile_deriv :
      deriv (velocityConvexProfile R) = fun v => v / Real.sqrt (R + v ^ 2) := by
    funext v
    exact (velocityConvexProfile_hasDerivAt hR v).deriv
  rw [velocityConvexProfile_deriv]
  have hp := add_pos_of_pos_of_nonneg hR (sq_nonneg v)
  have hd := (hasDerivAt_id v).div (velocityConvexProfile_hasDerivAt hR v) (ne_of_gt (Real.sqrt_pos.2 hp))
  change deriv (id / velocityConvexProfile R) v = _
  rw [hd.deriv]
  dsimp only [velocityConvexProfile, id_eq]
  have hsq := Real.sq_sqrt hp.le
  field_simp
  nlinarith

/-- The second derivative controls the entire velocity band with a uniform constant. -/
theorem velocityConvexProfile_band_lower {r v : ℝ} (hr : 0 < r)
    (hv : |v| ≤ 3 * r) :
    1 / (64 * r) ≤ r ^ 2 / Real.sqrt (r ^ 2 + v ^ 2) ^ 3 := by
  have hp := add_pos_of_pos_of_nonneg (sq_pos_of_pos hr)
    (sq_nonneg v)
  have hsq := Real.sq_sqrt hp.le
  have hv2 : v ^ 2 ≤ 9 * r ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg v) hv 2
    rw [sq_abs] at h
    nlinarith only [h]
  have hb : Real.sqrt (r ^ 2 + v ^ 2) ≤ 4 * r := by
    nlinarith
  have hc : Real.sqrt (r ^ 2 + v ^ 2) ^ 3 ≤ 64 * r ^ 3 := by
    have := pow_le_pow_left₀ (Real.sqrt_pos.2 hp).le hb 3
    nlinarith
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

/-- Increasing the squared regularization by `h` changes the profile by at most `sqrt h`.
This bound is independent of the velocity. -/
theorem velocityConvexProfile_increment {R h : ℝ} (hR : 0 ≤ R) (hh : 0 ≤ h)
    (v : ℝ) :
    0 ≤ velocityConvexProfile (R + h) v - velocityConvexProfile R v ∧
      velocityConvexProfile (R + h) v - velocityConvexProfile R v ≤ Real.sqrt h := by
  have ha := add_nonneg hR (sq_nonneg v)
  have hb : 0 ≤ R + h + v ^ 2 := by linarith
  have hs := Real.sqrt_nonneg (R + v ^ 2)
  have hu := Real.sqrt_nonneg h
  have hx := Real.sq_sqrt ha
  have hy := Real.sq_sqrt hb
  have hz := Real.sq_sqrt hh
  have hm : Real.sqrt (R + v ^ 2) ≤ Real.sqrt (R + h + v ^ 2) :=
    Real.sqrt_le_sqrt (by linarith)
  unfold velocityConvexProfile
  constructor
  · linarith
  · nlinarith [mul_nonneg hs hu]


/-- Time-dependent regularized absolute value in physical coordinates. -/
def velocityHeatProfile (R Lam T : ℝ) (p : Point) : ℝ :=
  velocityConvexProfile (R + 2 * Lam * (T - p.time)) (p.velocity 0)

/-- Bounded cancellation of two convex profiles, in evolution coordinates. -/
def velocityOccupationBarrier (r Lam T : ℝ) (p : Point) : ℝ :=
  velocityHeatProfile (r ^ 2) Lam T (terminalPhysicalPoint p) -
    velocityHeatProfile (r ^ 2) 0 T (terminalPhysicalPoint p)




/-- Exact operator of the expanding regularized absolute value. -/
theorem velocityHeatProfile_operator {R Lam T : ℝ} (p : Point)
    (hR : 0 < R + 2 * Lam * (T - p.time)) (a : ℝ → ℝ → ℝ) :
    forwardScalarOperator a (velocityHeatProfile R Lam T) p =
      -Lam / Real.sqrt (R + 2 * Lam * (T - p.time) + (p.velocity 0) ^ 2) +
        a (p.position 0) (p.velocity 0) *
          (R + 2 * Lam * (T - p.time)) /
            Real.sqrt (R + 2 * Lam * (T - p.time) + (p.velocity 0) ^ 2) ^ 3 := by
  have hp : 0 < R + 2 * Lam * (T - p.time) + (p.velocity 0) ^ 2 :=
    add_pos_of_pos_of_nonneg hR (sq_nonneg _)
  have ht : kineticTimeDerivative (velocityHeatProfile R Lam T) p =
      -Lam / Real.sqrt (R + 2 * Lam * (T - p.time) + (p.velocity 0) ^ 2) := by
    have hd : HasDerivAt (fun t => R + 2 * Lam * (T - t) + (p.velocity 0) ^ 2)
        (-2 * Lam) p.time := by
      convert (((hasDerivAt_const p.time T).sub (hasDerivAt_id p.time)).const_mul
        (2 * Lam) |>.const_add R |>.add_const ((p.velocity 0) ^ 2)) using 1
      · funext t
        rfl
      · ring
    have hh := hd.sqrt (ne_of_gt hp)
    unfold kineticTimeDerivative velocityHeatProfile velocityConvexProfile
    rw [hh.deriv]
    field_simp
  have hx : kineticPositionGradient (velocityHeatProfile R Lam T) p 0 = 0 := by
    rw [kineticPositionGradient_scalar]
    change deriv (fun _ => velocityHeatProfile R Lam T p) (p.position 0) = 0
    exact deriv_const _ _
  have hv : kineticVelocityHessian (velocityHeatProfile R Lam T) p 0 0 =
      (R + 2 * Lam * (T - p.time)) /
        Real.sqrt (R + 2 * Lam * (T - p.time) + (p.velocity 0) ^ 2) ^ 3 := by
    rw [kineticVelocityHessian_scalar]
    exact velocityConvexProfile_second_deriv hR _
  rw [forwardScalarOperator, ht, hx, hv]
  ring

/-- Each expanding profile is slice regular on its positive-parameter region. -/
theorem velocityHeatProfile_native_regular (R Lam T : ℝ) (p : Point)
    (hR : 0 < R + 2 * Lam * (T - p.time)) :
    IsSliceRegularAt (velocityHeatProfile R Lam T ∘ terminalPhysicalPoint) p := by
  apply IsSliceRegularAt.of_contDiffAt
  change ContDiffAt ℝ 2 (fun q : ℝ × (PDE.Vec 1 × PDE.Vec 1) =>
    Real.sqrt (R + 2 * Lam * (T - q.1) + (q.2.1 0) ^ 2)) _
  apply ContDiffAt.sqrt (by fun_prop)
  exact ne_of_gt (add_pos_of_pos_of_nonneg hR (sq_nonneg _))

/-- The expanding convex profile is a supersolution under the coefficient upper bound. -/
theorem velocityHeatProfile_operator_nonpos {R Lam T : ℝ} (p : Point)
    (hR : 0 < R + 2 * Lam * (T - p.time)) (hLam : 0 ≤ Lam)
    (a : ℝ → ℝ → ℝ) (ha : a (p.position 0) (p.velocity 0) ≤ Lam) :
    forwardScalarOperator a (velocityHeatProfile R Lam T) p ≤ 0 := by
  rw [velocityHeatProfile_operator p hR]
  let Q := R + 2 * Lam * (T - p.time)
  have hp : 0 < Q + (p.velocity 0) ^ 2 := add_pos_of_pos_of_nonneg hR (sq_nonneg _)
  have hs := Real.sqrt_pos.2 hp
  have hsq := Real.sq_sqrt hp.le
  have he : -Lam / Real.sqrt (Q + (p.velocity 0) ^ 2) +
      a (p.position 0) (p.velocity 0) * Q /
        Real.sqrt (Q + (p.velocity 0) ^ 2) ^ 3 =
      (a (p.position 0) (p.velocity 0) * Q - Lam * (Q + (p.velocity 0) ^ 2)) /
        Real.sqrt (Q + (p.velocity 0) ^ 2) ^ 3 := by
    field_simp
    nlinarith
  change -Lam / Real.sqrt (Q + (p.velocity 0) ^ 2) +
    a (p.position 0) (p.velocity 0) * Q /
      Real.sqrt (Q + (p.velocity 0) ^ 2) ^ 3 ≤ 0
  rw [he]
  apply div_nonpos_of_nonpos_of_nonneg
  · have hh := mul_le_mul_of_nonneg_right ha hR.le
    nlinarith [mul_nonneg hLam (sq_nonneg (p.velocity 0))]
  · positivity



/-- Inner regularity transfers a uniform bound on smooth compact unit tests to mass. -/
theorem measure_mass_le_of_smooth_unit_tests {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SigmaCompactSpace E]
    (mu : Measure E) [IsFiniteMeasure mu] {U : Set E} (hU : IsOpen U)
    (hs : mu.restrict U = mu) (C : ℝ)
    (h : ∀ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      tsupport f ⊆ U → (∀ x, 0 ≤ f x ∧ f x ≤ 1) → ∫ x, f x ∂mu ≤ C) :
    mu univ ≤ ENNReal.ofReal C := by
  have he : mu univ = mu U := by
    conv_lhs => rw [← hs]
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
  rw [he, hU.measure_eq_iSup_isCompact mu]
  refine iSup_le fun K => iSup_le fun hKU => iSup_le fun hK => ?_
  obtain ⟨f, hfs, hfc, hfU, hf01, hfK⟩ :=
    exists_smooth_bump_of_isCompact_subset_isOpen hK hU hKU
  have hi : Integrable f mu := hfs.continuous.integrable_of_hasCompactSupport hfc
  calc
    mu K = ∫⁻ x, K.indicator 1 x ∂mu := (lintegral_indicator_one hK.measurableSet).symm
    _ ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂mu := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ K
      · simp [indicator_of_mem hx, hfK x hx]
      · simp [indicator_of_notMem hx]
    _ = ENNReal.ofReal (∫ x, f x ∂mu) :=
      (ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall (fun x => (hf01 x).1))).symm
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (h f hfs hfc hfU hf01)


/-- Positive forcing density supplied by the convex velocity profile. -/
def velocityOccupationDensity (r v : ℝ) : ℝ :=
  r ^ 2 / Real.sqrt (r ^ 2 + v ^ 2) ^ 3

/-- The convex forcing density is smooth. -/
theorem velocityOccupationDensity_contDiff {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (velocityOccupationDensity r) := by
  apply contDiff_const.div
    (((contDiff_const.add (contDiff_id.pow 2)).sqrt
      (fun v => ne_of_gt (by nlinarith [sq_pos_of_pos hr, sq_nonneg v]))).pow 3)
  intro v
  exact pow_ne_zero _ (ne_of_gt (Real.sqrt_pos.2
    (by nlinarith [sq_pos_of_pos hr, sq_nonneg v])))

/-- The forcing density is nonnegative everywhere. -/
theorem velocityOccupationDensity_nonneg (r v : ℝ) : 0 ≤ velocityOccupationDensity r v := by
  unfold velocityOccupationDensity
  positivity



/-- Actual native initial state corresponding to a physical point. -/
def velocityInitialState (z : Z) : EvolutionState autonomousWholeDomain (fun _ => 0) 0 :=
  ⟨(wholeQuery 0 z).1.2.2, (wholeQuery 0 z).2.2⟩

/-- Actual finite-horizon occupation measure. -/
def velocityGreen (E : FullSpaceEvolution) (T : ℝ) (hT : 0 < T) (z : Z) :
    Measure (ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState 1) :=
  greenMeasure E.2 0 (ENNReal.ofReal T) (ENNReal.ofReal_pos.mpr hT)
    (Measure.dirac (velocityInitialState z))

/-- Finite-horizon occupation has mass at most the elapsed horizon. -/
theorem velocityGreen_mass_le (E : FullSpaceEvolution) (T : ℝ) (hT : 0 < T) (z : Z) :
    velocityGreen E T hT z univ ≤ ENNReal.ofReal T := by
  have h := greenMeasure_timeMarginal_le E.2 0 (ENNReal.ofReal T)
    (Measure.dirac (velocityInitialState z)) (velocityGreen E T hT z)
    (greenMeasure_spec E.2 0 _ _ _) univ MeasurableSet.univ
  simpa [preimage_univ, Measure.dirac_apply_of_mem (mem_univ _), elapsedVolume_univ T hT] using h

/-- Finite-horizon occupation is a finite measure. -/
instance velocityGreen_isFiniteMeasure (E : FullSpaceEvolution) (T : ℝ)
    (hT : 0 < T) (z : Z) : IsFiniteMeasure (velocityGreen E T hT z) :=
  ⟨(velocityGreen_mass_le E T hT z).trans_lt ENNReal.ofReal_lt_top⟩

/-- Remove only the elapsed-time subtype; spatial coordinates remain native. -/
def velocityElapsedRaw {T : ℝ}
    (q : ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState 1) :
    ℝ × EvolutionAmbientState 1 := (q.1.1, q.2)

/-- The raw elapsed-coordinate map is measurable. -/
theorem velocityElapsedRaw_measurable (T : ℝ) :
    Measurable (velocityElapsedRaw (T := T)) :=
  (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd

/-- Occupation measure on the ambient finite-dimensional raw coordinates. -/
def velocityGreenRaw (E : FullSpaceEvolution) (T : ℝ) (hT : 0 < T) (z : Z) :
    Measure (ℝ × EvolutionAmbientState 1) :=
  (velocityGreen E T hT z).map velocityElapsedRaw

/-- Raw occupation is finite. -/
instance velocityGreenRaw_isFiniteMeasure (E : FullSpaceEvolution) (T : ℝ)
    (hT : 0 < T) (z : Z) : IsFiniteMeasure (velocityGreenRaw E T hT z) := by
  unfold velocityGreenRaw
  infer_instance

/-- Every raw occupation point lies strictly before the terminal time. -/
theorem velocityGreenRaw_restrict_past (E : FullSpaceEvolution) (T : ℝ)
    (hT : 0 < T) (z : Z) :
    (velocityGreenRaw E T hT z).restrict {q | q.1 < T} = velocityGreenRaw E T hT z := by
  apply Measure.restrict_eq_self_of_ae_mem
  change ∀ᵐ q ∂(velocityGreen E T hT z).map velocityElapsedRaw, q.1 < T
  apply (ae_map_iff (velocityElapsedRaw_measurable T).aemeasurable
    (measurableSet_lt measurable_fst measurable_const)).2
  exact Eventually.of_forall fun q => (ENNReal.ofReal_lt_ofReal_iff hT).mp q.1.2.2



/-- Velocity band in raw evolution spacetime coordinates. -/
def velocityRawBand (r : ℝ) : Set (ℝ × EvolutionAmbientState 1) :=
  {q | |q.2.1 0| ≤ 3 * r}

/-- The raw velocity band is measurable. -/
theorem velocityRawBand_measurable (r : ℝ) : MeasurableSet (velocityRawBand r) := by
  apply measurableSet_le
  · exact continuous_abs.measurable.comp ((measurable_pi_apply 0).comp measurable_snd.fst)
  · exact measurable_const

/-- A unit test of restricted band occupation is bounded by its actual convex source. -/
theorem velocityGreenRaw_band_test_le (hH : HormanderHypoellipticityStatement)
    {lam Lam r T : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (hr : 0 < r) (hT : 0 < T) (z : Z)
    (f : ℝ × EvolutionAmbientState 1 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ {q | q.1 < T})
    (hf01 : ∀ q, 0 ≤ f q ∧ f q ≤ 1) :
    (∫ q in velocityRawBand r, f q ∂velocityGreenRaw E T hT z) ≤
      (64 * r / lam) * Real.sqrt (2 * Lam * T)  := by
  have velocityGreenRaw_source_integral_le :
      (∫ q, f q * (lam * velocityOccupationDensity r (q.2.1 0))
      ∂velocityGreenRaw E T hT z) ≤ Real.sqrt (2 * Lam * T) := by
    have velocity_profile_source_bound (p : Point) (hp : p.time < T) :
        duhamelPotential E.2 T
        (fun q => f (q.time, q.position, q.velocity) *
          (lam * velocityOccupationDensity r (q.position 0))) p ≤
        Real.sqrt (2 * Lam * (T - p.time)) := by
      have velocity_duhamel_le_barrier (g : Point → ℝ) (q : Point → ℝ) (hgn : ∀ p, 0 ≤ g p) (hgs : ContDiff ℝ (⊤ : ℕ∞) (rawLift g)) (hgc : HasCompactSupport g) (hgU : tsupport g ⊆ evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T) (hqc : Continuous q) (hqr : ∀ p, p.time ≤ T → IsSliceRegularAt q p) (hqn : ∀ p ∈ evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) T, 0 ≤ q p) (hqo : ∀ p ∈ evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T,
          transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) q p ≤ -g p) (p₀ : Point) (hp₀ : p₀ ∈ evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T) :
          duhamelPotential E.2 T g p₀ ≤ q p₀ := open Parabolic Evolution Occupation in by
        have source_slice_regular {u : Point → ℝ} {D : Set Point} (hD : IsOpen D) (hu : ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ evolutionHomeomorph 1)
            (evolutionHomeomorph 1 ⁻¹' D)) (p : Point) (hp : p ∈ D) :
            IsSliceRegularAt u p := by
          have hx : (evolutionHomeomorph 1).symm p ∈ evolutionHomeomorph 1 ⁻¹' D := by
            simpa using hp
          have hj := hu.contDiffAt
            ((hD.preimage (evolutionHomeomorph 1).continuous).mem_nhds hx)
          have h := (hj.of_le (by simp : (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞))).comp
            (p.time, p.position, p.velocity) (evolutionProdCLE 1).symm.contDiff.contDiffAt
          apply IsSliceRegularAt.of_contDiffAt
          have heq : (fun q => (u ∘ evolutionHomeomorph 1) ((evolutionProdCLE 1).symm q)) =
              rawLift u := by
            funext q
            simp [evolutionHomeomorph, rawLift, KineticPoint.homeomorphProd,
              KineticPoint.isometryEquivProd, KineticPoint.equivProd]
            rfl
          change ContDiffAt ℝ 2
            (fun q => (u ∘ evolutionHomeomorph 1) ((evolutionProdCLE 1).symm q))
            (p.time, p.position, p.velocity) at h
          rwa [heq] at h
        obtain ⟨⟨-, C, -, hCb⟩, -, hsm, -, heq, hc, ht, hl, -⟩ :=
          kinetic_duhamel hH (by omega) autonomousWholeDomain_admissible (zeroCurve_piecewiseC1 1)
            hlam hLam one_pos (evolutionCoefficient A.a) (evolutionCoefficient_smooth A)
            (evolutionCoefficient_symmetric A.a) (evolutionCoefficient_bounds A)
            (identityDrift 1) (identityDrift_smooth 1) (identityDrift_bounds 1)
            E.1 E.2 hE T g hgn hgs hgc hgU
        have hΩ := isOpen_of_isAdmissibleEvolutionDomain autonomousWholeDomain_admissible
        have hD := isOpen_duhamelCylinder (γ := fun _ => 0) hΩ continuous_const T
        have hs : movingClosedSlab autonomousWholeDomain (fun _ => 0) p₀.time T ⊆
            evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) T :=
          fun _ hp => ⟨hp.2.1, hp.2.2⟩
        have ha : movingActiveSlab autonomousWholeDomain (fun _ => 0) p₀.time T ⊆
            evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T :=
          fun _ hp => ⟨hp.2.1, hp.2.2⟩
        have hreg := fun p hp => source_slice_regular hD hsm p (ha hp)
        have hmax := growth_comparison hΩ continuous_const hlam (evolutionCoefficient_bounds A)
          (identityDrift_bounds 1).1 (le_refl 0) zero_le_one
          (a := p₀.time) (T := T) (u := fun p => duhamelPotential E.2 T g p - q p)
          ⟨C, fun p hp => by
            have h1 := (le_abs_self (duhamelPotential E.2 T g p)).trans (hCb p)
            have h2 := hqn p (hs hp)
            linarith only [h1, h2]⟩
          ((hc.mono hs).sub hqc.continuousOn)
          (fun p hp => (hreg p hp).sub (hqr p hp.2.1.le))
          (fun p hp => by
            rw [viscousTransportedOperator_sub (hreg p hp) (hqr p hp.2.1.le),
              viscousTransportedOperator_zero, viscousTransportedOperator_zero, heq p (ha hp)]
            have h := hqo p (ha hp)
            linarith only [h])
          (fun p hp hpt => by rw [ht p hpt]; linarith only [hqn p (hs hp)])
          (fun p hp hpf => by rw [hl p hpf]; linarith only [hqn p (hs hp)])
        exact sub_nonpos.mp (hmax p₀ ⟨le_rfl, hp₀.1.le, subset_closure hp₀.2⟩)
      have velocityOccupationBarrier_operator (p : Point) (hp : p.time ≤ T) :
          transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1)
          (velocityOccupationBarrier r Lam T) p ≤
            -lam * (r ^ 2 / Real.sqrt (r ^ 2 + (p.position 0) ^ 2) ^ 3) := by
        have hLam := (hlam.le.trans (A.bounds 0 0).1).trans (A.bounds 0 0).2
        have hR : 0 < r ^ 2 + 2 * Lam * (T - p.time) :=
          add_pos_of_pos_of_nonneg (sq_pos_of_pos hr)
            (mul_nonneg (mul_nonneg (by norm_num) hLam) (sub_nonneg.mpr hp))
        have h0 : 0 < r ^ 2 + 2 * 0 * (T - p.time) := by simpa using sq_pos_of_pos hr
        have he : velocityOccupationBarrier r Lam T =
            (fun p => (velocityHeatProfile (r ^ 2) Lam T ∘ terminalPhysicalPoint) p -
              (velocityHeatProfile (r ^ 2) 0 T ∘ terminalPhysicalPoint) p) := rfl
        rw [← viscousTransportedOperator_zero, he,
          viscousTransportedOperator_sub (velocityHeatProfile_native_regular _ _ _ p hR)
            (velocityHeatProfile_native_regular _ _ _ p h0),
          viscousTransportedOperator_zero, viscousTransportedOperator_zero,
          terminalPhysicalPoint_operator, terminalPhysicalPoint_operator,
          velocityHeatProfile_operator (terminalPhysicalPoint p) h0 A.a]
        have hh := velocityHeatProfile_operator_nonpos (terminalPhysicalPoint p) hR hLam
          A.a (A.bounds _ _).2
        have hl := (A.bounds (p.velocity 0) (p.position 0)).1
        have hd : 0 ≤ r ^ 2 / Real.sqrt (r ^ 2 + (p.position 0) ^ 2) ^ 3 := by positivity
        dsimp only [terminalPhysicalPoint] at hh ⊢
        simp
        rw [mul_div_assoc]
        have hm := mul_le_mul_of_nonneg_right hl hd
        linarith
      have velocityOccupationBarrier_bounds {r : ℝ} {Lam : ℝ} (_hr : 0 < r) (hLam : 0 ≤ Lam) (p : Point) (hp : p.time ≤ T) :
          0 ≤ velocityOccupationBarrier r Lam T p ∧
          velocityOccupationBarrier r Lam T p ≤ Real.sqrt (2 * Lam * (T - p.time)) := by
        have h := velocityConvexProfile_increment (sq_nonneg r)
          (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hLam)
            (sub_nonneg.mpr hp)) (p.position 0)
        simpa [velocityOccupationBarrier, velocityHeatProfile, terminalPhysicalPoint] using h
      have velocityOccupationBarrier_regular {Lam : ℝ} (hLam : 0 ≤ Lam) (p : Point) (hp : p.time ≤ T) :
          IsSliceRegularAt (velocityOccupationBarrier r Lam T) p := by
        apply IsSliceRegularAt.of_contDiffAt
        change ContDiffAt ℝ 2 (fun q : ℝ × (PDE.Vec 1 × PDE.Vec 1) =>
          Real.sqrt (r ^ 2 + 2 * Lam * (T - q.1) + (q.2.1 0) ^ 2) -
            Real.sqrt (r ^ 2 + 2 * 0 * (T - q.1) + (q.2.1 0) ^ 2)) _
        apply ContDiffAt.sub
        · apply ContDiffAt.sqrt (by fun_prop)
          have hh := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hLam)
            (sub_nonneg.mpr hp)
          exact ne_of_gt (by nlinarith [sq_pos_of_pos hr, sq_nonneg (p.position 0)])
        · apply ContDiffAt.sqrt (by fun_prop)
          exact ne_of_gt (by nlinarith [sq_pos_of_pos hr, sq_nonneg (p.position 0)])
      have velocityOccupationBarrier_continuous :
          Continuous (velocityOccupationBarrier r Lam T) := by
        unfold velocityOccupationBarrier velocityHeatProfile velocityConvexProfile
        apply Continuous.sub <;> apply Real.continuous_sqrt.comp <;>
          exact (continuous_const.add (continuous_const.mul
            (continuous_const.sub continuous_time))).add
              ((continuous_apply 0).comp continuous_position |>.pow 2)
      let g := fun q : Point => f (q.time, q.position, q.velocity) *
        (lam * velocityOccupationDensity r (q.position 0))
      have hgs : ContDiff ℝ (⊤ : ℕ∞) (rawLift g) := by
        exact hf.mul (contDiff_const.mul ((velocityOccupationDensity_contDiff hr).comp
          ((contDiff_apply ℝ ℝ 0).comp contDiff_snd.fst)))
      have hc : HasCompactSupport g :=
        (hfc.comp_homeomorph (KineticPoint.homeomorphProd 1)).mul_right
      have hu : tsupport g ⊆ evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T := by
        intro q hq
        have hqf := tsupport_mul_subset_left hq
        have hraw : (q.time, q.position, q.velocity) ∈ tsupport f := by
          exact tsupport_comp_subset_preimage f
            (KineticPoint.homeomorphProd 1).continuous hqf
        refine ⟨hfU hraw, ?_⟩
        change q.position ∈ movingDomain (wholeSpace 1) (fun _ => 0) q.time
        rw [movingDomain_wholeSpace]
        trivial
      have hLn := hlam.le.trans hLam
      have hpoint : p ∈ evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T := by
        refine ⟨hp, ?_⟩
        change p.position ∈ movingDomain (wholeSpace 1) (fun _ => 0) p.time
        rw [movingDomain_wholeSpace]
        trivial
      have hb := velocity_duhamel_le_barrier g
        (velocityOccupationBarrier r Lam T)
        (fun q => mul_nonneg (hf01 _).1
          (mul_nonneg hlam.le (velocityOccupationDensity_nonneg r _))) hgs hc hu
        (velocityOccupationBarrier_continuous)
        (velocityOccupationBarrier_regular hLn)
        (fun q hq => (velocityOccupationBarrier_bounds hr hLn q hq.1).1)
        (fun q hq => by
          have he := velocityOccupationBarrier_operator q hq.1.le
          have hm := mul_le_mul_of_nonneg_right (hf01 (q.time, q.position, q.velocity)).2
            (mul_nonneg hlam.le (velocityOccupationDensity_nonneg r (q.position 0)))
          change _ ≤ -(f _ * (lam * velocityOccupationDensity r (q.position 0)))
          change _ ≤ -lam * velocityOccupationDensity r (q.position 0) at he
          linarith) p hpoint
      exact hb.trans (velocityOccupationBarrier_bounds hr hLn p hp.le).2
    let g := fun q : Point => f (q.time, q.position, q.velocity) *
      (lam * velocityOccupationDensity r (q.position 0))
    have hs : ContDiff ℝ (⊤ : ℕ∞) (rawLift g) := hf.mul
      (contDiff_const.mul ((velocityOccupationDensity_contDiff hr).comp
        ((contDiff_apply ℝ ℝ 0).comp contDiff_snd.fst)))
    have hc : HasCompactSupport g :=
      (hfc.comp_homeomorph (KineticPoint.homeomorphProd 1)).mul_right
    have hg : Continuous g := hs.continuous.comp (KineticPoint.homeomorphProd 1).continuous
    have hn : ∀ q, 0 ≤ g q := fun q => mul_nonneg (hf01 _).1
      (mul_nonneg hlam.le (velocityOccupationDensity_nonneg r _))
    have hrep := duhamelPotential_eq_greenMeasure E.2 autonomousWholeDomain_measurable
      continuous_const T g hn hg hc 0 hT (velocityInitialState z)
    have hb := velocity_profile_source_bound
      ⟨0, fun _ => z.2, fun _ => z.1⟩ hT
    change (∫ q, rawLift g q ∂(velocityGreen E T hT z).map velocityElapsedRaw) ≤ _
    rw [integral_map (velocityElapsedRaw_measurable T).aemeasurable
      hs.continuous.aestronglyMeasurable]
    have hI (D : ℝ) (hD : 0 < D) (hDT : D = T) :
        (∫ q : ElapsedTime (ENNReal.ofReal D) × EvolutionAmbientState 1,
          g ⟨0 + q.1.1, q.2.1, q.2.2⟩ ∂greenMeasure E.2 0 (ENNReal.ofReal D)
            (ENNReal.ofReal_pos.mpr hD) (Measure.dirac (velocityInitialState z))) =
        ∫ q, rawLift g (velocityElapsedRaw q) ∂velocityGreen E T hT z := by
      subst D
      apply integral_congr_ae
      exact Eventually.of_forall fun q => by
        change g ⟨0 + q.1.1, q.2.1, q.2.2⟩ = g ⟨q.1.1, q.2.1, q.2.2⟩
        rw [show 0 + q.1.1 = q.1.1 by ring]
    have hi := (hI (T - 0) (sub_pos.mpr hT) (by ring)).symm.trans hrep.symm
    exact hi.trans_le (by simpa [velocityInitialState, wholeQuery, wholeSpaceQuery] using hb)
  let mu := velocityGreenRaw E T hT z
  let g := fun q : ℝ × EvolutionAmbientState 1 =>
    f q * (lam * velocityOccupationDensity r (q.2.1 0))
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.mul
    (contDiff_const.mul ((velocityOccupationDensity_contDiff hr).comp
      ((contDiff_apply ℝ ℝ 0).comp contDiff_snd.fst)))
  have hgc : HasCompactSupport g := hfc.mul_right
  have hi : Integrable g mu := hg.continuous.integrable_of_hasCompactSupport hgc
  have hfint : Integrable f mu := hf.continuous.integrable_of_hasCompactSupport hfc
  have hc0 : 0 ≤ 64 * r / lam := by positivity
  have hm : (∫ q in velocityRawBand r, f q ∂mu) ≤
      (64 * r / lam) * ∫ q, g q ∂mu := by
    rw [← integral_indicator (velocityRawBand_measurable r), ← integral_const_mul]
    apply integral_mono (hfint.indicator (velocityRawBand_measurable r)) (hi.const_mul _)
    intro q
    by_cases hq : q ∈ velocityRawBand r
    · rw [indicator_of_mem hq]
      have hd := velocityConvexProfile_band_lower hr hq
      have hl : 1 ≤ (64 * r / lam) *
          (lam * velocityOccupationDensity r (q.2.1 0)) := by
        have he : (64 * r / lam) * (lam * velocityOccupationDensity r (q.2.1 0)) =
            (64 * r) * velocityOccupationDensity r (q.2.1 0) := by
          field_simp
        rw [he]
        simpa only [velocityOccupationDensity, mul_comm] using
          (div_le_iff₀ (by positivity : 0 < 64 * r)).mp hd
      have hh := mul_le_mul_of_nonneg_left hl (hf01 q).1
      dsimp only [g]
      nlinarith only [hh]
    · rw [indicator_of_notMem hq]
      exact mul_nonneg hc0 (mul_nonneg (hf01 q).1
        (mul_nonneg hlam.le (velocityOccupationDensity_nonneg r _)))
  exact hm.trans (mul_le_mul_of_nonneg_left
    (velocityGreenRaw_source_integral_le) hc0)

/-- Uniform measurable-band occupation bound, with a constant depending only on ellipticity. -/
theorem velocityGreenRaw_band_mass_le (hH : HormanderHypoellipticityStatement)
    {lam Lam r T : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (hr : 0 < r) (hT : 0 < T) (z : Z) :
    velocityGreenRaw E T hT z (velocityRawBand r) ≤
      ENNReal.ofReal ((64 * r / lam) * Real.sqrt (2 * Lam * T)) := by
  let mu := (velocityGreenRaw E T hT z).restrict (velocityRawBand r)
  have hs : mu.restrict {q | q.1 < T} = mu := by
    dsimp only [mu]
    rw [Measure.restrict_comm, velocityGreenRaw_restrict_past]
    exact measurableSet_lt measurable_fst measurable_const
  have h := measure_mass_le_of_smooth_unit_tests mu
    (isOpen_lt continuous_fst continuous_const) hs
    ((64 * r / lam) * Real.sqrt (2 * Lam * T))
    (fun f hf hfc hfU hf01 =>
      velocityGreenRaw_band_test_le hH hlam hLam A E hE hr hT z f hf hfc hfU hf01)
  simpa only [mu, Measure.restrict_apply MeasurableSet.univ, univ_inter] using h


/-- Velocity band on the native terminal state. -/
def velocityNativeBand (r : ℝ) : Set (EvolutionAmbientState 1) := {w | |w.1 0| ≤ 3 * r}

/-- Native terminal velocity bands are measurable. -/
theorem velocityNativeBand_measurable (r : ℝ) : MeasurableSet (velocityNativeBand r) := by
  exact measurableSet_le
    (continuous_abs.measurable.comp ((measurable_pi_apply 0).comp measurable_fst))
    measurable_const

/-- Actual transition probability of the velocity band, extended to negative times by time zero. -/
def velocityBandProbability (E : FullSpaceEvolution) (r : ℝ) (z : Z) (t : ℝ) : ℝ≥0∞ :=
  E.2.master (wholeQuery (Real.toNNReal t) z) (velocityNativeBand r)


/-- Actual band probabilities depend measurably on elapsed time. -/
theorem velocityBandProbability_measurable (E : FullSpaceEvolution) (r : ℝ) (z : Z) :
    Measurable (velocityBandProbability E r z)  := by
  have velocityWholeQuery_measurable :
      Measurable (fun t : ℝ => wholeQuery (Real.toNNReal t) z) := by
    unfold wholeQuery wholeSpaceQuery
    fun_prop
  exact (E.2.master.measurable_coe (velocityNativeBand_measurable r)).comp
    (velocityWholeQuery_measurable)

/-- Band transition probabilities are bounded by one. -/
theorem velocityBandProbability_le_one (E : FullSpaceEvolution) (r : ℝ) (z : Z) (t : ℝ) :
    velocityBandProbability E r z t ≤ 1 :=
  (measure_mono (subset_univ _)).trans (E.2.mass_le_one _)

/-- Green band mass is the unnormalized elapsed-time integral of transition probabilities. -/
theorem velocityGreenRaw_band_eq_lintegral (E : FullSpaceEvolution)
    {T : ℝ} (hT : 0 < T) (r : ℝ) (z : Z) :
    velocityGreenRaw E T hT z (velocityRawBand r) =
      ∫⁻ t in Ioo 0 T, velocityBandProbability E r z t := by
  let B := velocityElapsedRaw (T := T) ⁻¹' velocityRawBand r
  have hB : MeasurableSet B :=
    (velocityElapsedRaw_measurable T) (velocityRawBand_measurable r)
  rw [velocityGreenRaw, Measure.map_apply (velocityElapsedRaw_measurable T)
    (velocityRawBand_measurable r), ← lintegral_indicator_one hB]
  rw [velocityGreen, greenMeasure_spec E.2 0 (ENNReal.ofReal T) (ENNReal.ofReal_pos.mpr hT)
    (Measure.dirac (velocityInitialState z)) _ (measurable_one.indicator hB)]
  rw [lintegral_dirac]
  have he (t : ElapsedTime (ENNReal.ofReal T)) :
      elapsedQuery 0 (velocityInitialState z) t = wholeQuery (Real.toNNReal t.1) z := by
    apply Subtype.ext
    simp [elapsedQuery, velocityInitialState, wholeQuery, wholeSpaceQuery, Real.coe_toNNReal _ t.2.1.le]
  have hh : (∫⁻ t : ElapsedTime (ENNReal.ofReal T),
      ∫⁻ w, B.indicator 1 (t, w) ∂E.2.master (elapsedQuery 0 (velocityInitialState z) t)
        ∂elapsedVolume (ENNReal.ofReal T)) =
      ∫⁻ t : ElapsedTime (ENNReal.ofReal T), velocityBandProbability E r z t
        ∂elapsedVolume (ENNReal.ofReal T) := by
    apply lintegral_congr
    intro t
    rw [he]
    change (∫⁻ w, (velocityNativeBand r).indicator 1 w
      ∂E.2.master (wholeQuery (Real.toNNReal t.1) z)) = _
    exact lintegral_indicator_one (velocityNativeBand_measurable r)
  rw [hh]
  have hi := lintegral_subtype_comap (μ := (volume : Measure ℝ))
    (measurableSet_elapsedTime (ENNReal.ofReal T)) (velocityBandProbability E r z)
  apply hi.trans
  have hset : {t : ℝ | 0 < t ∧ ENNReal.ofReal t < ENNReal.ofReal T} = Ioo 0 T := by
    ext t
    exact and_congr_right fun _ => ENNReal.ofReal_lt_ofReal_iff hT
  rw [hset]




/-- The literal unit indicator of the physical velocity band. -/
def velocityBandDatum (r : ℝ) : BoundedBorel (EvolutionAmbientState 1) := by
  let B : Set (EvolutionAmbientState 1) := {w | |w.2 0| ≤ 3 * r}
  have hB : MeasurableSet B := measurableSet_le
    (continuous_abs.measurable.comp ((measurable_pi_apply 0).comp measurable_snd))
    measurable_const
  exact ⟨B.indicator (fun _ => 1), measurable_const.indicator hB,
    ⟨1, zero_le_one, fun w => by
      by_cases hw : |w.2 0| ≤ 3 * r <;> simp [B, Set.indicator, hw]⟩⟩

/-- The source band test evaluated by the actual physical semigroup. -/
def velocityBandAction (E : FullSpaceEvolution) (r t : ℝ) (z : Z) : ℝ :=
  fullSpacePhysicalSemigroup E (Real.toNNReal t) (velocityBandDatum r)
    (fun _ => z.1, fun _ => z.2)

/-- The semigroup band action is exactly the real transition probability. -/
theorem velocityBandAction_eq_probability {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E) (r t : ℝ) (z : Z) :
    velocityBandAction E r t z = (velocityBandProbability E r z t).toReal := by
  rw [velocityBandAction, fullSpacePhysicalSemigroup_eq_action A E hE,
    fullSpaceAction_eq_zeroTime A E hE _ _ (Real.toNNReal t).property]
  have : IsFiniteMeasure (E.2.master (wholeQuery (Real.toNNReal t) z)) :=
    ⟨(E.2.mass_le_one _).trans_lt ENNReal.one_lt_top⟩
  change (∫ w, (velocityNativeBand r).indicator (fun _ => 1) w
    ∂E.2.master (wholeQuery (Real.toNNReal t) z)) = _
  rw [integral_indicator (velocityNativeBand_measurable r)]
  simp [integral_const, Measure.real, velocityBandProbability, Measure.restrict_apply MeasurableSet.univ, univ_inter]

/-- In physical scalar coordinates the same probability is the band mass of `kernelXV`. -/
theorem velocityBandProbability_eq_kernelXV (E : FullSpaceEvolution) (r t : ℝ) (z : Z) :
    velocityBandProbability E r z t =
      kernelXV E (Real.toNNReal t) z {w | |w.2| ≤ 3 * r} := by
  rw [kernelXV, Measure.map_apply nativeToXV_measurable]
  · rfl
  · exact measurableSet_le (continuous_abs.measurable.comp measurable_snd) measurable_const

/-- The literal semigroup band test is integrable on every finite time interval. -/
theorem velocityBandAction_integrable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E) (r T : ℝ) (z : Z) :
    Integrable (fun t => velocityBandAction E r t z) (volume.restrict (Ioc 0 T))  := by
  have velocityBandProbability_toReal_integrable :
      Integrable (fun t => (velocityBandProbability E r z t).toReal)
      (volume.restrict (Ioc 0 T)) := open Filter in by
    apply Integrable.mono' (integrable_const 1)
      (velocityBandProbability_measurable E r z).ennreal_toReal.aestronglyMeasurable
    exact Eventually.of_forall fun t => by
      rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top
        (velocityBandProbability_le_one E r z t)
  have he : (fun t => velocityBandAction E r t z) =
      fun t => (velocityBandProbability E r z t).toReal :=
    funext fun t => velocityBandAction_eq_probability A E hE r t z
  rw [he]
  exact velocityBandProbability_toReal_integrable



/-- The sharp quadratic moment bound in the source's real-integral normalization. -/
theorem velocity_moment_le {lam Lam : ℝ} (hlam : 0 < lam)
    (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (T : NNReal) (z : Z) :
    (∫ w, (w.2 - z.2) ^ 2 ∂kernelXV E T z) ≤ 2 * Lam * (T : ℝ)  := by
  have velocity_moment_integrable :
      Integrable (fun w : Z => (w.2 - z.2) ^ 2) (kernelXV E T z) := by
    apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
      (Filter.Eventually.of_forall (fun w : Z => sq_nonneg (w.2 - z.2)))).mp
    exact ne_of_lt ((kernelXV_velocity_2_moment hlam A E hE z T).trans_lt
      ENNReal.ofReal_lt_top)
  have h := kernelXV_velocity_2_moment hlam A E hE z T
  rw [← ofReal_integral_eq_lintegral_ofReal
    (velocity_moment_integrable)
    (Filter.Eventually.of_forall (fun w : Z => sq_nonneg (w.2 - z.2)))] at h
  have hL : 0 ≤ Lam := (hlam.le.trans (A.bounds 0 0).1).trans (A.bounds 0 0).2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h


/-- Source occupation bound for any realizing full-space evolution. -/
theorem velocity_occupation_le (hH : HormanderHypoellipticityStatement)
    {lam Lam r T : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (hr : 0 < r) (hT : 0 < T) (z : Z) :
    (∫ t in Ioc 0 T, velocityBandAction E r t z) ≤
      (64 * Real.sqrt (2 * Lam) / lam) * r * Real.sqrt T  := by
  have velocity_band_integral_eq_green :
      (∫ t in Ioc 0 T, (velocityBandProbability E r z t).toReal) =
      (velocityGreenRaw E T hT z (velocityRawBand r)).toReal := open Filter SectionTwo in by
    rw [integral_Ioc_eq_integral_Ioo, integral_toReal
      (velocityBandProbability_measurable E r z).aemeasurable]
    · rw [velocityGreenRaw_band_eq_lintegral E hT r z]
    · exact Eventually.of_forall fun t =>
        (velocityBandProbability_le_one E r z t).trans_lt ENNReal.one_lt_top
  have hLn : 0 ≤ Lam := hlam.le.trans hLam
  have h := velocityGreenRaw_band_mass_le hH hlam hLam A E hE hr hT z
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (by positivity)] at hb
  have ha : (∫ t in Ioc 0 T, velocityBandAction E r t z) =
      (∫ t in Ioc 0 T, (velocityBandProbability E r z t).toReal) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => velocityBandAction_eq_probability A E hE r t z
  rw [ha, velocity_band_integral_eq_green]
  apply hb.trans_eq
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Lam)]
  ring

/-- Uniform constant, actual measurable band occupation, and sharp real quadratic moment.
Only the named Hörmander and Lieberman construction inputs remain explicit. -/
theorem velocity_occupation_and_moment
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (r T : ℝ) (z : Z),
      0 < r → 0 < T →
      let E := fullSpaceEvolution hH hLE hlam hLam A
      (∫ t in Ioc 0 T, velocityBandAction E r t z) ≤ C * r * Real.sqrt T ∧
        (∫ w, (w.2 - z.2) ^ 2 ∂kernelXV E (Real.toNNReal T) z) ≤ 2 * Lam * T := by
  refine ⟨64 * Real.sqrt (2 * Lam) / lam, ?_, ?_⟩
  · have hLp : 0 < Lam := hlam.trans_le hLam
    positivity
  · intro A r T z hr hT
    let E := fullSpaceEvolution hH hLE hlam hLam A
    have hE := fullSpaceEvolution_spec hH hLE hlam hLam A
    refine ⟨velocity_occupation_le hH hlam hLam A E hE hr hT z, ?_⟩
    have hm := velocity_moment_le hlam A E hE (Real.toNNReal T) z
    simpa only [Real.coe_toNNReal T hT.le] using hm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

