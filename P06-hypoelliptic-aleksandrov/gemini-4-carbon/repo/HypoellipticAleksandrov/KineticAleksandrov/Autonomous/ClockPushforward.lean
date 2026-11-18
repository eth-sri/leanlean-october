module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforwardValue

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov SectionTwo TheoremA Evolution Green
open scoped ENNReal NNReal

/-- The advancing-clock cone holds on the actual infinite physical Green measure. -/
theorem clock_forward_cone_infinite
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : StripPole c.activeInterval ⊤) :
    ∀ᵐ p ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤ e,
      p.time - e.1.time ≤ 2 * c.r ^ 2 * (c.map e.1 p).time := by
  apply stripGreen_infinite_ae_of_finite hH hLE hlam hLam A c.activeInterval e
  intro T ht
  exact (clock_forward_cone_finite hH hLE hlam hLam A c T
    (stripPoleFinite c.activeInterval e T ht)).2



/-- The actual normalized infinite Green measure has finite mass, by the interval density
  estimate. -/
instance clockNativeGreen_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    IsFiniteMeasure (clockNativeGreen hH hLE hlam hLam A c e he) := by
  obtain ⟨C, -, hc⟩ := Interval.interval_green_finite_mass hH hLE
    (3 * lam / 5) (3 * Lam) (9 / 25) 9 (3 / 2) (by positivity) (by norm_num)
  have hh := @hc (-3 / 4) (3 / 4) (by norm_num)
    (c.extendedCoefficient lam A.a e) c.extendedVectorDrift
    (c.extended_sourceSetting hlam hLam A e)
    (intervalDomain_measurable clockNormalizedInterval)
    (clockEvolution hH hLE hlam hLam A c e).1
    (clockEvolution hH hLE hlam hLam A c e).2
    (clockEvolution_spec hH hLE hlam hLam A c e) (by norm_num) 0
    (Measure.dirac (clockInitialState c e he)) isFiniteMeasure_dirac
    (clockNativeGreen hH hLE hlam hLam A c e he)
    (clockNativeGreen_spec hH hLE hlam hLam A c e he)
  exact ⟨hh.2⟩

/-- Finite mass survives the established physical coordinate map. -/
instance clockGreen_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    IsFiniteMeasure (clockGreen hH hLE hlam hLam A c e he) := by
  unfold clockGreen
  infer_instance

/-- The physical velocity weight is Borel. -/
theorem clock_velocity_weight_measurable :
    Measurable (fun p : Point => ENNReal.ofReal |p.velocity 0|) :=
  (((continuous_apply 0).comp continuous_velocity).abs.measurable).ennreal_ofReal

/-- The actual physical infinite Green has finite mass after weighting by velocity. -/
instance clockWeightedGreen_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    IsFiniteMeasure ((stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      ⟨e, WithTop.coe_lt_top _, he⟩).withDensity (fun p => ENNReal.ofReal |p.velocity 0|)) := by
  apply isFiniteMeasure_withDensity
  apply ne_of_lt
  apply lt_of_le_of_lt
    (lintegral_mono_ae (g := fun _ => ENNReal.ofReal (3 * |c.vbar| / 2)) ?_) ?_
  · filter_upwards [stripGreen_infinite_ae_future_carrier hH hLE hlam hLam A c.activeInterval
      ⟨e, WithTop.coe_lt_top _, he⟩] with p hp
    exact ENNReal.ofReal_le_ofReal (c.active_abs_bounds hp.2).2
  · rw [lintegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)


/-- The normalized physical support is the open positive-time active strip. -/
def clockGreenSupport : Set Point := {p | 0 < p.time ∧ p.velocity 0 ∈ normalizedActive}

/-- The support used for determining the clock Green measure is open. -/
theorem isOpen_clockGreenSupport : IsOpen clockGreenSupport :=
  (isOpen_lt continuous_const continuous_time).inter
    (isOpen_Ioo.preimage ((continuous_apply 0).comp continuous_velocity))




/-- The literal position clock pushes velocity-weighted physical Green to the actual normalized
Green with factor exactly `|vbar| r²`. No density or analytic bridge is a premise. -/
theorem clock_green_pushforward
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    Measure.map (c.map e) ((stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      ⟨e, WithTop.coe_lt_top _, he⟩).withDensity (fun p => ENNReal.ofReal |p.velocity 0|)) =
      ENNReal.ofReal (|c.vbar| * c.r ^ 2) • clockGreen hH hLE hlam hLam A c e he    := by
  have clock_weighted_pushforward_ae_support :
      ∀ᵐ p ∂Measure.map (c.map e)
      ((stripGreen hH hLE hlam hLam A c.activeInterval ⊤
        ⟨e, WithTop.coe_lt_top _, he⟩).withDensity
        (fun p => ENNReal.ofReal |p.velocity 0|)), p ∈ clockGreenSupport := by
    apply (c.homeomorph e).measurableEmbedding.ae_map_iff.mpr
    apply (ae_withDensity_iff clock_velocity_weight_measurable).mpr
    filter_upwards [stripGreen_infinite_ae_future_carrier hH hLE hlam hLam A c.activeInterval
      ⟨e, WithTop.coe_lt_top _, he⟩,
      clock_forward_cone_infinite hH hLE hlam hLam A c
        ⟨e, WithTop.coe_lt_top _, he⟩] with p hp hc _
    refine ⟨?_, (c.mem_active_iff (p.velocity 0)).mp hp.2⟩
    change 0 < (c.map e p).time
    have hs := sq_pos_of_pos c.positive
    have ht := hp.1
    nlinarith
  have clockGreen_ae_support :
      ∀ᵐ p ∂clockGreen hH hLE hlam hLam A c e he, p ∈ clockGreenSupport := by
    rw [ae_iff]
    have hz := (reconstruction_green_infinite_zero_of_finite clockNormalizedInterval (clockEvolution hH hLE hlam hLam A c e) (clockPhysicalPole c e he) clockGreenSupportᶜ isOpen_clockGreenSupport.measurableSet.compl) (fun T ht => by
      apply (ae_iff (p := fun p => p ∈ clockGreenSupport)).mp
      filter_upwards [reconstruction_green_ae_time_gt clockNormalizedInterval
        (clockEvolution hH hLE hlam hLam A c e).2 T
        ⟨(clockPhysicalPole c e he).1, WithTop.coe_lt_coe.mpr ht,
          (clockPhysicalPole c e he).2.2⟩,
        stripGreenOfKernel_ae_mem_stripPast clockNormalizedInterval
          (clockEvolution hH hLE hlam hLam A c e).2 T
          ⟨(clockPhysicalPole c e he).1, WithTop.coe_lt_coe.mpr ht,
            (clockPhysicalPole c e he).2.2⟩] with p hp hq
      exact ⟨hp, hq.2⟩)
    exact (congrArg (fun μ : Measure Point => μ clockGreenSupportᶜ)
      (clockGreen_eq_stripGreenOfKernel hH hLE hlam hLam A c e he)).trans hz
  have clock_weighted_test_infinite (f : exitProbeSubmodule) (hfn : ∀ p, 0 ≤ exitProbePhysical f p) (hs : tsupport (exitProbePhysical f) ⊆
      {p | 0 < p.time ∧ p.velocity 0 ∈ normalizedActive}) :
      (∫ p, clockWeightedProbe c e f p ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      ⟨e, WithTop.coe_lt_top _, he⟩) =
      (|c.vbar| * c.r ^ 2) * ∫ p, exitProbePhysical f p
        ∂clockGreen hH hLE hlam hLam A c e he := by
    obtain ⟨R, hR, htimes, hz⟩ := clock_probe_cutoff f
    let ei : StripPole c.activeInterval ⊤ := ⟨e, WithTop.coe_lt_top _, he⟩
    let U := e.time + 2 * c.r ^ 2 * R + 1
    have hU : e.time < U := by
      have hpositive : 0 < 2 * c.r ^ 2 * R :=
        mul_pos (mul_pos (by norm_num) (sq_pos_of_pos c.positive)) hR
      linarith
    have hs' : tsupport (exitProbePhysical f) ⊆
        {p | p.time < R + 1 ∧ p.velocity 0 ∈ clockNormalizedInterval.carrier} := by
      intro p hp
      exact ⟨by linarith [htimes p hp], (hs hp).2⟩
    have hf := clock_weighted_test_finite hH hLE hlam hLam A c e R (R + 1) U
      (by linarith) (by dsimp [U]; linarith) (stripPoleFinite c.activeInterval ei U hU) rfl f hfn hs' hz
    have hstab : (∫ p, clockWeightedProbe c e f p
        ∂(stripGreen hH hLE hlam hLam A c.activeInterval ⊤ ei).restrict {p | p.time < U}) =
        ∫ p, clockWeightedProbe c e f p ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤ ei := by
      apply setIntegral_eq_integral_of_ae_compl_eq_zero
      filter_upwards [clock_forward_cone_infinite hH hLE hlam hLam A c ei] with p hp hlate
      have hclock : R ≤ (c.map e p).time := by
        have ht := not_lt.mp hlate
        dsimp [U] at ht
        nlinarith
      change |p.velocity 0| * exitProbePhysical f (c.map e p) = 0
      rw [hz _ hclock, mul_zero]
    exact hstab.symm.trans ((congrArg (fun μ : Measure Point =>
      ∫ p, clockWeightedProbe c e f p ∂μ) (stripGreen_finite_restrict_infinite hH hLE hlam hLam A c.activeInterval ei U hU).symm).trans
        (hf.trans (congrArg (fun x => (|c.vbar| * c.r ^ 2) * x) (clockSourcePotential_eq_infinite_green hH hLE hlam hLam A c e he R (R + 1) (by linarith) (by linarith) f hz))))
  have : IsFiniteMeasure ((stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      ⟨e, WithTop.coe_lt_top _, he⟩).withDensity
      (fun p => ENNReal.ofReal |p.velocity 0|)) :=
    clockWeightedGreen_isFiniteMeasure hH hLE hlam hLam A c e he
  have := Measure.isFiniteMeasure_map
    ((stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      ⟨e, WithTop.coe_lt_top _, he⟩).withDensity
      (fun p => ENNReal.ofReal |p.velocity 0|)) (c.map e)
  have := Measure.smul_finite (clockGreen hH hLE hlam hLam A c e he)
    (ENNReal.ofReal_ne_top : ENNReal.ofReal (|c.vbar| * c.r ^ 2) ≠ ⊤)
  apply nested_physical_measure_eq clockGreenSupport isOpen_clockGreenSupport
    (clock_weighted_pushforward_ae_support)
    (Measure.ae_smul_measure (clockGreen_ae_support) _)
  intro f hs hn
  have hweight' : (∫ p, exitProbePhysical f (c.map e p)
      ∂(stripGreen hH hLE hlam hLam A c.activeInterval ⊤
        ⟨e, WithTop.coe_lt_top _, he⟩).withDensity
        (fun p => ENNReal.ofReal |p.velocity 0|)) =
      ∫ p, clockWeightedProbe c e f p ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤
        ⟨e, WithTop.coe_lt_top _, he⟩ := by
    simpa [ENNReal.toReal_ofReal (abs_nonneg _), clockWeightedProbe]
      using (integral_withDensity_eq_integral_toReal_smul (μ := stripGreen hH hLE hlam hLam A c.activeInterval ⊤ ⟨e, WithTop.coe_lt_top _, he⟩) clock_velocity_weight_measurable (Filter.Eventually.of_forall (fun p => ENNReal.ofReal_lt_top)) (fun p => exitProbePhysical f (c.map e p)))
  exact (integral_map (μ := (stripGreen hH hLE hlam hLam A c.activeInterval ⊤ ⟨e, WithTop.coe_lt_top _, he⟩).withDensity (fun p => ENNReal.ofReal |p.velocity 0|)) (c.continuous_map e).measurable.aemeasurable (exitProbePhysical_continuous_compact f).1.measurable.aestronglyMeasurable).trans (hweight'.trans ((clock_weighted_test_infinite
    f hn hs).trans (by rw [integral_smul_measure, ENNReal.toReal_ofReal (mul_pos (abs_pos.mpr c.nonzero) (sq_pos_of_pos c.positive)).le]; rfl)))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

