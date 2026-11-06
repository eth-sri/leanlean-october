module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PoleDensityNorm
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PoleDensityExtension
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.SmoothEstimateDensity
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGreenTestSupport
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripGreen
import HypoellipticAleksandrov.KineticAleksandrov.Interval.Green
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PoleDensityGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PoleDensityNormalized
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PoleDensityTransport

/-! # Uniform one-sign pole density of the actual physical infinite Green measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped ENNReal NNReal
open SectionTwo TheoremA Evolution Green

/- The actual one-sign infinite physical Green measure has a nonnegative Lebesgue density
with the exact `r^(6/q-4)` norm bound. The constant is uniform in coefficient derivatives,
clock centres, radii and starting points. The analytic classical inputs remain explicit. -/
theorem one_sign_pole_density
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q ) (hq : 1 < q) (hq2 : q < (3 : ℝ) / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
      (he : e.velocity 0 ∈ c.active), ∃ g : Point → ℝ,
      Measurable g ∧ (∀ p, 0 ≤ g p) ∧
      stripGreen hH hLE hlam hLam A c.activeInterval ⊤ ⟨e, WithTop.coe_lt_top _, he⟩ =
        volume.withDensity (fun p => ENNReal.ofReal (g p)) ∧
      eLpNorm g (ENNReal.ofReal q) volume ≤ ENNReal.ofReal (C * c.r ^ (6 / q - 4 : ℝ)) ∧
      (∀ᵐ p ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤
        ⟨e, WithTop.coe_lt_top _, he⟩, e.time < p.time ∧ p.velocity 0 ∈ c.active) := by
  obtain ⟨C, hC, hc⟩ : ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
      (he : e.velocity 0 ∈ c.active), ∃ F : Point → ℝ,
      Measurable F ∧ (∀ p, 0 ≤ F p) ∧
      clockGreen hH hLE hlam hLam A c e he = volume.withDensity (fun p => ENNReal.ofReal (F p)) ∧
      eLpNorm F (ENNReal.ofReal q) volume ≤ ENNReal.ofReal C := by
    obtain ⟨C, hC, hc⟩ : ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
      (he : e.velocity 0 ∈ c.active),
      ∃ G : GreenCarrier 1 → ℝ≥0∞, Measurable G ∧
        clockNativeGreen hH hLE hlam hLam A c e he = (greenLebesgue 1).withDensity G ∧
        eLpNorm G (ENNReal.ofReal q) (greenLebesgue 1) ≤ ENNReal.ofReal C ∧
        clockNativeGreen hH hLE hlam hLam A c e he univ < ⊤ := by
      obtain ⟨C, hC, hc⟩ := Interval.interval_green_density hH hLE
        (3 * lam / 5) (3 * Lam) (9 / 25) 9 (3 / 2)
        (by positivity) (by linarith) (by norm_num) (by norm_num) (by norm_num) q hq hq2
      refine ⟨C, hC, ?_⟩
      intro A c e he
      obtain ⟨G, hm, hd, hn, hf⟩ := @hc (-3 / 4) (3 / 4) (by norm_num)
        (c.extendedCoefficient lam A.a e) c.extendedVectorDrift
        (c.extended_sourceSetting hlam hLam A e)
        (intervalDomain_measurable clockNormalizedInterval)
        (clockEvolution hH hLE hlam hLam A c e).1
        (clockEvolution hH hLE hlam hLam A c e).2
        (clockEvolution_spec hH hLE hlam hLam A c e) (by norm_num) 0
        (Measure.dirac (clockInitialState c e he)) isFiniteMeasure_dirac
        (clockNativeGreen hH hLE hlam hLam A c e he)
        (clockNativeGreen_spec hH hLE hlam hLam A c e he)
      have hm1 : (Measure.dirac (clockInitialState c e he)) univ = 1 :=
        Measure.dirac_apply_of_mem (mem_univ _)
      exact ⟨G, hm, hd, hn.trans (le_of_eq ((congrArg (fun x : ℝ≥0∞ => ENNReal.ofReal C * x) hm1).trans
        (mul_one _))), hf⟩
    refine ⟨C, hC, ?_⟩
    intro A c e he
    obtain ⟨G, hm, hd, hn, -⟩ := hc A c e he
    have _h_xinl_0 : ((greenLebesgue 1).withDensity G).map (elapsedPhysicalPoint 0) = (volume : Measure Point).withDensity (poleDensityExtend G) := by
      have hmap : ((greenLebesgue 1).withDensity G).map (elapsedPhysicalPoint 0) =
          ((greenLebesgue 1).map (elapsedPhysicalPoint 0)).withDensity (poleDensityExtend G) := by
        apply Measure.ext
        intro S hS
        rw [poleDensityElapsed_measurableEmbedding.map_apply,
          withDensity_apply _ (poleDensityElapsed_measurableEmbedding.measurable hS),
          withDensity_apply _ hS,
          setLIntegral_map hS (poleDensityExtend_measurable hm)
            poleDensityElapsed_measurableEmbedding.measurable]
        apply lintegral_congr
        intro q
        exact (poleDensityExtend_apply G q).symm
      have hres : ((volume : Measure Point).restrict {p | 0 < p.time}).withDensity
          (poleDensityExtend G) = volume.withDensity (poleDensityExtend G) := by
        apply Measure.ext
        intro S hS
        rw [withDensity_apply _ hS, withDensity_apply _ hS,
          Measure.restrict_restrict hS]
        rw [← lintegral_indicator hS, ← lintegral_indicator
          (hS.inter (isOpen_lt continuous_const continuous_time).measurableSet)]
        have hi : (S ∩ {p : Point | 0 < p.time}).indicator (poleDensityExtend G) =
            S.indicator (poleDensityExtend G) := by
          funext p
          by_cases hp : p ∈ S
          · by_cases ht : 0 < p.time
            · rw [Set.indicator_of_mem (show p ∈ S ∩ {p : Point | 0 < p.time}
                from ⟨hp, ht⟩), Set.indicator_of_mem hp]
            · have hz : poleDensityExtend G p = 0 := by
                by_contra hn
                exact ht (poleDensityExtend_support G hn)
              simp [hp, ht, hz]
          · simp [hp]
        exact congrArg (fun f : Point → ℝ≥0∞ => ∫⁻ p, f p ∂volume) hi

      exact hmap.trans ((congrArg (fun μ : Measure Point => μ.withDensity (poleDensityExtend G))
        poleDensityElapsed_map_volume).trans hres)
    have hphysical :=
      (congrArg (fun μ : Measure (GreenCarrier 1) => μ.map (elapsedPhysicalPoint 0)) hd).trans
        _h_xinl_0
    have hnorm : eLpNorm (poleDensityExtend G) (ENNReal.ofReal q) volume ≤
        ENNReal.ofReal C := (poleDensityExtend_eLpNorm hm _).le.trans hn
    obtain ⟨F, hFm, hFn, hFd, hFN, hFLp⟩ := real_density_of_eLpNorm_bound volume
      (clockGreen hH hLE hlam hLam A c e he) (poleDensityExtend G)
      (poleDensityExtend_measurable hm) hphysical q C (by linarith) hC.le hnorm
    refine ⟨F, hFm, hFn, hFd, ?_⟩
    exact (ENNReal.ofReal_toReal hFLp.eLpNorm_ne_top).symm.le.trans
      (ENNReal.ofReal_le_ofReal hFN)
  refine ⟨2 * C, by positivity, ?_⟩
  intro A c e he
  obtain ⟨F, hFm, hFn, hFd, hFN⟩ := hc A c e he
  have _h_xinl_0 : stripGreen hH hLE hlam hLam A c.activeInterval ⊤ ⟨e, WithTop.coe_lt_top _, he⟩ = volume.withDensity (fun p => ENNReal.ofReal (polePhysicalDensity c e F p)) := by
    let μ := stripGreen hH hLE hlam hLam A c.activeInterval ⊤ ⟨e, WithTop.coe_lt_top _, he⟩
    have hi : (μ.withDensity (fun p => ENNReal.ofReal |p.velocity 0|)).withDensity
        (fun p => ENNReal.ofReal (poleInverseVelocity c p)) = μ := by
      rw [← withDensity_mul μ clock_velocity_weight_measurable
        (poleInverseVelocity_measurable c).ennreal_ofReal]
      have hh : ((fun p => ENNReal.ofReal |p.velocity 0|) *
          fun p => ENNReal.ofReal (poleInverseVelocity c p)) =ᵐ[μ] 1 := by
        filter_upwards [stripGreen_infinite_ae_future_carrier hH hLE hlam hLam A c.activeInterval
          ⟨e, WithTop.coe_lt_top _, he⟩] with p hp
        have hc : 0 < |c.vbar| := abs_pos.mpr c.nonzero
        have hv : 0 < |p.velocity 0| := lt_of_lt_of_le (by linarith) (c.active_abs_bounds hp.2).1
        have hpactive : p.velocity 0 ∈ c.active := hp.2
        change ENNReal.ofReal |p.velocity 0| * ENNReal.ofReal (poleInverseVelocity c p) = 1
        rw [poleInverseVelocity, ite_eq_left hpactive, ← ENNReal.ofReal_mul (abs_nonneg _),
          mul_one_div_cancel hv.ne', ENNReal.ofReal_one]
      exact (withDensity_congr_ae hh).trans withDensity_one
    have hw : (stripGreen hH hLE hlam hLam A c.activeInterval ⊤
        ⟨e, WithTop.coe_lt_top _, he⟩).withDensity (fun p => ENNReal.ofReal |p.velocity 0|) =
        volume.withDensity (fun p => ENNReal.ofReal
          ((|c.vbar| * c.r ^ 2) * (c.r ^ 6)⁻¹ * F (c.map e p))) := by
      have hD : 0 ≤ |c.vbar| * c.r ^ 2 := mul_nonneg (abs_nonneg _) (sq_nonneg _)
      have hr : 0 ≤ (c.r ^ 6)⁻¹ := inv_nonneg.mpr (pow_nonneg c.positive.le _)
      have hmap : ((volume : Measure Point).withDensity (fun p => ENNReal.ofReal (F p))).map (c.inverse e) =
          ((volume : Measure Point).map (c.inverse e)).withDensity
            (fun p => ENNReal.ofReal (F (c.map e p))) := by
          apply Measure.ext
          intro S hS
          rw [Measure.map_apply (c.continuous_inverse e).measurable hS,
            withDensity_apply _ ((c.continuous_inverse e).measurable hS), withDensity_apply _ hS]
          have hm := setLIntegral_map (μ := (volume : Measure Point))
            (f := fun p => ENNReal.ofReal (F (c.map e p))) hS
            (hFm.comp (c.continuous_map e).measurable).ennreal_ofReal
            (c.continuous_inverse e).measurable
          refine (lintegral_congr (fun p => ?_)).trans hm.symm
          exact congrArg (fun q : Point => ENNReal.ofReal (F q)) (c.map_inverse e p).symm


      have hm := c.map_inverse_volume e
      have hfull : (stripGreen hH hLE hlam hLam A c.activeInterval ⊤
          ⟨e, WithTop.coe_lt_top _, he⟩).withDensity (fun p => ENNReal.ofReal |p.velocity 0|) =
          ENNReal.ofReal (|c.vbar| * c.r ^ 2) •
            (clockGreen hH hLE hlam hLam A c e he).map (c.inverse e) := by
          have h := congrArg (fun μ : Measure Point => μ.map (c.inverse e))
            (clock_green_pushforward hH hLE hlam hLam A c e he)
          have hi (μ : Measure Point) : (μ.map (c.map e)).map (c.inverse e) = μ := by
            rw [Measure.map_map (c.continuous_inverse e).measurable (c.continuous_map e).measurable]
            have heq : c.inverse e ∘ c.map e = id := funext (c.inverse_map e)
            rw [heq, Measure.map_id]
          exact (hi _).symm.trans (h.trans (Measure.map_smul _ (c.continuous_inverse
            e).measurable.aemeasurable))



      have heq := congrArg (fun μ : Measure Point =>
        ENNReal.ofReal (|c.vbar| * c.r ^ 2) • μ.map (c.inverse e)) hFd
      refine hfull.trans (heq.trans ?_)
      rw [hmap, hm, withDensity_smul_measure, smul_smul]
      have hx := withDensity_smul' (μ := (volume : Measure Point))
        (ENNReal.ofReal (|c.vbar| * c.r ^ 2) * ENNReal.ofReal ((c.r ^ 6)⁻¹))
        (fun p => ENNReal.ofReal (F (c.map e p)))
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      refine hx.symm.trans ?_
      apply congrArg (fun g : Point → ℝ≥0∞ => volume.withDensity g)
      funext p
      simp only [Pi.smul_apply, smul_eq_mul]
      exact ((ENNReal.ofReal_mul (mul_nonneg hD hr)).trans
        (congrArg (fun x : ℝ≥0∞ => x * ENNReal.ofReal (F (c.map e p)))
          (ENNReal.ofReal_mul hD))).symm
    have hm : Measurable (fun p => ENNReal.ofReal
        ((|c.vbar| * c.r ^ 2) * (c.r ^ 6)⁻¹ * F (c.map e p))) := (measurable_const.mul (hFm.comp
          (c.continuous_map e).measurable)).ennreal_ofReal
    have hp := withDensity_mul (volume : Measure Point) hm
      (poleInverseVelocity_measurable c).ennreal_ofReal
    have hg : ((fun p => ENNReal.ofReal
        ((|c.vbar| * c.r ^ 2) * (c.r ^ 6)⁻¹ * F (c.map e p))) *
        fun p => ENNReal.ofReal (poleInverseVelocity c p)) =
        fun p => ENNReal.ofReal (polePhysicalDensity c e F p) := by
      funext p
      exact (ENNReal.ofReal_mul (mul_nonneg (mul_nonneg
        (mul_nonneg (abs_nonneg _) (sq_nonneg _)) (inv_nonneg.mpr (pow_nonneg c.positive.le _)))
        (hFn _))).symm
    exact hi.symm.trans ((congrArg (fun ν : Measure Point => ν.withDensity
      (fun p => ENNReal.ofReal (poleInverseVelocity c p))) hw).trans
        (hp.symm.trans (congrArg (fun g : Point → ℝ≥0∞ => volume.withDensity g) hg)))
  exact ⟨polePhysicalDensity c e F, polePhysicalDensity_measurable c e F hFm,
    polePhysicalDensity_nonneg c e F hFn,
    _h_xinl_0,
    polePhysicalDensity_eLpNorm_bound c e F hFm hFn q C (by linarith) hC.le hFN,
    stripGreen_infinite_ae_future_carrier hH hLE hlam hLam A c.activeInterval
      ⟨e, WithTop.coe_lt_top _, he⟩⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
