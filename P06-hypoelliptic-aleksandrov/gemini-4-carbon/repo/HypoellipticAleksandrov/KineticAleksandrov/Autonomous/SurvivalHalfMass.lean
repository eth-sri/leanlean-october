module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SurvivalKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripMassInfinite
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforwardCone

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo
open scoped ENNReal

/-- Twice the uniform quadratic occupation time of the clock's active interval. -/
def activeHalfMassTime (lam : ℝ) (c : Clock) : ℝ := 9 * c.r ^ 2 / (16 * lam)

/-- Positive ellipticity and radius give a strictly positive half-mass time. -/
theorem activeHalfMassTime_pos {lam : ℝ} (hlam : 0 < lam) (c : Clock) :
    0 < activeHalfMassTime lam c := by
  unfold activeHalfMassTime
  have hr := c.positive
  positivity

/-- Every active pole has the same uniform upper bound on quadratic occupation. -/
theorem active_quadratic_occupation_le {lam : ℝ} (hlam : 0 < lam) (c : Clock)
    (v : ℝ) :
    (v - c.activeInterval.lo) * (c.activeInterval.hi - v) / (2 * lam) ≤
      activeHalfMassTime lam c / 2 := by
  apply (div_le_iff₀ (by positivity : 0 < 2 * lam)).mpr
  have he : activeHalfMassTime lam c / 2 * (2 * lam) = 9 * c.r ^ 2 / 16 := by
    unfold activeHalfMassTime
    field_simp
  rw [he]
  change (v - (c.vbar - 3 * c.r / 4)) * (c.vbar + 3 * c.r / 4 - v) ≤ _
  nlinarith only [sq_nonneg (v - c.vbar)]

/-- The actual killed kernel has lost at least half its mass at this common elapsed time. -/
theorem active_survival_half_mass
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (s : ℝ)
    (z : EvolutionState (intervalDomain c.activeInterval) (fun _ => 0) s) :
    let D := activeHalfMassTime lam c
    stripSurvivingMass c.activeInterval (stripEvolution hH hLE hlam hLam A c.activeInterval)
      s (s + D) (le_add_of_nonneg_right (activeHalfMassTime_pos hlam c).le) z ≤ 1 / 2  := by
  have stripSurvivingMass_mul_time_le_green (H : Interval) (E : StripEvolution H) (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
      ENNReal.ofReal (T - e.1.time) *
      ENNReal.ofReal (stripSurvivingMass H E e.1.time T
        (WithTop.coe_lt_coe.mp e.2.1).le (stripPoleState H T e)) ≤
      stripGreenOfKernel H E.2 T e univ := by
    let dt := T - e.1.time
    have hdt := sub_pos.mpr (WithTop.coe_lt_coe.mp e.2.1)
    let z := stripPoleState H T e
    let m := stripSurvivingMass H E e.1.time T (WithTop.coe_lt_coe.mp e.2.1).le z
    have hact := stripGreenOfKernel_spec H E.2 T e (fun _ => 1) measurable_const
    simp at hact
    rw [hact]
    have hc : ENNReal.ofReal dt * ENNReal.ofReal m =
        ∫⁻ _tau : ElapsedTime (ENNReal.ofReal dt), ENNReal.ofReal m
          ∂elapsedVolume (ENNReal.ofReal dt) := by
      rw [lintegral_const, elapsedVolume_univ dt hdt, mul_comm]
    rw [hc]
    apply lintegral_mono
    intro tau
    have htau := (ENNReal.ofReal_lt_ofReal_iff hdt).mp tau.2.2
    have hst : e.1.time ≤ e.1.time + tau.1 := le_add_of_nonneg_right tau.2.1.le
    have htu : e.1.time + tau.1 ≤ T := by dsimp [dt] at htau; linarith
    have hm := stripSurvivingMass_antitone A H E hE e.1.time
      (e.1.time + tau.1) T hst htu z
    have hun := congrArg (fun mu => mu univ) (E.2.map_fiberKernel_eq_master (intervalDomain_measurable H) e.1.time (e.1.time + tau.1) hst z)
    rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, preimage_univ] at hun
    apply (ENNReal.ofReal_le_ofReal hm).trans
    rw [(stripSurvivingMass_eq_kernel_mass A H E hE e.1.time (e.1.time + tau.1) hst z), ENNReal.ofReal_toReal
      ((E.2.fiberKernel_mass_le_one (intervalDomain_measurable H)
        e.1.time (e.1.time + tau.1) hst z).trans_lt ENNReal.one_lt_top).ne]
    exact hun.le
  let D := activeHalfMassTime lam c
  have hD := activeHalfMassTime_pos hlam c
  let E := stripEvolution hH hLE hlam hLam A c.activeInterval
  have hE := stripEvolution_spec hH hLE hlam hLam A c.activeInterval
  let p : Point := ⟨s, z.1.2, z.1.1⟩
  have hv : p.velocity 0 ∈ c.activeInterval.carrier := by
    have hh := z.2.1
    apply PDE.mem_translateSet_iff_sub_mem.mp at hh
    simpa [p, intervalDomain, PDE.mem_oneDimensionalAxisBox_iff, PDE.vecOneCoordinate, Interval.carrier] using hh
  let e : StripPole c.activeInterval ((s + D : ℝ) : WithTop ℝ) :=
    ⟨p, WithTop.coe_lt_coe.mpr (lt_add_of_pos_right s hD), hv⟩
  have hz : stripPoleState c.activeInterval (s + D) e = z := Subtype.ext rfl
  have hb := (stripSurvivingMass_mul_time_le_green c.activeInterval E hE (s + D) e).trans ((stripGreen_finite_quadratic_mass hH hLE hlam hLam A c.activeInterval (s + D) e).trans
    (ENNReal.ofReal_le_ofReal (active_quadratic_occupation_le hlam c (p.velocity 0))))
  change ENNReal.ofReal ((s + D) - s) *
      ENNReal.ofReal (stripSurvivingMass c.activeInterval E s (s + D) _
        (stripPoleState c.activeInterval (s + D) e)) ≤ ENNReal.ofReal (D / 2) at hb
  rw [hz, add_sub_cancel_left] at hb
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hD.le,
    ENNReal.toReal_ofReal ((stripSurvivingMass_bounds A c.activeInterval E hE s (s + D) (le_add_of_nonneg_right hD.le) z).1), ENNReal.toReal_ofReal (by positivity)] at hr
  nlinarith only [hr, hD]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

