module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionPointwise
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripMassInfinite
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripMass
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Continuous boundary values for the actual homogeneous reconstruction -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter
open SectionTwo TheoremA Evolution
open scoped Topology
open scoped ENNReal

/- The source potential is zero at every invalid open-strip pole. -/
theorem reconstruction_potential_zero_outside (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : ℝ)
    (g : BoundedBorel Point) (p ) (hp : p ∉ stripPast H T) :
    stripSourcePotential H K T g p = 0 := by
  by_cases ht : p.time < T
  · apply duhamelPotential_eq_zero_of_not_mem
    change p.velocity ∉ movingDomain (intervalDomain H) (fun _ => 0) p.time
    rw [movingDomain, PDE.mem_translateSet_iff_sub_mem, sub_zero, intervalDomain,
      PDE.mem_oneDimensionalAxisBox_iff]
    exact fun hv => hp ⟨ht, hv⟩
  · exact duhamelPotential_eq_zero_of_terminal_le K T (nativeStripSource g)
      (sectionTwoPoint p) (le_of_not_gt ht)

/- The time barrier extends continuously to all ambient points. -/
theorem reconstruction_potential_abs_le_time (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : ℝ)
    (g : BoundedBorel Point) (C : ℝ) (hC : 0 ≤ C) (hg : ∀ p, |g p| ≤ C) (p : Point) :
    |stripSourcePotential H K T g p| ≤ C * max (T - p.time) 0 := by
  by_cases hp : p ∈ stripPast H T
  · let e : StripPole H (T : WithTop ℝ) := ⟨p, WithTop.coe_lt_coe.mpr hp.1, hp.2⟩
    rw [stripSourcePotential_eq_green H K T g e,
      max_eq_left (sub_nonneg.mpr hp.1.le)]
    have hb := norm_integral_le_of_norm_le_const (f := (g : Point → ℝ))
      (μ := stripGreenOfKernel H K T e) (C := C)
      (Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hg p)
    have hm : (stripGreenOfKernel H K T e).real univ ≤ T - e.1.time := by
      have hT : 0 ≤ T - e.1.time := (sub_pos.mpr (WithTop.coe_lt_coe.mp e.2.1)).le
      simpa only [Measure.real, ENNReal.toReal_ofReal hT] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (stripGreenOfKernel_finite_time_mass H K T e)
    have hb' : |stripPotentialOfKernel H K T g e| ≤
        C * (stripGreenOfKernel H K T e).real univ := by
      simpa only [stripPotentialOfKernel, Real.norm_eq_abs] using hb
    exact hb'.trans (mul_le_mul_of_nonneg_left hm hC)
  · rw [reconstruction_potential_zero_outside H K T g p hp, abs_zero]
    exact mul_nonneg hC (le_max_right _ _)

/- The quadratic face barrier extends continuously to all ambient points. -/
theorem reconstruction_potential_abs_le_face
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ)
    (g : BoundedBorel Point) (C : ℝ) (hC : 0 ≤ C) (hg : ∀ p, |g p| ≤ C) (p : Point) :
    |stripSourcePotential H E.2 T g p| ≤
      C * max ((p.velocity 0 - H.lo) * (H.hi - p.velocity 0) / (2 * lam)) 0 := by
  by_cases hp : p ∈ stripPast H T
  · let e : StripPole H (T : WithTop ℝ) := ⟨p, WithTop.coe_lt_coe.mpr hp.1, hp.2⟩
    have hq : 0 ≤ (p.velocity 0 - H.lo) * (H.hi - p.velocity 0) / (2 * lam) :=
      div_nonneg (mul_nonneg (sub_nonneg.mpr hp.2.1.le) (sub_nonneg.mpr hp.2.2.le))
        (by positivity)
    rw [stripSourcePotential_eq_green H E.2 T g e, max_eq_left hq]
    let q := (e.1.velocity 0 - H.lo) * (H.hi - e.1.velocity 0) / (2 * lam)
    have hq : 0 ≤ q :=
      div_nonneg (mul_nonneg (sub_nonneg.mpr e.2.2.1.le) (sub_nonneg.mpr e.2.2.2.le))
        (by positivity)
    have hm : (stripGreenOfKernel H E.2 T e).real univ ≤ q := by
      have hmass := stripGreenOfRealization_quadratic_mass hH hlam hLam A H E hE T e
      change stripGreenOfKernel H E.2 T e univ ≤ ENNReal.ofReal q at hmass
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass).trans_eq
        (ENNReal.toReal_ofReal hq)
    have hb : |stripPotentialOfKernel H E.2 T g e| ≤
        C * (stripGreenOfKernel H E.2 T e).real univ := by
      simpa only [stripPotentialOfKernel, Real.norm_eq_abs] using
        norm_integral_le_of_norm_le_const (f := (g : Point → ℝ)) (C := C)
          (μ := stripGreenOfKernel H E.2 T e)
          (Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hg p)
    exact hb.trans (mul_le_mul_of_nonneg_left hm hC)
  · rw [reconstruction_potential_zero_outside H E.2 T g p hp, abs_zero]
    exact mul_nonneg hC (le_max_right _ _)

/- Bounded-source potentials are ambient continuous at the terminal face. -/
theorem reconstruction_candidate_continuousOn_exit
    (hH : HormanderHypoellipticityStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (sMinus T : ℝ) (phi : Point → ℝ)
    (hphi : Parabolic.IsKineticC112On phi (reconstructionStrip H sMinus T))
    (hc : ContinuousOn phi (reconstructionStrip H sMinus T ∪ reconstructionExit H sMinus T))
    (g : BoundedBorel Point)
    (hg : ∀ p ∈ reconstructionStrip H sMinus T, g p = -forwardScalarOperator A.a phi p) :
    ContinuousOn (stripReconstructionCandidate H E.2 T phi g)
      (reconstructionStrip H sMinus T ∪ reconstructionExit H sMinus T) := by
  apply hc.sub
  apply ContinuousOn.union_continuousAt (isOpen_reconstructionStrip H sMinus T)
    (reconstruction_source_potential_continuousOn hH hlam hLam A H E hE sMinus T g
      (reconstruction_source_continuousOn A H sMinus T phi hphi g hg))
  intro p hp
  rcases hp with ht | hv
  ·
    let K := E.2
    have hp := ht.1
    obtain ⟨C, hC, hg⟩ := g.exists_bound
    have hc : Continuous (fun q : Point => C * max (T - q.time) 0) :=
      continuous_const.mul ((continuous_const.sub continuous_time).max continuous_const)
    have hb : Tendsto (fun q : Point => C * max (T - q.time) 0) (𝓝 p) (𝓝 0) := by
      simpa only [hp, sub_self, max_self, mul_zero] using! (hc.continuousAt (x := p)).tendsto
    have ht := squeeze_zero_norm (f := stripSourcePotential H K T g)
      (fun q => by simpa only [Real.norm_eq_abs] using
        reconstruction_potential_abs_le_time H K T g C hC hg q) hb
    change Tendsto (stripSourcePotential H K T g) (𝓝 p)
      (𝓝 (stripSourcePotential H K T g p))
    rw [reconstruction_potential_zero_outside H K T g p
      (fun h => (by simpa only [hp] using h.1 : T < T).false)]
    exact ht
  ·
    have hp := hv.2.2
    obtain ⟨C, hC, hg⟩ := g.exists_bound
    have hv : Continuous (fun q : Point => q.velocity 0) :=
      (continuous_apply 0).comp continuous_velocity
    have hc : Continuous (fun q : Point => C *
        max ((q.velocity 0 - H.lo) * (H.hi - q.velocity 0) / (2 * lam)) 0) :=
      continuous_const.mul
      ((((hv.sub continuous_const).mul (continuous_const.sub hv)).div_const (2 * lam)).max
        continuous_const)
    have hb : Tendsto (fun q : Point => C *
        max ((q.velocity 0 - H.lo) * (H.hi - q.velocity 0) / (2 * lam)) 0)
        (𝓝 p) (𝓝 0) := by
      rcases hp with hp | hp <;>
        simpa only [hp, sub_self, zero_mul, mul_zero, zero_div, max_self] using!
          (hc.continuousAt (x := p)).tendsto
    have ht := squeeze_zero_norm (f := stripSourcePotential H E.2 T g)
      (fun q => by simpa only [Real.norm_eq_abs] using
        reconstruction_potential_abs_le_face hH hlam hLam A H E hE T g C hC hg q) hb
    change Tendsto (stripSourcePotential H E.2 T g) (𝓝 p)
      (𝓝 (stripSourcePotential H E.2 T g p))
    have hn : p ∉ stripPast H T := by
      intro h
      rcases hp with hp | hp
      · exact (lt_irrefl _ : ¬H.lo < H.lo) (hp ▸ h.2.1)
      · exact (lt_irrefl _ : ¬H.hi < H.hi) (hp ▸ h.2.2)
    rw [reconstruction_potential_zero_outside H E.2 T g p hn]
    exact ht

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
