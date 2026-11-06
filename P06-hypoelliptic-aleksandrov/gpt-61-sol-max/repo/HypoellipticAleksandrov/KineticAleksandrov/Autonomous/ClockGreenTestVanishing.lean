module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGreenTestEvolution
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelTheorem
public import PDEFoundation.Calculus.RegularityOrder


/-! # Literal late-time vanishing of actual compact-source Duhamel potentials -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory
open SectionTwo Evolution
open scoped Topology

/-- A source vanishing after a time has an actual Duhamel potential vanishing after that time. -/
theorem clock_duhamel_zero_after {Ω : PDE.VelocityRegion 1} {γ : ℝ → PDE.Vec 1}
    (K : MovingFiberKernel Ω γ) (T R : ℝ) (g : Point → ℝ)
    (hg : ∀ p, R ≤ p.time → g p = 0) (p : Point) (hp : R ≤ p.time) :
    duhamelPotential K T g p = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro r hr
  unfold duhamelIntegrand
  split
  · unfold duhamelSourceIntegral
    have hz : (fun w : EvolutionAmbientState 1 => g ⟨r, w.1, w.2⟩) = 0 := by
      funext w
      exact hg _ (hp.trans hr.1.le)
    rw [hz]
    exact integral_zero' _ _
  · rfl

/-- Smoothness below a terminal time and exact vanishing on an earlier half-space imply
smoothness throughout the native open velocity strip. -/
theorem clock_native_smooth_of_zero_after (u : Point → ℝ) (R T : ℝ) (hRT : R < T)
    (hu : ContDiffOn ℝ PDE.smoothOrder (u ∘ evolutionHomeomorph 1)
      (evolutionHomeomorph 1 ⁻¹'
        evolutionPastOpenCylinder (intervalDomain clockNormalizedInterval) (fun _ => 0) T))
    (hz : ∀ p, R ≤ p.time → u p = 0) :
    ContDiffOn ℝ PDE.smoothOrder (u ∘ evolutionHomeomorph 1)
      {x : EvolutionVec 1 | (evolutionHomeomorph 1 x).position ∈
        intervalDomain clockNormalizedInterval} := by
  intro x hx
  by_cases ht : (evolutionHomeomorph 1 x).time < T
  · have hmem : evolutionHomeomorph 1 x ∈
        evolutionPastOpenCylinder (intervalDomain clockNormalizedInterval) (fun _ => 0) T := by
      refine ⟨ht, ?_⟩
      rw [mem_movingDomain_iff, sub_zero]
      exact hx
    have hD := isOpen_duhamelCylinder
      (isOpen_of_isAdmissibleEvolutionDomain (intervalDomain_admissible clockNormalizedInterval))
      (show Continuous (fun _ : ℝ => (0 : PDE.Vec 1)) from continuous_const) T
    exact ((hu x hmem).contDiffAt
      ((hD.preimage (evolutionHomeomorph 1).continuous).mem_nhds hmem)).contDiffWithinAt
  ·
    have hn : ∀ᶠ y in 𝓝 x, R < (evolutionHomeomorph 1 y).time :=
      (isOpen_lt continuous_const (continuous_time.comp (evolutionHomeomorph
        1).continuous)).mem_nhds
        (hRT.trans_le (not_lt.mp ht))

    exact (contDiffAt_const.congr_of_eventuallyEq (hn.mono (fun y hy => hz _ hy.le))).contDiffWithinAt

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
