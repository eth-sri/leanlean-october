module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelSlice
import HypoellipticAleksandrov.Analysis.DuhamelPairing

/-! # Continuous zero traces for the kinetic Duhamel potential -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Filter
open scoped Topology
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

theorem exists_duhamelIntegrand_bound (K : MovingFiberKernel Ω γ) (g : KineticPoint d → ℝ)
    (hgn : ∀ p, 0 ≤ g p) (hg : Continuous g) (hgc : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p r, |duhamelIntegrand K g p r| ≤ C := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  have hgb (p : KineticPoint d) : g p ≤ C := (le_abs_self _).trans (by simpa using hC p)
  have hC0 := (hgn ⟨0, 0, 0⟩).trans (hgb _)
  refine ⟨C, hC0, fun p r => ?_⟩
  rw [abs_of_nonneg (duhamelIntegrand_nonneg K g hgn p r)]
  exact duhamelIntegrand_le K g hgn C hC0 hgb p r

section
variable (hΩa : IsAdmissibleEvolutionDomain Ω) (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
  (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d) (S : TerminalOperatorFamily Ω γ)
  (K : MovingFiberKernel Ω γ) (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
  (g : KineticPoint d → ℝ) (hgn : ∀ p, 0 ≤ g p) (hg : Continuous g) (hgc : HasCompactSupport g)
  (hgs : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d => g ⟨q.1, q.2.1, q.2.2⟩)) (T : ℝ)
  (hgU : tsupport g ⊆ evolutionPastOpenCylinder Ω γ T)
include hΩa hΩ hγ B b S hreal hgn hg hgc hgs hgU

/-- Dominated convergence gives continuity of the kinetic potential up to the past boundary. -/
theorem continuousWithinAt_duhamelPotential
    (p₀ : KineticPoint d) (hp₀ : p₀ ∈ evolutionPastClosedCylinder Ω γ T) :
    ContinuousWithinAt (duhamelPotential K T g)
      (evolutionPastClosedCylinder Ω γ T) p₀ := by
  obtain ⟨a, btime, -, hab⟩ := exists_time_window_of_hasCompactSupport g hgc
  obtain ⟨C, hC, hb⟩ := exists_duhamelIntegrand_bound K g hgn hg hgc
  have hmeas := measurable_duhamelIntegrand K hΩ hγ g hg.measurable
  refine Analysis.continuousWithinAt_integral_Ioc continuous_time
    (fun p => hmeas.comp (measurable_const.prodMk measurable_id)) hC hb
    (duhamelIntegrand_eq_zero_of_time_not_mem K g a btime hab) ?_
  intro r h _
  have hc := continuousOn_duhamelIntegrand hΩa hΩ B b S K hreal g hg hgc hgs T hgU r
  exact (hc p₀ ⟨h.le, hp₀.2⟩).mono_of_mem_nhdsWithin <|
    mem_nhdsWithin.2 ⟨{p | p.time < r}, isOpen_lt continuous_time continuous_const, h,
      fun p hp => ⟨hp.1.le, hp.2.2⟩⟩

/-- The kinetic Duhamel potential is continuous on the entire closed past cylinder. -/
theorem continuousOn_duhamelPotential :
    ContinuousOn (duhamelPotential K T g) (evolutionPastClosedCylinder Ω γ T) :=
  fun p hp => continuousWithinAt_duhamelPotential hΩa hΩ hγ B b S K hreal
    g hgn hg hgc hgs T hgU p hp

end

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
