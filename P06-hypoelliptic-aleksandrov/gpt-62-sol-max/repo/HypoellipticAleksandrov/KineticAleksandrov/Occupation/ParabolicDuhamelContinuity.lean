module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSlice
import HypoellipticAleksandrov.Analysis.DuhamelPairing

/-!
# Continuity of the parabolic Duhamel potential and its traces

Each source slice integrand `p ↦ integrand p r` is continuous on the closed cylinder at time `r`
(it is the classical solution `V_r`), vanishes on the lateral frontier, and equals `g(r,·)` on
the terminal face.  Dominated convergence in the source time `r` then gives continuity of the
potential on the closed region `{s ≤ T, v ∈ closure Ω_s}`, hence the continuous zero terminal
and lateral traces, without any barrier estimate.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set Filter
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open scoped ENNReal ProbabilityTheory Topology

variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
variable (K : MovingFiberKernel Ω γ)

/-- On the closed cylinder the integrand is the classical slice solution. -/
theorem integrand_eq_slice_solution (hΩa : IsAdmissibleEvolutionDomain Ω)
    (hΩ : MeasurableSet Ω) (g : TimeVelocity d → ℝ) (r : ℝ) (V : TimeVelocity d → ℝ)
    (hlat : ∀ p ∈ ParabolicProbe.scalarLateralFrontier Ω γ r, V p = 0)
    (hV : ∀ (s : ℝ) (hsr : s ≤ r) (y : EvolutionPosition Ω γ s),
      V (s, y.1) = parabolicSourceIntegral K hΩ g s r hsr y)
    (p : TimeVelocity d) (hp : p ∈ sliceClosedCylinder Ω γ r) :
    parabolicDuhamelIntegrand K hΩ g p r = V p := by
  by_cases hmem : p.2 ∈ movingDomain Ω γ p.1
  · rw [parabolicDuhamelIntegrand_of_valid K hΩ g p r ⟨hp.1, hmem⟩]
    exact (hV p.1 hp.1 ⟨p.2, hmem⟩).symm
  · rw [parabolicDuhamelIntegrand_of_not_valid K hΩ g p r (fun h => hmem h.2)]
    have hfr : p.2 ∈ frontier (movingDomain Ω γ p.1) := by
      rw [(isOpen_movingDomain_of_isAdmissibleEvolutionDomain γ hΩa p.1).frontier_eq]
      exact ⟨hp.2, hmem⟩
    exact (hlat p ⟨hp.1, hfr⟩).symm

/-- The slice integrand is continuous on the closed cylinder, and equals the classical
solution there, which is smooth in the open cylinder and has the stated trace data. -/
theorem slice_regularity {B : CoefficientField d} (hΩa : IsAdmissibleEvolutionDomain Ω)
    (hP : SectionTwo.HasParabolicMarginalBundle Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩa) (zIndependentCoefficient B) K)
    (g : TimeVelocity d → ℝ) (hgs : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) (T : ℝ)
    (hgU : tsupport g ⊆ duhamelFiber Ω γ T) (r : ℝ) :
    ∃ V : TimeVelocity d → ℝ,
      (∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ sliceClosedCylinder Ω γ r, |V p| ≤ C) ∧
      ContinuousOn V (sliceClosedCylinder Ω γ r) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) V (sliceOpenCylinder Ω γ r) ∧
      (∀ p ∈ sliceOpenCylinder Ω γ r,
        scalarParabolicOperator B (fun _ _ => 0) V p = 0) ∧
      (∀ v ∈ closure (movingDomain Ω γ r), V (r, v) = g (r, v)) ∧
      ∀ p ∈ sliceClosedCylinder Ω γ r,
        parabolicDuhamelIntegrand K (measurableSet_of_isAdmissibleEvolutionDomain hΩa) g p r
          = V p := by
  obtain ⟨V, ⟨hbd, hcont, hsm, heq, hterm, hlat⟩, hVs⟩ :=
    exists_slice_solution K (measurableSet_of_isAdmissibleEvolutionDomain hΩa) hP g hgs hgc T
      hgU r
  refine ⟨V, hbd, hcont, hsm, heq, fun v hv => ?_,
    integrand_eq_slice_solution K hΩa _ g r V hlat hVs⟩
  exact hterm (r, v) ⟨rfl, hv⟩

/-- A compactly supported source vanishes at all times outside a bounded interval. -/
theorem exists_time_range (g : TimeVelocity d → ℝ) (hgc : HasCompactSupport g) :
    ∃ a b : ℝ, ∀ r, r ∉ Icc a b → ∀ v, g (r, v) = 0 := by
  have hK := hgc.image continuous_fst
  obtain ⟨b, hb⟩ := hK.bddAbove
  obtain ⟨a, ha⟩ := hK.bddBelow
  refine ⟨a, b, fun r hr v => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  exact hr ⟨ha ⟨_, hmem, rfl⟩, hb ⟨_, hmem, rfl⟩⟩

theorem exists_parabolicDuhamelIntegrand_bound (K : MovingFiberKernel Ω γ)
    (hΩ : MeasurableSet Ω) (g : TimeVelocity d → ℝ)
    (hgn : ∀ p, 0 ≤ g p) (hg : Continuous g) (hgc : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p r, |parabolicDuhamelIntegrand K hΩ g p r| ≤ C := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  have hgb (p : TimeVelocity d) : g p ≤ C := (le_abs_self _).trans (by simpa using hC p)
  have hgm (r : ℝ) : Measurable (fun v => g (r, v)) := hg.measurable.comp (measurable_const.prodMk measurable_id)
  refine ⟨C, (hgn (0, 0)).trans (hgb _), fun p r => ?_⟩
  rw [abs_of_nonneg (parabolicDuhamelIntegrand_nonneg K hΩ g hgm hgn p r)]
  exact parabolicDuhamelIntegrand_le K hΩ g hgm hgn C hgb p r

section
variable {B : CoefficientField d} (hΩa : IsAdmissibleEvolutionDomain Ω) (hγ : Continuous γ)
  (hP : SectionTwo.HasParabolicMarginalBundle Ω γ (measurableSet_of_isAdmissibleEvolutionDomain hΩa) (zIndependentCoefficient B) K)
  (g : TimeVelocity d → ℝ) (hgn : ∀ p, 0 ≤ g p) (hgs : ContDiff ℝ (⊤ : ℕ∞) g)
  (hgc : HasCompactSupport g) (T : ℝ) (hgU : tsupport g ⊆ duhamelFiber Ω γ T)
include B hγ hP hgn hgs hgc hgU

/-- **Continuity of the Duhamel potential** on the closed region
`{s ≤ T, v ∈ closure Ω_s}`, by dominated convergence in the source time. -/
theorem continuousWithinAt_duhamelPotential
    (p₀ : TimeVelocity d) (hp₀ : p₀ ∈ duhamelClosedFiber Ω γ T) :
    ContinuousWithinAt
      (parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩa) T g)
      (duhamelClosedFiber Ω γ T) p₀ := by
  have hΩ := measurableSet_of_isAdmissibleEvolutionDomain hΩa
  obtain ⟨a, b, hab⟩ := exists_time_range g hgc
  obtain ⟨C, hC, hb⟩ := exists_parabolicDuhamelIntegrand_bound K hΩ g hgn hgs.continuous hgc
  have hg (r : ℝ) : Measurable (fun v => g (r, v)) := hgs.continuous.measurable.comp (measurable_const.prodMk measurable_id)
  have hmeas := measurable_parabolicDuhamelIntegrand K hΩ hγ g hgs.continuous.measurable
  refine Analysis.continuousWithinAt_integral_Ioc continuous_fst
    (fun p => hmeas.comp (measurable_const.prodMk measurable_id)) hC hb
    (fun p r hr => parabolicDuhamelIntegrand_eq_zero_of_slice K hΩ g hg p r (hab r hr)) ?_
  intro r h _
  obtain ⟨V, -, hVc, -, -, -, hVeq⟩ := slice_regularity K hΩa hP g hgs hgc T hgU r
  have hc := hVc.congr (fun p hp => hVeq p hp)
  exact (hc p₀ ⟨h.le, hp₀.2⟩).mono_of_mem_nhdsWithin <|
    mem_nhdsWithin.2 ⟨{p | p.1 < r}, isOpen_lt continuous_fst continuous_const, h,
      fun p hp => ⟨hp.1.le, hp.2.2⟩⟩

/-- Continuity of the Duhamel potential on the closed region. -/
theorem continuousOn_duhamelPotential :
    ContinuousOn
      (parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩa) T g)
      (duhamelClosedFiber Ω γ T) :=
  fun p₀ hp₀ => continuousWithinAt_duhamelPotential K hΩa hγ hP g hgn hgs hgc T hgU p₀ hp₀

end

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
