module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGreenTestSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripBoundary

/-! # Genuine continuity and lateral traces of normalized clock tests -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution
open scoped Topology

variable (u : Point → ℝ) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (R T : ℝ) (hRT : R < T)
include hRT

/-- Past closed-strip continuity and an earlier zero half-space give full closed-strip
  continuity. -/
theorem clock_continuous_of_zero_after
    (hu : ContinuousOn u {p | p.time ≤ T ∧
      p.position ∈ closure (intervalDomain clockNormalizedInterval)})
    (hz : ∀ p, R ≤ p.time → u p = 0) :
    ContinuousOn u {p | p.position ∈ closure (intervalDomain clockNormalizedInterval)} := by
  intro p hp
  by_cases ht : p.time < T
  · apply (hu p ⟨ht.le, hp⟩).mono_of_mem_nhdsWithin
    have hn : ∀ᶠ q in 𝓝 p, q.time < T :=
      (isOpen_lt continuous_time continuous_const).mem_nhds ht
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hq hmem
    exact ⟨hq.le, hmem⟩
  · have hRp : R < p.time := hRT.trans_le (not_lt.mp ht)
    have hn : ∀ᶠ q in 𝓝 p, R < q.time :=
      (isOpen_lt continuous_const continuous_time).mem_nhds hRp
    have heq := hn.mono (fun q hq => hz q hq.le)
    exact (continuousAt_const.congr_of_eventuallyEq heq).continuousWithinAt

/-- The actual normalized test is continuous on the full closed velocity strip and zero on
both lateral faces; the boundary conclusions come from the genuine Duhamel theorem. -/
theorem clockSourcePotential_boundary
    (f : exitProbeSubmodule) (hfn : ∀ p, 0 ≤ exitProbePhysical f p)
    (hs : tsupport (exitProbePhysical f) ⊆
      {p | p.time < T ∧ p.velocity 0 ∈ clockNormalizedInterval.carrier})
    (hz : ∀ p, R ≤ p.time → exitProbePhysical f p = 0) :
    ContinuousOn (clockSourcePotential hlam hLam A c e T f)
      {p | p.position ∈ closure (intervalDomain clockNormalizedInterval)} ∧
    (∀ p, p.position 0 = -3 / 4 ∨ p.position 0 = 3 / 4 →
      clockSourcePotential hlam hLam A c e T f p = 0) := by
  let E := clockEvolution hlam hLam A c e
  have hsetting := c.extended_sourceSetting hlam hLam A e
  obtain ⟨hBs, hBsym, hBell⟩ := sectionTwoCoefficient_fullBounds (3 * lam / 5) (3 * Lam)
    (c.extendedCoefficient lam A.a e) hsetting.1
  obtain ⟨-, -, -, -, -, hc, -, hv, -⟩ :=
    kinetic_duhamel (by omega)
      (intervalDomain_admissible clockNormalizedInterval) (zeroCurve_piecewiseC1 1)
      (by positivity) (by linarith)
      (by norm_num)
      (zIndependentCoefficient (c.extendedCoefficient lam A.a e)) hBs hBsym hBell
      c.extendedVectorDrift hsetting.2.1 hsetting.2.2.2.2.1 E.1 E.2
      (clockEvolution_spec hlam hLam A c e) T
      (exitProbePhysical f ∘ sectionTwoPoint) (fun p => hfn _)
      (nested_native_probe_raw_smooth f)
      ((exitProbePhysical_continuous_compact f).2.comp_homeomorph (sectionTwoHomeomorph 1))
      (nested_native_probe_source_support clockNormalizedInterval T f hs)
  refine ⟨clock_continuous_of_zero_after _ R T hRT ?_ ((clockSourcePotential_regular hlam hLam A c e R T hRT f hfn hs hz).2.2.1), ?_⟩
  · apply hc.mono
    intro p hp
    refine ⟨hp.1, ?_⟩
    rw [mem_closure_movingDomain_iff, sub_zero]
    exact hp.2
  · intro p hp
    apply hv p
    rw [mem_frontier_movingDomain_iff, sub_zero]
    exact nested_intervalDomain_frontier_of_endpoint clockNormalizedInterval p.position hp

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
