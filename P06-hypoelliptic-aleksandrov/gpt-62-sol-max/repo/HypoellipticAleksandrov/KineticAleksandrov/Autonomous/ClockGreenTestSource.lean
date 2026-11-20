module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGreenTestGerm
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripDuhamel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripSource

/-! # Actual normalized clock source potentials and their global strip equation -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution
open scoped Topology

/-- The clock test is the genuine normalized killed Duhamel potential. -/
def clockSourcePotential
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (T : ℝ)
    (f : exitProbeSubmodule) : Point → ℝ :=
  duhamelPotential (clockEvolution A c e).2 T
    (exitProbePhysical f ∘ sectionTwoPoint)

/-- Past closed-strip continuity and an earlier zero half-space give full closed-strip
  continuity. -/
theorem clock_continuous_of_zero_after (u : Point → ℝ) (R T : ℝ) (hRT : R < T)
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
    have heq : u =ᶠ[𝓝 p] (fun _ => (0 : ℝ)) := hn.mono (fun q hq => hz q hq.le)
    exact (continuousAt_const.congr_of_eventuallyEq heq).continuousWithinAt

/-- The interior equation, regularity, and boundary traces of one normalized clock potential. -/
structure ClockSourcePotentialSpec {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock)
    (e : Point) (R T : ℝ) (f : exitProbeSubmodule) : Prop where
  bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ p, |clockSourcePotential A c e T f p| ≤ C
  smooth : ContDiffOn ℝ (⊤ : ℕ∞)
    ((clockSourcePotential A c e T f ∘ sectionTwoPoint) ∘ scalarPoint)
    {q : Fin 3 → ℝ | q 2 ∈ normalizedActive}
  zero_after : ∀ p, R ≤ p.time → clockSourcePotential A c e T f p = 0
  equation : ∀ p, p.position ∈ intervalDomain clockNormalizedInterval →
    transportedForwardOperator (zIndependentCoefficient (c.extendedCoefficient lam A.a e))
      c.extendedVectorDrift (clockSourcePotential A c e T f) p =
        -exitProbePhysical f (sectionTwoPoint p)
  continuous_closed : ContinuousOn (clockSourcePotential A c e T f)
    {p | p.position ∈ closure (intervalDomain clockNormalizedInterval)}
  lateral_zero : ∀ p, p.position 0 = -3 / 4 ∨ p.position 0 = 3 / 4 →
    clockSourcePotential A c e T f p = 0

/-- The actual clock test is bounded, smooth on the whole normalized strip, vanishes late,
and solves the literal extended transported equation there. -/
theorem clockSourcePotential_regular
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (R T : ℝ) (hRT : R < T)
    (f : exitProbeSubmodule) (hfn : ∀ p, 0 ≤ exitProbePhysical f p)
    (hs : tsupport (exitProbePhysical f) ⊆
      {p | p.time < T ∧ p.velocity 0 ∈ clockNormalizedInterval.carrier})
    (hz : ∀ p, R ≤ p.time → exitProbePhysical f p = 0) :
    ClockSourcePotentialSpec A c e R T f := by
  let E := clockEvolution A c e
  have hsetting := c.extended_sourceSetting A e
  obtain ⟨hBs, hBsym, hBell⟩ := sectionTwoCoefficient_fullBounds (3 * lam / 5) (3 * Lam)
    (c.extendedCoefficient lam A.a e) hsetting.1
  have hgc := (exitProbePhysical_continuous_compact f).2.comp_homeomorph
    (sectionTwoHomeomorph 1)
  obtain ⟨⟨-, C, hC, hb⟩, -, hsm, -, hop, hc, -, hv, -⟩ :=
    kinetic_duhamel
      (intervalDomain_admissible clockNormalizedInterval) (zeroCurve_piecewiseC1 1)
      (by linarith [A.positive] : 0 < 3 * lam / 5)
      
      (by norm_num : (0 : ℝ) < 9 / 25)
      (zIndependentCoefficient (c.extendedCoefficient lam A.a e)) hBs hBsym hBell
      c.extendedVectorDrift hsetting.2.1 hsetting.2.2.2.2.1 E.1 E.2
      (clockEvolution_spec A c e) T
      (exitProbePhysical f ∘ sectionTwoPoint) (fun p => hfn _)
      (nested_native_probe_raw_smooth f) hgc
      (nested_native_probe_source_support clockNormalizedInterval T f hs)
  have hzero : ∀ p, R ≤ p.time → duhamelPotential E.2 T
      (exitProbePhysical f ∘ sectionTwoPoint) p = 0 := by
    intro p hp
    exact clock_duhamel_zero_after E.2 T R (exitProbePhysical f ∘ sectionTwoPoint)
      (fun q hq => hz (sectionTwoPoint q) hq) p hp
  refine ⟨⟨C, hC, hb⟩,
    clock_native_smooth_to_scalar _
      (clock_native_smooth_of_zero_after _ R T hRT hsm hzero), hzero, ?_,
      clock_continuous_of_zero_after _ R T hRT ?_ hzero, ?_⟩
  · intro p hp
    by_cases ht : p.time < T
    · exact hop p ⟨ht, mem_movingDomain_iff.mpr (by simpa using hp)⟩
    · have hRp : R < p.time := hRT.trans_le (not_lt.mp ht)
      exact (clock_transport_operator_zero_after _ _ _ R hzero p hRp).trans
        (by rw [hz (sectionTwoPoint p) hRp.le]; simp)
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
