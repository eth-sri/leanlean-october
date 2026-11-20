module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalSetting
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PushforwardStatement

/-! # Canonical visits in an enlarged bounded velocity strip

Source: companion paper, Lemma 8.6 and its proof. Unlike the cylinder-specific count,
the outer interval is an independent argument. Initial poles at time zero
are retained, as required by the initial atom of the entrance count.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov
open scoped Classical

section
variable (H : FiniteIntervalUnion) (T : ℝ)
include H T

/-- Valid physical poles before a finite horizon, including the initial time. -/
def enlargedVisitPoleSet : Set Point :=
  {p | p.time < T ∧ p.velocity 0 ∈ H.carrier}

/-- The enlarged visit pole carrier is measurable. -/
theorem measurableSet_enlargedVisitPoleSet :
    MeasurableSet (enlargedVisitPoleSet H T) :=
  (isOpen_lt continuous_time continuous_const).measurableSet.inter
    (H.isOpen_carrier.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)

/-- Physical poles enter the canonical finite-union pole carrier. -/
def enlargedVisitPole
    (p : enlargedVisitPoleSet H T) : FiniteUnionPole H (T : WithTop ℝ) :=
  ⟨p.1, WithTop.coe_lt_coe.mpr p.2.1, p.2.2⟩

/-- The physical pole inclusion is measurable. -/
theorem measurable_enlargedVisitPole :
    Measurable (enlargedVisitPole H T) := measurable_subtype_coe.subtype_mk

end

/-- Zero extension from the enlarged and clipped carriers agrees on measures after the cutoff. -/
theorem visitExtendKernel_comp_eq_clipped (H : FiniteIntervalUnion) (s T : ℝ)
    (f : FiniteUnionPole H (T : WithTop ℝ) → Measure Point) (hf : Measurable f)
    (mu : Measure Point) (hs : ∀ᵐ p ∂mu, s ≤ p.time) :
    visitExtendKernel _ (measurableSet_enlargedVisitPoleSet H T) (f ∘ enlargedVisitPole H T)
        (hf.comp (measurable_enlargedVisitPole H T)) ∘ₘ mu =
      visitExtendKernel _ (measurableSet_visitPoleSet H (s - 1) T) (f ∘ visitPoleInclusion H (s - 1) T)
        (hf.comp (measurable_visitPoleInclusion H (s - 1) T)) ∘ₘ mu := by
  apply Measure.comp_congr
  filter_upwards [hs] with p hp
  have he : p ∈ enlargedVisitPoleSet H T ↔ p ∈ visitPoleSet H (s - 1) T :=
    ⟨fun h => ⟨by linarith, h⟩, fun h => h.2⟩
  by_cases h : p ∈ enlargedVisitPoleSet H T
  · rw [visitExtendKernel_apply_mem h, visitExtendKernel_apply_mem (he.mp h)]
    rfl
  · rw [visitExtendKernel_apply_notMem h, visitExtendKernel_apply_notMem (mt he.mpr h)]

/-- Canonical exit kernel extended by zero only outside its valid pole carrier. -/
def enlargedVisitExitKernel
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : ℝ) :
    Kernel Point Point :=
  visitExtendKernel (enlargedVisitPoleSet H T) (measurableSet_enlargedVisitPoleSet H T)
    (fun p => finiteUnionExit A H T (enlargedVisitPole H T p))
    ((finiteUnionExit_measurable A H T).comp
      (measurable_enlargedVisitPole H T))

/-- Every enlarged exit kernel has mass at most one. -/
instance enlargedVisitExitKernel_isFiniteKernel
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : ℝ) :
    IsFiniteKernel (enlargedVisitExitKernel A H T) := by
  refine ⟨1, by simp only [ENNReal.one_lt_top], ?_⟩
  intro p
  change (if hp : p ∈ enlargedVisitPoleSet H T then
    finiteUnionExit A H T (enlargedVisitPole H T ⟨p, hp⟩)
    else 0) univ ≤ 1
  split
  · simp
  · exact zero_le

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
  (P : Point)
include lam Lam A c J s T P

/-- Entrance number `n+1` in the literal enlarged-strip alternating recursion. -/
def enlargedVisitEntrance (n : ℕ) : Measure Point :=
  visitGamma P (visitEntranceInterval c)
    (visitBoundary s T (visitEntranceInterval c) J)
    (visitBoundary s T (visitActiveInterval c) J)
    (enlargedVisitExitKernel A (visitActiveUnion c J) T)
    (enlargedVisitExitKernel A (visitWaitingUnion c J) T) n

/-- The enlarged-strip counting measure, including the initial atom exactly once. -/
def enlargedVisitStarts : Measure Point :=
  Measure.sum (enlargedVisitEntrance A c J s T P)

end

/-- Each individual entrance is finite; finiteness of the full sum is a separate estimate. -/
instance enlargedVisitEntrance_isFiniteMeasure
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (n : ℕ) :
    IsFiniteMeasure (enlargedVisitEntrance A c J s T P n) := by
  unfold enlargedVisitEntrance
  infer_instance

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock)
include lam Lam A c

/-- A canonical all-time Green kernel on the active interval. -/
def enlargedActiveGreenKernel : Kernel Point Point :=
  visitExtendKernel {p | p.velocity 0 ∈ c.active}
    (isOpen_Ioo.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)
    (fun p => stripGreen A c.activeInterval ⊤
      (densityClockPole c p.1 p.2))
    ((Measure.measurable_measure.mpr
      (stripGreen_measurable_apply A c.activeInterval ⊤)).comp
      (show Measurable (fun p : {p : Point | p.velocity 0 ∈ c.active} =>
        densityClockPole c p.1 p.2) from measurable_subtype_coe.subtype_mk))

/-- Integrate the actual all-time active Green family against physical starting points. -/
def enlargedActiveGreen (nu : Measure Point) : Measure Point :=
  enlargedActiveGreenKernel A c ∘ₘ nu

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
