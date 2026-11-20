module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionHorizonSplit
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassTerminal
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionFuture

/-! # The actual terminal family and its disjoint earlier exits -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory
open scoped Classical

/-- Every actual terminal family has mass at most one, including zero-duration poles. -/
theorem enlarged_terminal_family_mass_le_one
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) (p : Point) :
    enlargedActiveTerminalFamily hlam hLam A c J b p univ ≤ 1 := by
  unfold enlargedActiveTerminalFamily
  split
  · aesop
  · apply (Measure.restrict_le_self univ).trans
    change (if hp : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) b then
      finiteUnionExit hlam hLam A (visitActiveUnion c J) b
        (enlargedVisitPole _ _ ⟨p, hp⟩) else 0) univ ≤ 1
    split
    · simp
    positivity

/-- Every actual terminal fiber is finite. -/
instance enlarged_terminal_family_isFiniteMeasure
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) (p : Point) :
    IsFiniteMeasure (enlargedActiveTerminalFamily hlam hLam A c J b p) :=
  ⟨(enlarged_terminal_family_mass_le_one hlam hLam A c J b p).trans_lt
    ENNReal.one_lt_top⟩

/-- At a valid earlier active pole, terminal and earlier restart exits are disjoint submeasures. -/
theorem enlarged_terminal_and_early_exit_le
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b T : ℝ)
    (hJ : closure c.active ⊆ J.carrier) (p : Point) (hv : p.velocity 0 ∈ c.active)
    (hb : p.time < b) (hBT : b ≤ T)
    (B : Set Point) (hB : MeasurableSet B) (hsub : B ⊆ {q | q.time < b}) :
    enlargedActiveTerminalFamily hlam hLam A c J b p +
      (enlargedVisitExitKernel hlam hLam A (visitActiveUnion c J) T p).restrict B ≤
        enlargedVisitExitKernel hlam hLam A (visitActiveUnion c J) b p := by
  let H := c.activeInterval.toFiniteUnion
  have hp : p ∈ enlargedVisitPoleSet H b :=
    ⟨hb, by
      rw [Interval.toFiniteUnion_carrier _]
      aesop⟩
  unfold enlargedActiveTerminalFamily
  rw [enlarged_activeUnion_eq c J hJ]
  rw [ite_eq_right (fun h => (ne_of_lt hb) h.1)]
  change (if h : p ∈ enlargedVisitPoleSet H b then
    finiteUnionExit hlam hLam A H b (enlargedVisitPole H b ⟨p, h⟩)
      else 0).restrict {q | q.time = b} +
    (if h : p ∈ enlargedVisitPoleSet H T then
      finiteUnionExit hlam hLam A H T (enlargedVisitPole H T ⟨p, h⟩)
        else 0).restrict B ≤
      (if h : p ∈ enlargedVisitPoleSet H b then
        finiteUnionExit hlam hLam A H b (enlargedVisitPole H b ⟨p, h⟩) else 0)
  rw [dite_eq_left hp, dite_eq_left ⟨hb.trans_le hBT, hp.2⟩]
  exact enlarged_stripExit_cap_and_early_le hlam hLam A c.activeInterval ⟨p, WithTop.coe_lt_top _, (densityClockPole c p hv).2.2⟩ b T
    hb hBT B hB hsub

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
