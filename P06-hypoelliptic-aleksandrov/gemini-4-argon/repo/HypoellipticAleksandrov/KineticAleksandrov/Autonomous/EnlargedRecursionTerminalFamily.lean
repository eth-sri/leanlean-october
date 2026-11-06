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

/- Every actual terminal family has mass at most one, including zero-duration poles. -/
theorem enlarged_terminal_family_mass_le_one
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) (p : Point) :
    enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p univ ≤ 1 := by
  unfold enlargedActiveTerminalFamily
  split
  · simp only [Measure.dirac_apply_of_mem (mem_univ p), le_refl]
  · apply (Measure.restrict_le_self univ).trans
    change (if hp : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) b then
      finiteUnionExit hH hLE hlam hLam A (visitActiveUnion c J) b
        (enlargedVisitPole _ _ ⟨p, hp⟩) else 0) univ ≤ 1
    split
    · simp only [measure_univ, le_refl]
    · exact zero_le

/- Every actual terminal fiber is finite. -/
instance enlarged_terminal_family_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) (p : Point) :
    IsFiniteMeasure (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p) :=
  ⟨(enlarged_terminal_family_mass_le_one hH hLE hlam hLam A c J b p).trans_lt
    ENNReal.one_lt_top⟩

/- At a valid earlier active pole, terminal and earlier restart exits are disjoint submeasures. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
