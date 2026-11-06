module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ActiveTerminalDominationKernel

/-! # Finiteness and exact time support of the canonical terminal pieces -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory
open scoped Classical

/- Each actual terminal fiber is carried by the observation-time slice. -/
theorem enlarged_terminal_family_ae_time
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) (p : Point) :
    ∀ᵐ q ∂enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p, q.time = b := by
  unfold enlargedActiveTerminalFamily
  split
  · rename_i hp
    exact (ae_dirac_iff (isClosed_eq continuous_time continuous_const).measurableSet).mpr hp.1
  · exact ae_restrict_mem (isClosed_eq continuous_time continuous_const).measurableSet

/- Every finite sum of actual enlarged terminal pieces is finite. -/
instance enlargedActiveTerminal_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (N : ℕ) (b : ℝ) :
    IsFiniteMeasure (enlargedActiveTerminal hH hLE hlam hLam A c J s T P N b) := by
  change IsFiniteMeasure (∑ n ∈ Finset.range N,
    enlargedTerminalFamilyKernel hH hLE hlam hLam A c J b ∘ₘ
      enlargedVisitEntrance hH hLE hlam hLam A c J s T P n)
  infer_instance

/- The actual finite terminal sum retains its literal observation time. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
