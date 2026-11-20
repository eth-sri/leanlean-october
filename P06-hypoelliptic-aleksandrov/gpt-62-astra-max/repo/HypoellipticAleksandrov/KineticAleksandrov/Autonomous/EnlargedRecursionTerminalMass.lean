module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionDomination
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassTerminal

/-! # The finite enlarged terminal mass at its observation horizon -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- The sum of active terminal masses at the recursion horizon is at most one. -/
theorem enlarged_active_terminal_mass_le_one
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (hP : s ≤ P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier)
    (hJ : closure c.active ⊆ J.carrier) (N : ℕ) :
    enlargedActiveTerminal hlam hLam A c J s T P N T univ ≤ 1 := by
  let gamma := enlargedVisitEntrance hlam hLam A c J s T P
  have hpiece (n : ℕ) :
      (gamma n).bind (enlargedActiveTerminalFamily hlam hLam A c J T) ≤
        ((enlargedVisitExitKernel hlam hLam A (visitActiveUnion c J) T) ∘ₘ gamma n).restrict (finiteUnionExitSet J.toFiniteUnion s T) := by
    rw [enlargedActiveTerminal_bind_eq_restrict hlam hLam A c J T (gamma n)
      ((enlargedVisitEntrance_ae_support hlam hLam A c J s T P hP.1 hP.2.1 n).mono
        fun _ hp => hp.2.1)]
    apply Measure.restrict_mono_ae
    filter_upwards [enlargedActiveExitMixture_ae_velocity hlam hLam A c J T (gamma n)]
      with q hq
    intro ht
    apply Or.inl
    refine ⟨ht, ?_⟩
    rw [Interval.toFiniteUnion_carrier]
    exact subset_closure (hJ hq)
  exact ((Finset.sum_le_sum (s := Finset.range N) (fun n _ => hpiece n)) univ).trans
    (enlarged_piece_domination hlam hLam A c J s T P hP N).1

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
