module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SurvivalHalfMass
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SurvivalIteration
import Mathlib.Tactic

/-! # Exponential survival decay in the active velocity interval

Source: companion paper, Corollary 8.4 (survival decay). Constants precede coefficients,
clocks and poles. Only the evolution existence hypotheses remain.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo

/- The literal remaining killed mass from an interior active pole at nonnegative elapsed time. -/
def activeSurvivingMass
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
    (he : e.velocity 0 ∈ c.active) (t : ℝ) (ht : 0 ≤ t) : ℝ :=
  stripSurvivingMass c.activeInterval (stripEvolution hH hLE hlam hLam A c.activeInterval)
    e.time (e.time + t) (le_add_of_nonneg_right ht)
    (stripPoleState c.activeInterval ⊤ ⟨e, WithTop.coe_lt_top _, he⟩)

/- Uniform exponential decay of surviving killed mass, with constants depending only on
ellipticity and with every pole in the whole active interval allowed. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
