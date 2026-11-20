module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitsPieces
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.RestartTailStatement

/-! # Core domination by visits in an enlarged bounded velocity strip

Source: companion paper, Lemma 8.8 (core domination). The outer interval is independent
of J_Q.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

/-- Active pieces exhaust the core and are dominated by their all-time extensions. -/
def CoreDominationStatement : Prop :=
  ∀
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (hP : P.time < T ∧ P.velocity 0 ∈ J.carrier),
    |c.vbar| = 2 * c.r → closure c.active ⊆ J.carrier → s ≤ P.time →
    let mu := stripGreen A J T
      ⟨P, WithTop.coe_lt_coe.mpr hP.1, hP.2⟩
    let nu := enlargedVisitStarts A c J s T P
    mu.restrict {p | p.velocity 0 ∈ c.core} =
      Measure.sum (fun n =>
        (enlargedActivePiece A c J s T P n).restrict
          {p | p.velocity 0 ∈ c.core}) ∧
      mu.restrict {p | p.velocity 0 ∈ c.core} ≤
        (enlargedActiveGreen A c nu).restrict
          {p | p.velocity 0 ∈ c.core}

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
