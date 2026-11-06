module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceLimitsInfinite
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitConeOneSign

/-! # The exact infinite-horizon Green supremum and inherited quadratic bound -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/- Every infinite pole determines the same physical pole at any later finite terminal time. -/
def stripPoleFinite (H : Interval) (e : StripPole H ⊤) (T ) (hT : e.1.time < T) :
    StripPole H (T : WithTop ℝ) := ⟨e.1, WithTop.coe_lt_coe.mpr hT, e.2.2⟩

/- Every finite terminal Green measure is the physical-time restriction of the infinite one. -/
theorem stripGreen_finite_restrict_infinite
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤)
    (T : ℝ) (hT : e.1.time < T) :
    stripGreen hH hLE hlam hLam A H T (stripPoleFinite H e T hT) =
      (stripGreen hH hLE hlam hLam A H ⊤ e).restrict {p | p.time < T} :=
  stripGreenOfKernel_horizonRestriction H _ T (stripPoleFinite H e T hT)

/- The actual infinite Green measure is the supremum over all later finite terminal times. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
