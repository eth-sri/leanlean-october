module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitConeLimit

/-! # Finite speed for the actual finite-horizon Green and exit measures -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter
open SectionTwo TheoremA Evolution

/-- Both actual measures lie in the literal physical finite-speed cone. -/
theorem strip_cone_ae_of_realization
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    (∀ᵐ p ∂stripExitOfRealization hH hlam hLam A H E hE T e,
      |p.position 0 - e.1.position 0| ≤ max |H.lo| |H.hi| * (p.time - e.1.time)) ∧
    ∀ᵐ p ∂stripGreenOfKernel H E.2 T e,
      |p.position 0 - e.1.position 0| ≤ max |H.lo| |H.hi| * (p.time - e.1.time) := by
  let V := max |H.lo| |H.hi|
  have hr := reconstruction_transport_cone_ae hH hlam hLam A H E hE T e
    (-V) 1 (V * e.1.time - e.1.position 0)
    (by dsimp only [reconstructionConeCoordinate]; ring)
    (fun v hv => by
      have hh : v ≤ V := hv.2.le.trans ((le_abs_self H.hi).trans (le_max_right _ _))
      linarith)
  have hl := reconstruction_transport_cone_ae hH hlam hLam A H E hE T e
    (-V) (-1) (V * e.1.time + e.1.position 0)
    (by dsimp only [reconstructionConeCoordinate]; ring)
    (fun v hv => by
      have hh : -V ≤ v := ((neg_le_neg (le_max_left _ _)).trans
        (neg_abs_le H.lo)).trans hv.1.le
      linarith)
  have hbound (p : Point)
      (hr : reconstructionConeCoordinate (-V) 1 (V * e.1.time - e.1.position 0) p ≤ 0)
      (hl : reconstructionConeCoordinate (-V) (-1) (V * e.1.time + e.1.position 0) p ≤ 0) :
      |p.position 0 - e.1.position 0| ≤ V * (p.time - e.1.time) := by
    dsimp only [reconstructionConeCoordinate] at hr hl
    grind
  constructor
  · filter_upwards [hr.1, hl.1] with p hp hq
    grind
  · filter_upwards [hr.2, hl.2] with p hp hq
    grind

/-- The finite-horizon Green measure gives zero mass to violations of the physical cone. -/
theorem strip_cone_finite_of_realization
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    stripGreenOfKernel H E.2 T e
      {p | |p.position 0 - e.1.position 0| > max |H.lo| |H.hi| * (p.time - e.1.time)} = 0 := by
  have hh := (strip_cone_ae_of_realization hH hlam hLam A H E hE T e).2
  rw [ae_iff] at hh
  simp_all

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
