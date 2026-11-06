module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitsPieces
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.IntegratedVelocity
import Mathlib.Tactic

/-! # Full-space bounds used in the enlarged-strip quadratic count -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov

/- Inserting time in scalar physical coordinates is measurable. -/
theorem measurable_enlargedOccupationPoint (P : Point) :
    Measurable (fun tz : ℝ × Z => enlargedTerminalPoint (P.time + tz.1) tz.2) := by
  exact (KineticPoint.measurable_equivProd_symm 1).comp
    ((measurable_const.add measurable_fst).prodMk
      ((Measurable.of_eval fun _ => measurable_fst.comp measurable_snd).prodMk
        (Measurable.of_eval fun _ => measurable_snd.comp measurable_snd)))

/- Full-space terminal measures have mass at most one. -/
theorem enlargedFullSpaceTerminal_mass_le_one
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (P : Point) (b : ℝ) :
    enlargedFullSpaceTerminal hH hLE hlam hLam A P b univ ≤ 1 := by
  change ((kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal (b - P.time))
    (P.position 0, P.velocity 0)).map (enlargedTerminalPoint b)) univ ≤ 1
  have _h_inl_8 : Measurable (enlargedTerminalPoint b) := by
      exact (KineticPoint.measurable_equivProd_symm 1).comp
        (measurable_const.prodMk
          ((Measurable.of_eval fun _ => measurable_fst).prodMk
            (Measurable.of_eval fun _ => measurable_snd)))

    /- The physical spacetime map for elapsed occupation is measurable. -/
  rw [Measure.map_apply _h_inl_8
    MeasurableSet.univ, preimage_univ]
  exact kernelXV_mass_le_one _ _ _

/- Full-space occupation of a physical velocity band is its elapsed probability integral. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
