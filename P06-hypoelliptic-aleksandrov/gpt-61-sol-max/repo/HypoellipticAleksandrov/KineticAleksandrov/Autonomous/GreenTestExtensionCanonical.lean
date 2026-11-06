module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtension
public import PDEFoundation.Calculus.RegularityOrder


/-! # Canonical bounded smooth tests and finite-horizon probability normalization -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory
open Evolution

/-- Global physical smoothness transfers to the fixed packed Euclidean carrier. -/
theorem reconstruction_raw_smooth_to_packed (phi : Point → ℝ)
    (hphi : ContDiff ℝ PDE.smoothOrder (phi ∘ (KineticPoint.equivProd 1).symm)) :
    ContDiff ℝ PDE.smoothOrder (phi ∘ reconstructionPhysicalHomeomorph) := by
  let c  := fun x =>
    ((evolutionProdCLE 1 x).1, (evolutionProdCLE 1 x).2.2, (evolutionProdCLE 1 x).2.1)
  have hc : ContDiff ℝ PDE.smoothOrder c :=
    (evolutionProdCLE 1).contDiff.fst.prodMk
      ((evolutionProdCLE 1).contDiff.snd.snd.prodMk (evolutionProdCLE 1).contDiff.snd.fst)
  exact hphi.comp hc

variable (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam) (H : Interval) (T : ℝ) (e : StripPole H (T : WithTop ℝ))

/-- The source's canonical bounded smooth identity in raw physical coordinates. -/
theorem strip_identity_bounded_smooth
     (phi : Point → ℝ)
    (hphi : ContDiff ℝ PDE.smoothOrder (phi ∘ (KineticPoint.equivProd 1).symm))
    (hb : ∃ M : ℝ, ∀ p, p.velocity 0 ∈ H.carrier →
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M) :
    phi e.1 = (∫ p, phi p ∂stripExit hH hLE hlam hLam A H T e) -
      ∫ p, forwardScalarOperator A.a phi p ∂stripGreen hH hLE hlam hLam A H T e :=
  strip_identity_bounded_smooth_of_realization hH hlam hLam A H _
    _ T e phi
    (reconstruction_raw_smooth_to_packed phi hphi) hb

/-- The canonical finite-horizon exit measure has total mass one. -/
theorem stripExit_mass_one
     : stripExit hH hLE hlam hLam A H T e univ = 1 :=
  stripExitOfRealization_mass_one hH hlam hLam A H _
    _ T e

/-- The canonical exit family consists of probability measures. -/
instance stripExit_isProbabilityMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) : IsProbabilityMeasure (stripExit hH hLE hlam hLam A H T e) :=
  ⟨stripExit_mass_one hH hLE hlam hLam A H T e⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
