module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtension

/-! # Canonical bounded smooth tests and finite-horizon probability normalization -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

section
variable {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (H : Interval) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) (phi : Point → ℝ)
    (hphi : ContDiff ℝ (⊤ : ℕ∞) (phi ∘ (KineticPoint.equivProd 1).symm))

include hphi in
/-- Global physical smoothness transfers to the fixed packed Euclidean carrier. -/
theorem reconstruction_raw_smooth_to_packed :
    ContDiff ℝ (⊤ : ℕ∞) (phi ∘ reconstructionPhysicalHomeomorph) := by
  let c := fun x =>
    ((evolutionProdCLE 1 x).1, (evolutionProdCLE 1 x).2.2, (evolutionProdCLE 1 x).2.1)
  exact hphi.comp ((evolutionProdCLE 1).contDiff.fst.prodMk ((evolutionProdCLE 1).contDiff.snd.snd.prodMk (evolutionProdCLE 1).contDiff.snd.fst))

include hphi in
/-- The source's canonical bounded smooth identity in raw physical coordinates. -/
theorem strip_identity_bounded_smooth
    (hb : ∃ M : ℝ, ∀ p, p.velocity 0 ∈ H.carrier →
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M) :
    phi e.1 = (∫ p, phi p ∂stripExit hlam hLam A H T e) -
      ∫ p, forwardScalarOperator A.a phi p ∂stripGreen hlam hLam A H T e :=
  strip_identity_bounded_smooth_of_realization hlam hLam A H _
    (stripEvolution_spec hlam hLam A H) T e phi
    (reconstruction_raw_smooth_to_packed phi hphi) hb

/-- The canonical finite-horizon exit measure has total mass one. -/
theorem stripExit_mass_one : stripExit hlam hLam A H T e univ = 1 :=
  stripExitOfRealization_mass_one hlam hLam A H _
    (stripEvolution_spec hlam hLam A H) T e

end

/-- The canonical exit family consists of probability measures. -/
instance stripExit_isProbabilityMeasure
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) : IsProbabilityMeasure (stripExit hlam hLam A H T e) :=
  ⟨stripExit_mass_one hlam hLam A H T e⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
