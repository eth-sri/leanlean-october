module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionHomogeneous
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EarlyExit

/-! # The full actual finite-strip Green identity for the original bounded C112 class -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter Parabolic
open SectionTwo TheoremA Evolution

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (H : Interval)

/-- The original bounded C112 class has the full actual identity at every strictly interior
starting time, with no extra regularity or boundary-solution premise. -/
theorem strip_identity_C112_of_realization (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (sMinus T : ℝ) (_hT : sMinus < T)
    (e : StripPole H (T : WithTop ℝ)) (he : sMinus < e.1.time) (phi : Point → ℝ)
    (hphi : IsKineticC112On phi (reconstructionStrip H sMinus T))
    (hc : ContinuousOn phi (reconstructionStrip H sMinus T ∪ reconstructionExit H sMinus T))
    (hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H sMinus T,
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M) :
    phi e.1 = (∫ p, phi p ∂stripExitOfRealization A H E hE T e) -
      ∫ p, forwardScalarOperator A.a phi p ∂stripGreenOfKernel H E.2 T e := by
  obtain ⟨u, hform, hu, hop, huc, hexit⟩ := strip_bounded_source_reconstruction
    A H E hE sMinus T phi hphi hc hb
  have hub := reconstruction_uniform_bound H E A sMinus T e he phi u hphi hb hform huc
  have hrep := reconstruction_homogeneous_exit_representation A H E hE
    sMinus T e he u hu hop huc hub
  have hclosed : ∀ᵐ p ∂stripExitOfRealization A H E hE T e,
      p ∈ stripClosedExit H T := by
    rw [ae_iff]
    exact stripExitOfRealization_compl_closedExit A H E hE T e
  have hAE : u =ᵐ[stripExitOfRealization A H E hE T e] phi := by
    filter_upwards [hclosed,
      stripExitOfRealization_ae_closed_future A H E hE T e] with p hp ht
    apply hexit
    rcases hp with hp | hp
    · exact Or.inl hp
    · by_cases hpt : p.time = T
      · exact Or.inl ⟨hpt, ht.2.2⟩
      · exact Or.inr ⟨he.trans_le ht.1, lt_of_le_of_ne hp.1 hpt, hp.2⟩
  rw [integral_congr_ae hAE] at hrep
  have hh := hform e he
  rw [integral_neg] at hh
  linarith

/-- The canonical autonomous families satisfy the full C112 identity at an interior pole. -/
theorem strip_identity_C112 (sMinus T : ℝ) (hT : sMinus < T)
    (e : StripPole H (T : WithTop ℝ)) (he : sMinus < e.1.time) (phi : Point → ℝ)
    (hphi : IsKineticC112On phi (reconstructionStrip H sMinus T))
    (hc : ContinuousOn phi (reconstructionStrip H sMinus T ∪ reconstructionExit H sMinus T))
    (hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H sMinus T,
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M) :
    phi e.1 = (∫ p, phi p ∂stripExit A H T e) -
      ∫ p, forwardScalarOperator A.a phi p ∂stripGreen A H T e :=
  strip_identity_C112_of_realization A H _
    (stripEvolution_spec A H) sMinus T hT e he phi hphi hc hb

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
