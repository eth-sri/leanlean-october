module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripMassQuadratic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionCollar
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelCutoffSequence

/-! # Profile comparison for the actual finite-strip Green measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter Parabolic
open SectionTwo TheoremA Evolution
open scoped Topology ENNReal

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
  (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ))
include Lam A hE

/-- Integrating a smooth nonnegative profile against the actual Green measure is bounded
by any smooth native supersolution profile. -/
theorem reconstruction_green_lintegral_le_barrier
    (k q : Point → ℝ)
    (hk : ContDiff ℝ (⊤ : ℕ∞) (rawLift k)) (hkn : ∀ p, 0 ≤ k p)
    (hqc : Continuous q) (hqr : ∀ p, IsSliceRegularAt q p)
    (hqn : ∀ p ∈ evolutionPastClosedCylinder (intervalDomain H) (fun _ => 0) T, 0 ≤ q p)
    (hqo : ∀ p ∈ evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T,
      transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1)
      q p ≤ -k p) :
    ∫⁻ p, ENNReal.ofReal (k (sectionTwoPoint p)) ∂stripGreenOfKernel H E.2 T e ≤
      ENNReal.ofReal (q (sectionTwoPoint e.1)) := by
  refine stripGreen_lintegral_le_of_compact_sources H E T e k _ hk hkn ?_
  intro g hg0 hgk hgs hgc hgU hp
  exact autonomous_duhamel_le_barrier A (intervalDomain_admissible H) E hE T g q hg0 hgs hgc hgU hqc (fun p _ => hqr p) hqn
    (fun z hz => (hqo z hz).trans (neg_le_neg (hgk z))) _ hp

/-- Integrating a smooth nonnegative profile against the actual Green measure is bounded
by any smooth native supersolution profile. -/
theorem reconstruction_green_le_profile
    (k q : ℝ → ℝ)
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hkn : ∀ v, 0 ≤ k v)
    (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hqn : ∀ v, H.lo ≤ v → v ≤ H.hi → 0 ≤ q v)
    (hqo : ∀ p, transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1)
      (reconstructionProfile q) p ≤ -k (p.position 0)) :
    ∫ p, k (p.velocity 0) ∂stripGreenOfKernel H E.2 T e ≤ q (e.1.velocity 0) := by
  have h := reconstruction_green_lintegral_le_barrier A H E hE T e
    (reconstructionProfile k) (reconstructionProfile q)
    (hk.comp ((contDiff_apply ℝ ℝ (0 : Fin 1)).comp contDiff_snd.fst))
    (fun p => hkn _) (reconstructionProfile_continuous hq.continuous)
    (reconstructionProfile_regular (hq.of_le (by simp)))
    (fun z hz => by
      have hv := intervalDomain_closure_bounds H
        (by simpa only [mem_closure_movingDomain_iff, sub_zero] using hz.2)
      exact hqn _ hv.1 hv.2) (fun z _ => hqo z)
  have hmeas : AEStronglyMeasurable (fun p : Point => k (p.velocity 0))
      (stripGreenOfKernel H E.2 T e) :=
    (hk.continuous.comp ((continuous_apply 0).comp continuous_velocity)).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => hkn _) hmeas]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq
    (ENNReal.toReal_ofReal (hqn _ e.2.2.1.le e.2.2.2.le))

/-- Exponential collar occupation is uniformly quadratic in the collar width. -/
theorem reconstruction_green_collar_bound
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ p, reconstructionCollarWeight H δ (p.velocity 0) ∂stripGreenOfKernel H E.2 T e ≤
      2 * δ ^ 2 / lam := by
  have h := reconstruction_green_le_profile A H E hE T e
    (reconstructionCollarWeight H δ) (reconstructionCollarProfile H lam δ)
    (reconstructionCollarWeight_smooth H δ) (reconstructionCollarWeight_nonneg H δ)
    (reconstructionCollarProfile_smooth H lam δ)
    (fun v hlo hhi => (reconstructionCollarProfile_bounds H A.positive hδ ⟨hlo, hhi⟩).1)
    (reconstructionCollarProfile_operator_le A H hδ)
  exact h.trans (reconstructionCollarProfile_bounds H A.positive hδ ⟨e.2.2.1.le, e.2.2.2.le⟩).2

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
