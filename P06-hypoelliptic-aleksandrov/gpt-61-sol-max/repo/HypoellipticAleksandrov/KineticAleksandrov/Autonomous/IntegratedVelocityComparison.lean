module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.IntegratedVelocityBarrier
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelTheorem
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripMassComparison
public import PDEFoundation.Calculus.RegularityOrder


open private HypoellipticAleksandrov.KineticAleksandrov.Autonomous.sliceRegular_of_smooth from HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripMassComparison


/-! # Full-space occupation supersolution comparison

The source
potential is the existing actual Duhamel integral, not a separately supplied solution.
-/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set HypoellipticAleksandrov
open SectionTwo Evolution




/-- A nonnegative supersolution bounds the actual compact interior source potential. -/
theorem velocity_duhamel_le_barrier
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution)
    (hE : IsFullSpaceEvolution A E) (T : ℝ) (g q : Point → ℝ)
    (hgn : ∀ p, 0 ≤ g p)
    (hgs : ContDiff ℝ PDE.smoothOrder (rawLift g)) (hgc : HasCompactSupport g)
    (hgU : tsupport g ⊆ evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T)
    (hqc : Continuous q) (hqr : ∀ p, p.time ≤ T → IsSliceRegularAt q p)
    (hqn : ∀ p ∈ evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) T, 0 ≤ q p)
    (hqo : ∀ p ∈ evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T,
      transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) q p ≤ -g p)
    (p₀ : Point) (hp₀ : p₀ ∈ evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T) :
    duhamelPotential E.2 T g p₀ ≤ q p₀ := by
  obtain ⟨⟨-, C, -, hCb⟩, -, hsm, -, heq, hc, ht, hl, -⟩ :=
    kinetic_duhamel hH (by omega) autonomousWholeDomain_admissible (zeroCurve_piecewiseC1 1)
      hlam hLam one_pos (evolutionCoefficient A.a) (evolutionCoefficient_smooth A)
      (evolutionCoefficient_symmetric A.a) (evolutionCoefficient_bounds A)
      (identityDrift 1) (identityDrift_smooth 1) (identityDrift_bounds 1)
      E.1 E.2 hE T g hgn hgs hgc hgU
  have hΩ := isOpen_of_isAdmissibleEvolutionDomain autonomousWholeDomain_admissible

  have hs : movingClosedSlab autonomousWholeDomain (fun _ => 0) p₀.time T ⊆
      evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) T :=
    fun _ hp => ⟨hp.2.1, hp.2.2⟩
  have ha : movingActiveSlab autonomousWholeDomain (fun _ => 0) p₀.time T ⊆
      evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T :=
    fun _ hp => ⟨hp.2.1, hp.2.2⟩
  have hreg := fun p hp => _root_.HypoellipticAleksandrov.KineticAleksandrov.Autonomous.sliceRegular_of_smooth (isOpen_duhamelCylinder (γ := fun _ => 0) hΩ continuous_const T) hsm p (ha hp)
  have hmax := growth_comparison hΩ continuous_const hlam (evolutionCoefficient_bounds A)
    (identityDrift_bounds 1).1 (le_refl 0) zero_le_one
    (a := p₀.time) (T := T) (u := fun p => duhamelPotential E.2 T g p - q p)
    ⟨C, fun p hp => by


      linarith only [((le_abs_self (duhamelPotential E.2 T g p)).trans (hCb p)), (hqn p (hs hp))]⟩
    ((hc.mono hs).sub hqc.continuousOn)
    (fun p hp => (hreg p hp).sub (hqr p hp.2.1.le))
    (fun p hp => by
      rw [viscousTransportedOperator_sub (hreg p hp) (hqr p hp.2.1.le),
        viscousTransportedOperator_zero, viscousTransportedOperator_zero, heq p (ha hp)]

      linarith only [(hqo p (ha hp))])
    (fun p hp hpt => by rw [ht p hpt]; linarith only [hqn p (hs hp)])
    (fun p hp hpf => by rw [hl p hpf]; linarith only [hqn p (hs hp)])
  exact sub_nonpos.mp (hmax p₀ ⟨le_rfl, hp₀.1.le, subset_closure hp₀.2⟩)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
