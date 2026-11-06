module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionComparison
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceWeakGreenSigned
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure
import Aesop
public import PDEFoundation.Calculus.RegularityOrder




/-! # Continuity of actual signed compact interior source potentials -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set
open SectionTwo

/-- Signed smooth compact interior sources have continuous actual Duhamel potentials.
A smooth positive shift reduces this to the nonnegative source theorem. -/
theorem reconstruction_compact_duhamel_continuousOn
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (g : Point → ℝ)
    (hgs : ContDiff ℝ PDE.smoothOrder (rawLift g)) (hgc : HasCompactSupport g)
    (hgU : tsupport g ⊆ evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T) :
    ContinuousOn (duhamelPotential E.2 T g)
      (evolutionPastClosedCylinder (intervalDomain H) (fun _ => 0) T) := by
  classical
  let D := evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T
  let U := (KineticPoint.equivProd 1).symm ⁻¹' D
  have hD : IsOpen D := isOpen_duhamelCylinder
     (isOpen_of_isAdmissibleEvolutionDomain (intervalDomain_admissible H))
    continuous_const T

  have hgcont : Continuous g := by
    have hh := hgs.continuous.comp (KineticPoint.homeomorphProd 1).continuous
    exact hh

  obtain ⟨χ, hχ, hc, hs, hb, hone⟩ := exists_smooth_bump_of_isCompact_subset_isOpen (hgc.isCompact.image (KineticPoint.homeomorphProd 1).continuous) (hD.preimage (KineticPoint.homeomorphProd 1).symm.continuous)
    (by
      simp_all [KineticPoint.equivProd] <;> aesop)
  let c : Point → ℝ := χ ∘ KineticPoint.equivProd 1




  obtain ⟨B, hB⟩ := hgcont.bounded_above_of_compact_support hgc
  let C := max B 0
  have hC : 0 ≤ C := le_max_right _ _
  have hgb : ∀ p, |g p| ≤ C := by
    intro p
    have hh : |g p| ≤ B := by exact hB p
    exact hh.trans (le_max_left _ _)
  let f : BoundedBorel Point := ⟨g, hgcont.measurable, ⟨C, hC, hgb⟩⟩
  let b : BoundedBorel Point := ⟨fun p => C * c p,
    measurable_const.mul (hχ.continuous.comp (KineticPoint.homeomorphProd 1).continuous).measurable, ⟨C, hC, fun p => by
      change |C * χ (KineticPoint.equivProd 1 p)| ≤ C
      rw [abs_mul, abs_of_nonneg hC, abs_of_nonneg (hb _).1]
      exact mul_le_of_le_one_right hC (hb _).2⟩⟩
  have hb0 : ∀ p, 0 ≤ b p := fun p => mul_nonneg hC (hb _).1

  have hbs : ContDiff ℝ PDE.smoothOrder (rawLift b) := contDiff_const.mul hχ
  have hbc : HasCompactSupport (b : Point → ℝ) := (hc.comp_homeomorph (KineticPoint.homeomorphProd 1)).mul_left
  have hbD : tsupport (b : Point → ℝ) ⊆ D :=
    (tsupport_mul_subset_right).trans ((fun ⦃p⦄ hp =>
  id (fun hh => hh) (hs (tsupport_comp_subset_preimage χ (Homeomorph.continuous (KineticPoint.homeomorphProd 1)) hp))))



  have hcont (u : Point → ℝ) (hu0 : ∀ p, 0 ≤ u p)
      (hus : ContDiff ℝ PDE.smoothOrder (rawLift u)) (huc : HasCompactSupport u)
      (huD : tsupport u ⊆ D) : ContinuousOn (duhamelPotential E.2 T u)
        (evolutionPastClosedCylinder (intervalDomain H) (fun _ => 0) T) := by
    obtain ⟨-, -, -, -, -, hcont, -⟩ :=
      kinetic_duhamel hH (by omega) (intervalDomain_admissible H) (zeroCurve_piecewiseC1 1)
        hlam hLam one_pos (evolutionCoefficient A.a) (evolutionCoefficient_smooth A)
        (evolutionCoefficient_symmetric A.a) (evolutionCoefficient_bounds A)
        (identityDrift 1) (identityDrift_smooth 1) (identityDrift_bounds 1)
        E.1 E.2 hE T u hu0 hus huc huD
    exact hcont
  have hh := (hcont (f + b) (by
      intro p
      change 0 ≤ g p + C * c p
      by_cases hp : g p = 0
      · rw [hp, zero_add]
        exact hb0 p
      ·
        rw [(show c p = 1 from hone _ ⟨p, subset_tsupport _ hp, rfl⟩), mul_one]
        linarith only [neg_abs_le (g p), hgb p]) (hgs.add hbs) (hgc.add hbc) ((tsupport_add _ _).trans (union_subset hgU hbD))).sub (hcont b hb0 hbs hbc hbD)
  apply hh.congr
  intro p _
  have hs := strip_duhamel_sub H E.2 (f + b) b p T
  rw [add_sub_cancel_right] at hs
  exact hs

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
