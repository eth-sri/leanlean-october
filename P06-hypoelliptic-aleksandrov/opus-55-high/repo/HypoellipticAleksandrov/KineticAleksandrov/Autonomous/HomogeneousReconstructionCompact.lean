module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionComparison
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceWeakGreenSigned
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure

/-! # Continuity of actual signed compact interior source potentials -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo Evolution

/-- Signed smooth compact interior sources have continuous actual Duhamel potentials.
A smooth positive shift reduces this to the nonnegative source theorem. -/
theorem reconstruction_compact_duhamel_continuousOn
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (g : Point → ℝ)
    (hgs : ContDiff ℝ (⊤ : ℕ∞) (rawLift g)) (hgc : HasCompactSupport g)
    (hgU : tsupport g ⊆ evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T) :
    ContinuousOn (duhamelPotential E.2 T g)
      (evolutionPastClosedCylinder (intervalDomain H) (fun _ => 0) T) := by
  classical
  let D := evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T
  let U := (KineticPoint.equivProd 1).symm ⁻¹' D
  have hD : IsOpen D := isOpen_duhamelCylinder
    (γ := fun _ => 0) (isOpen_of_isAdmissibleEvolutionDomain (intervalDomain_admissible H))
    continuous_const T
  have hU : IsOpen U := hD.preimage (KineticPoint.homeomorphProd 1).symm.continuous
  have hgcont : Continuous g := by
    have hh := hgs.continuous.comp (KineticPoint.homeomorphProd 1).continuous
    exact hh
  have hK := hgc.isCompact.image (KineticPoint.homeomorphProd 1).continuous
  obtain ⟨χ, hχ, hc, hs, hb, hone⟩ := exists_smooth_bump_of_isCompact_subset_isOpen hK hU
    (by
      aesop)
  let c : Point → ℝ := χ ∘ KineticPoint.equivProd 1
  have hcc : HasCompactSupport c := hc.comp_homeomorph (KineticPoint.homeomorphProd 1)
  have hcs : ContDiff ℝ _ (rawLift c) := hχ
  have hccont : Continuous c := hχ.continuous.comp (KineticPoint.homeomorphProd 1).continuous
  have hcD : tsupport c ⊆ D := by
    intro p hp
    have hh := hs ((tsupport_comp_subset_preimage χ
      (KineticPoint.homeomorphProd 1).continuous) hp)
    aesop
  obtain ⟨B, hB⟩ := hgcont.bounded_above_of_compact_support hgc
  let C := max B 0
  have hC : 0 ≤ C := le_max_right _ _
  have hgb : ∀ p, |g p| ≤ C := by
    aesop
  let f : BoundedBorel Point := ⟨g, hgcont.measurable, ⟨C, hC, hgb⟩⟩
  let b : BoundedBorel Point := ⟨fun p => C * c p,
    measurable_const.mul hccont.measurable, ⟨C, hC, fun p => by
      change |C * χ _| ≤ C
      rw [abs_mul, abs_of_nonneg hC, abs_of_nonneg (hb _).1]
      exact mul_le_of_le_one_right hC (hb _).2⟩⟩
  have hb0 : ∀ p, 0 ≤ b p := fun p => mul_nonneg hC (hb _).1
  have hfb0 : ∀ p, 0 ≤ (f + b) p := by
    intro p
    change 0 ≤ g p + C * c p
    by_cases hp : g p = 0
    · grind
    · have hcp : c p = 1 := hone _ ⟨p, subset_tsupport _ hp, rfl⟩
      rw [hcp]
      grind
  have hbs : ContDiff ℝ _ (rawLift b) := contDiff_const.mul hcs
  have hbc : HasCompactSupport b := hcc.mul_left
  have hbD : tsupport b ⊆ D :=
    (tsupport_mul_subset_right).trans hcD
  have hfbs : ContDiff ℝ _ (rawLift (f + b)) := hgs.add hbs
  have hfbc : HasCompactSupport (f + b) := hgc.add hbc
  have hfbD : tsupport (f + b) ⊆ D :=
    (tsupport_add _ _).trans (union_subset hgU hbD)
  have hcont (u : Point → ℝ) (hu0 : ∀ p, 0 ≤ u p)
      (hus : ContDiff ℝ (⊤ : ℕ∞) (rawLift u)) (huc : HasCompactSupport u)
      (huD : tsupport u ⊆ D) : ContinuousOn (duhamelPotential E.2 T u)
        (evolutionPastClosedCylinder (intervalDomain H) (fun _ => 0) T) := by
    obtain ⟨-, -, -, -, -, hcont, -⟩ :=
      kinetic_duhamel hH (by omega) (intervalDomain_admissible H) (zeroCurve_piecewiseC1 1)
        hlam hLam one_pos (evolutionCoefficient A.a) (evolutionCoefficient_smooth A)
        (evolutionCoefficient_symmetric A.a) (evolutionCoefficient_bounds A)
        (identityDrift 1) (identityDrift_smooth 1) (identityDrift_bounds 1)
        E.1 E.2 hE T u hu0 hus huc huD
    omega
  have hh := (hcont (f + b) hfb0 hfbs hfbc hfbD).sub (hcont b hb0 hbs hbc hbD)
  apply hh.congr
  intro p _
  have hs := strip_duhamel_sub H E.2 (f + b) b p T
  aesop

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
