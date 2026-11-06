module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceRestriction
public import HypoellipticAleksandrov.KineticAleksandrov.ClassicalInputs
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminalWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSmooth

/-! # Homogeneous regularity before a bounded source starts

A bounded Borel source that vanishes before a fixed time has homogeneous weak forcing
there. Hörmander gives a smooth almost-everywhere representative on that earlier domain.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open Set MeasureTheory Evolution Occupation
open scoped Topology

/-- A bounded potential is an actual homogeneous weak solution before its source starts. -/
theorem duhamelPotential_weak_before_source
    {d Ω γ}
    (hΩa : IsAdmissibleEvolutionDomain Ω) (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (g : KineticPoint d → ℝ) (hg : Measurable g)
    (M ) (hM : 0 ≤ M) (hgb : ∀ p, |g p| ≤ M) (s T : ℝ) (hsT : s ≤ T)
    (hgz : ∀ p : KineticPoint d, p.time < s → g p = 0) :
    IsWeakTransportedSolution B b
      (evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ s)
      (duhamelPotential K T g ∘ evolutionHomeomorph d) (fun _ => 0) := by
  have hU := isOpen_evolutionPastOpenCylinder (isOpen_of_isAdmissibleEvolutionDomain hΩa)
    hγ s
  have hsub : evolutionPastOpenCylinder Ω γ s ⊆ evolutionPastOpenCylinder Ω γ T :=
    fun p hp => ⟨hp.1.trans_le hsT, hp.2⟩
  have hw := duhamel_bounded_isKineticWeakTransportedSolution hΩa hΩ hγ B b S K hreal
    hB hBs hb g hg M hM hgb T
  have hwr := boundedSource_weak_restrict hsub B b (duhamelPotential K T g)
    (fun p => -g p) hw
  have hsource : EqOn (fun p => -g p) (fun _ => 0)
      (evolutionPastOpenCylinder Ω γ s) := by
    intro p hp
    change -g p = 0
    rw [hgz p hp.1, neg_zero]
  have hzero := boundedSource_weak_source_congr hU.measurableSet B b
    (duhamelPotential K T g) (fun p => -g p) (fun _ => 0) hsource hwr
  exact (isWeakTransportedSolution_comp_iff B b _ _ _).2 hzero

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
