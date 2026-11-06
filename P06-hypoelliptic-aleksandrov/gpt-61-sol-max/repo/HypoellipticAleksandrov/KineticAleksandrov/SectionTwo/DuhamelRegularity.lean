module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelWeak
public import HypoellipticAleksandrov.KineticAleksandrov.ClassicalInputs
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSmooth
public import PDEFoundation.Calculus.RegularityOrder


/-! # Hörmander regularity for the full kinetic Duhamel source potential -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open Evolution Occupation

variable {d : ℕ} {Ω : PDE.VelocityRegion d} {γ : ℝ → PDE.Vec d}

/-- The full kinetic Duhamel potential solves the source equation in the existing weak carrier. -/
theorem duhamel_isKineticWeakTransportedSolution (hΩa : IsAdmissibleEvolutionDomain Ω)
    (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.VectorField d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (g : HypoellipticAleksandrov.KineticScalarField d) (hgn : ∀ p, 0 ≤ g p)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgs : ContDiff ℝ PDE.smoothOrder (fun q : ℝ × EvolutionAmbientState d =>
      g ⟨q.1, q.2.1, q.2.2⟩)) (T : ℝ)
    (hgU : tsupport g ⊆ evolutionPastOpenCylinder Ω γ T) :
    IsKineticWeakTransportedSolution B b (evolutionPastOpenCylinder Ω γ T)
      (duhamelPotential K T g) (fun p => -g p) := by


  have hWc : ContinuousOn (duhamelPotential K T g) (evolutionPastOpenCylinder Ω γ T) :=
    (continuousOn_duhamelPotential hΩa hΩ hγ B b S K hreal g hgn hg hgc hgs T hgU
      ).mono (fun p hp => ⟨hp.1.le, subset_closure hp.2⟩)

  apply (isWeakTransportedSolution_comp_iff B b _ _ _).1
  refine ⟨(hWc.comp (evolutionHomeomorph d).continuous.continuousOn (fun x hx => hx)).locallyIntegrableOn ((isOpen_duhamelCylinder (isOpen_of_isAdmissibleEvolutionDomain hΩa) hγ T).preimage (evolutionHomeomorph d).continuous).measurableSet, fun ψ hψ hc hs => ?_⟩
  have hfull := duhamel_weak_identity hΩa hΩ hγ B b S K hreal hB hBs hb
    g hgn hg hgc hgs T hgU hψ hc hs
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · simp only [Function.comp_apply, neg_mul, integral_neg]
    exact hfull
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
  · intro x hx
    rw [transportedAdjoint_eq_zero_of_notMem_tsupport ψ (fun h => hx (hs h)), mul_zero]

/-- Hörmander gives pointwise interior smoothness of the continuous kinetic source potential. -/
theorem duhamelPotential_contDiffOn (hH : HormanderHypoellipticityStatement)
    (hΩa : IsAdmissibleEvolutionDomain Ω)
    (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.VectorField d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (g : HypoellipticAleksandrov.KineticScalarField d) (hgn : ∀ p, 0 ≤ g p)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgs : ContDiff ℝ PDE.smoothOrder (fun q : ℝ × EvolutionAmbientState d =>
      g ⟨q.1, q.2.1, q.2.2⟩)) (T : ℝ)
    (hgU : tsupport g ⊆ evolutionPastOpenCylinder Ω γ T)
    {lam Lam m : ℝ} (hlam : 0 < lam) (hm : 0 < m)
    (hell : HasEverywhereLoewnerBounds lam Lam B)
    (hcoerc : HasUnitDirectionDriftCoercivity m b) :
    ContDiffOn ℝ PDE.smoothOrder (duhamelPotential K T g ∘ evolutionHomeomorph d)
      (evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ T) := by

  have hU := (isOpen_duhamelCylinder (isOpen_of_isAdmissibleEvolutionDomain hΩa) hγ T).preimage (evolutionHomeomorph d).continuous
  have hWc : ContinuousOn (duhamelPotential K T g) (evolutionPastOpenCylinder Ω γ T) :=
    (continuousOn_duhamelPotential hΩa hΩ hγ B b S K hreal g hgn hg hgc hgs T hgU
      ).mono (fun p hp => ⟨hp.1.le, subset_closure hp.2⟩)

  have hweak := (isWeakTransportedSolution_comp_iff B b _ _ _).2
    (duhamel_isKineticWeakTransportedSolution hΩa hΩ hγ B b S K hreal hB hBs hb
      g hgn hg hgc hgs T hgU)

  obtain ⟨f, hf, hae⟩ := exists_smooth_representative_transported_source hH hlam hB hell hb
    hm hcoerc hU hweak (((hgs.comp (evolutionProdCLE d).contDiff).neg).contDiffOn)

  exact hf.congr (fun x hx => (Measure.eqOn_open_of_ae_eq hae hU (hWc.comp (evolutionHomeomorph d).continuous.continuousOn (fun x hx => hx)) hf.continuousOn) hx)

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
