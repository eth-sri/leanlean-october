module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceWeak

/-! # Restriction of the existing kinetic weak equation

Weak tests supported in a smaller domain extend by zero to the larger domain.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Evolution Occupation

/-- Restrict a kinetic weak solution to a subdomain without changing its source. -/
theorem boundedSource_weak_restrict {d : ℕ} {U V : Set (KineticPoint d)}
    (hUV : U ⊆ V)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (u f : KineticPoint d → ℝ) (h : IsKineticWeakTransportedSolution B b V u f) :
    IsKineticWeakTransportedSolution B b U u f := by
  rw [← isWeakTransportedSolution_comp_iff] at h ⊢
  exact h.mono fun _ hx => hUV hx

/-- Changing the source only outside the tested domain preserves the kinetic weak equation. -/
theorem boundedSource_weak_source_congr {d : ℕ} {U : Set (KineticPoint d)}
    (hU : MeasurableSet U) (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (u f g : KineticPoint d → ℝ) (hfg : EqOn f g U)
    (h : IsKineticWeakTransportedSolution B b U u f) :
    IsKineticWeakTransportedSolution B b U u g := by
  refine ⟨h.1, fun ψ hψ hc hs => ?_⟩
  rw [h.2 ψ hψ hc hs]
  apply setIntegral_congr_fun hU
  intro z hz
  simp [hfg hz]

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
