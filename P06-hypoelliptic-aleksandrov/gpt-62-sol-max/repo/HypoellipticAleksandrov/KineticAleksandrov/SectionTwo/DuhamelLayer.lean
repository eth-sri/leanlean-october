module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSliceLimit

/-! # Terminal-layer weak identities for full kinetic source slices -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Filter
open Evolution Occupation
open scoped Topology
variable {d : ℕ}

/-- Passing the kinetic cutoff identity to the limit retains the terminal source term. -/
theorem kinetic_slice_weak_identity {B : FullKineticCoefficient d}
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    {b : PDE.Vec d → PDE.Vec d} (hb : IsSmoothDrift b)
    {D : Set (EvolutionVec d)} (hD : IsOpen D) {V u : EvolutionVec d → ℝ}
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V D)
    (hVeq : ∀ p ∈ D, transportedOperator B b V p = 0)
    (huV : ∀ p ∈ D, u p = V p) (hum : Measurable u)
    (C : ℝ) (hC0 : 0 ≤ C) (hub : ∀ p, |u p| ≤ C)
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (r : ℝ) (hψD : ∀ x ∈ tsupport ψ, timeCoord d x < r → x ∈ D)
    (m₀ : EvolutionAmbientState d → ℝ)
    (hlim : ∀ w, Tendsto (fun t => u (packQ d (t, w)) * ψ (packQ d (t, w)))
      (𝓝[<] r) (𝓝 (m₀ w))) :
    (∫ q : ℝ × EvolutionAmbientState d,
      {q : ℝ × EvolutionAmbientState d | q.1 < r}.indicator
        (fun q => u (packQ d q) * transportedAdjoint B b ψ (packQ d q)) q) +
      ∫ w, m₀ w = 0 := by
  refine evolution_layer_slice_identity hB hb hD.measurableSet ?_ huV hum hC0 hub hψ hc hψD hlim
  intro φ hφ hφc hφs
  rw [integral_transportedAdjoint_contDiffOn hD hB hBs hb hV φ hφ hφc hφs,
    setIntegral_congr_fun hD.measurableSet (g := fun _ => (0 : ℝ))]
  · exact integral_zero _ _
  · intro x hx
    simp only [hVeq x hx, zero_mul]

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
