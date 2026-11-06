module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceWeakDetermination
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelWeak
public import PDEFoundation.Calculus.RegularityOrder


/-! # Smooth testing discharges the finite-measure determination premise -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open Evolution Occupation

variable {d : ℕ} {Ω : PDE.VelocityRegion d} {γ : ℝ → PDE.Vec d}

/-- Product-coordinate test sources retain their closed support under the homeomorphism. -/
theorem boundedSourceTest_support (φ : ℝ × EvolutionAmbientState d → ℝ) :
    tsupport (φ ∘ KineticPoint.equivProd d) =
      (KineticPoint.equivProd d) ⁻¹' tsupport φ := by
  change tsupport (φ ∘ KineticPoint.homeomorphProd d) = _
  rw [tsupport_comp_eq_preimage]
  rfl

/-- The smooth Duhamel theorem gives the exact product-coordinate test identity. -/
theorem duhamel_smooth_product_identity (hΩa : IsAdmissibleEvolutionDomain Ω)
    (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.VectorField d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (T : ℝ)
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ PDE.smoothOrder ψ)
    (hc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ T)
    (φ : ℝ × EvolutionAmbientState d → ℝ) (hφ : ContDiff ℝ PDE.smoothOrder φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ boundedSourcePast Ω γ T)
    (hφr : ∀ q, 0 ≤ φ q ∧ φ q ≤ 1) :
    (∫ q, transportedAdjoint B b ψ (packQ d q) *
      duhamelPotential K T (φ ∘ KineticPoint.equivProd d) ⟨q.1, q.2.1, q.2.2⟩) =
      -(∫ q, ψ (packQ d q) * φ q) := by
  let g := φ ∘ KineticPoint.equivProd d





  have h := duhamel_weak_identity hΩa hΩ hγ B b S K hreal hB hBs hb g (fun p => (hφr _).1)
    (hφ.continuous.comp (KineticPoint.homeomorphProd d).continuous) (hφc.comp_homeomorph (KineticPoint.homeomorphProd d)) hφ T (by
        intro p hp
        rw [boundedSourceTest_support] at hp
        exact hφU hp) hψ hc hψs
  rw [integral_evolution_eq_prod, integral_evolution_eq_prod] at h
  simp only [duhamel_homeomorph_packQ] at h


  exact (show (∫ q, transportedAdjoint B b ψ (packQ d q) *
      duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩) =
      ∫ q, duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩ *
        transportedAdjoint B b ψ (packQ d q) by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q => mul_comm _ _).trans (h.trans (congrArg Neg.neg (by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q => mul_comm _ _)))

/-- The transported adjoint's support is contained in the support of its test. -/
theorem boundedSourceAdjoint_support {B : FullKineticCoefficient d}
    {b : PDE.VectorField d} (ψ : EvolutionVec d → ℝ) :
    tsupport (transportedAdjoint B b ψ) ⊆ tsupport ψ := by
  apply closure_minimal
  · intro x hx
    by_contra hnot
    exact hx (transportedAdjoint_eq_zero_of_notMem_tsupport ψ hnot)
  · exact isClosed_tsupport ψ

/-- Compact weak tests have a uniform lower time bound in product coordinates. -/
theorem exists_boundedSource_test_floor (Λ : ℝ × EvolutionAmbientState d → ℝ)
    (hc : HasCompactSupport Λ) (T : ℝ) :
    ∃ a : ℝ, a < T ∧ ∀ q, Λ q ≠ 0 → a ≤ q.1 := by
  obtain ⟨lower, hLower⟩ := (hc.image continuous_fst).bddBelow
  refine ⟨min lower (T - 1), ?_, ?_⟩
  · exact (min_le_right lower (T - 1)).trans_lt (by linarith)
  · intro q hq
    exact (min_le_left lower (T - 1)).trans (hLower ⟨q, subset_tsupport Λ hq, rfl⟩)

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
