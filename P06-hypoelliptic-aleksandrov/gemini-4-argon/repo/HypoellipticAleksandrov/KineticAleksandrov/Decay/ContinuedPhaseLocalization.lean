module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.PhaseCurve
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonEvolution
import Mathlib.Tactic.FunProp

/-! # Speed-free continuous-curve phase localization for block continuation -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/- Smooth forbidden-phase tests have zero integral against the supplied moving kernel. -/
theorem phase_test_zero_of_continuous_curve (d )
    (lam Lam : ℝ)
    (m Lb : ℝ) (D : Set (PDE.Vec d)) (B : CoefficientField d)
    (b : PDE.Vec d → PDE.Vec d) (hsetting : SourceSetting lam Lam m Lb D B b)
    (σ τ ρ : ℝ) (γ : ℝ → PDE.Vec d) (hρ : 0 < ρ)
    (hγ : Continuous γ)
    (S : TerminalOperatorFamily (PDE.euclideanBall 0 ρ) γ)
    (K : MovingFiberKernel (PDE.euclideanBall 0 ρ) γ)
    (hreal : RealizesTerminalEvolution (PDE.euclideanBall 0 ρ) γ
      (PDE.isOpen_euclideanBall 0 ρ).measurableSet (zIndependentCoefficient B) b S K)
    (ξ z0 v : PDE.Vec d) (hξ : PDE.vecNormSq ξ = 1)
    (hστ : σ ≤ τ)
    (hv : v ∈ movingDomain (PDE.euclideanBall 0 ρ) γ σ)
    (sgn ) (hsgn : sgn = 1 ∨ sgn = -1)
    (φ : BoundedBorel (EvolutionAmbientState d))
    (hφ : IsSmoothCompactTerminalDatum (PDE.euclideanBall 0 ρ)
      γ τ φ)
    (hbound : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hs : tsupport (φ : EvolutionAmbientState d → ℝ) ⊆
      {x | 0 < sgn * (phaseCoordinate ξ z0 x - phaseCenter ξ b γ σ τ) -
        Lb * ρ * (τ - σ)}) :
    ∫ x, φ x ∂K.master (movingQuery σ τ hστ v z0 hv) = 0 := by
  let Ω := PDE.euclideanBall (0 : PDE.Vec d) ρ
  let γc := γ
  let p : EvolutionState Ω γc σ := ⟨(v, z0), hv, mem_univ _⟩
  have hi : ∫ x, φ x ∂K.master (movingQuery σ τ hστ v z0 hv) =
      ∫ x, φ x.1 ∂K.fiberKernel (PDE.isOpen_euclideanBall 0 ρ).measurableSet σ τ hστ p :=
    integral_master_eq_fiber K (PDE.isOpen_euclideanBall 0 ρ).measurableSet
      σ τ hστ p φ φ.measurable
  by_cases ht : σ = τ
  · subst τ
    rw [hi, hreal.2.2.1 σ]
    simp only [ProbabilityTheory.Kernel.id_apply, integral_dirac]
    change φ (v, z0) = 0
    by_contra hn
    have hs' := hs (subset_tsupport (φ : EvolutionAmbientState d → ℝ)
      (show (v, z0) ∈ Function.support (φ : EvolutionAmbientState d → ℝ) from hn))
    simp only [Set.mem_ofPred_eq, phaseCoordinate, phaseCenter, sub_self,
      PDE.vecDot, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero, intervalIntegral.integral_same, sub_zero, lt_self_iff_false]
      at hs'
  · have ht' : σ < τ := lt_of_le_of_ne hστ ht
    obtain ⟨u, hu, hup, -⟩ := hreal.1 τ φ hφ
    have hB : ∀ t v, (B t v).PosSemidef := by
      intro t v
      have hbounds := (sectionTwoCoefficient_fullBounds lam Lam B hsetting.1).2.2
      exact posSemidef_of_hasEverywhereLoewnerBounds hsetting.1.1.le hbounds t v 0
    have hnonpos := classical_phase_test_nonpos B b γc σ τ Lb ρ ht' hρ ξ z0 hξ
      hsetting.2.2.2.2.1.1 hγ hB sgn hsgn
      φ hφ hbound hs u hu v hv
    have huintegral : ∫ x, φ x ∂K.master (movingQuery σ τ hστ v z0 hv) =
        u ⟨σ, v, z0⟩ := by
      rw [hi]
      exact (hreal.2.1 σ τ hστ p (terminalStateDatum φ)).symm.trans (hup σ hστ p).symm
    apply le_antisymm
    · exact huintegral.trans_le hnonpos
    · exact integral_nonneg (fun x => (hbound x).1)


/- The supplied moving kernel is concentrated in the source closed phase strip. -/
end HypoellipticAleksandrov.KineticAleksandrov.Decay
