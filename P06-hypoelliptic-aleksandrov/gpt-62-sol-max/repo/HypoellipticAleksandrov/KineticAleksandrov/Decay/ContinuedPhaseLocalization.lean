module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.PhaseLocalization
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonEvolution
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierGeometry
import Mathlib.Tactic.FunProp

/-! # Phase localization on a continuously moving ball for block continuation -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

section
variable {d : ℕ} (lam Lam : ℝ) (m Lb : ℝ) (D : Set (PDE.Vec d)) (B : CoefficientField d)
  (b : PDE.Vec d → PDE.Vec d) (hsetting : SourceSetting lam Lam m Lb D B b) (σ τ ρ : ℝ)
  (c : PDE.Vec d) (γ center : ℝ → PDE.Vec d) (hρ : 0 < ρ) (hc : Continuous center)
  (hcenter : ∀ t, center t = γ t + c) (S : TerminalOperatorFamily (PDE.euclideanBall c ρ) γ)
  (K : MovingFiberKernel (PDE.euclideanBall c ρ) γ)
  (hreal : RealizesTerminalEvolution (PDE.euclideanBall c ρ) γ (PDE.isOpen_euclideanBall c ρ).measurableSet (zIndependentCoefficient B) b S K)
  (ξ z0 v : PDE.Vec d) (hξ : PDE.vecNormSq ξ = 1) (hστ : σ ≤ τ)
  (hv : v ∈ movingDomain (PDE.euclideanBall c ρ) γ σ)
include lam Lam m D B hsetting hρ hc hcenter S hreal hξ

/-- Smooth forbidden-phase tests have zero integral against the supplied moving kernel. -/
private theorem phase_test_zero
    (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1)
    (φ : BoundedBorel (EvolutionAmbientState d))
    (hφ : IsSmoothCompactTerminalDatum (PDE.euclideanBall c ρ)
      γ τ φ)
    (hbound : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hs : tsupport (φ : EvolutionAmbientState d → ℝ) ⊆
      {x | 0 < sgn * (phaseCoordinate ξ z0 x - phaseCenter ξ b center σ τ) -
        Lb * ρ * (τ - σ)}) :
    ∫ x, φ x ∂K.master (movingQuery σ τ hστ v z0 hv) = 0 := by
  let p : EvolutionState (PDE.euclideanBall c ρ) γ σ := ⟨(v, z0), hv, mem_univ _⟩
  have hi : ∫ x, φ x ∂K.master (movingQuery σ τ hστ v z0 hv) =
      ∫ x, φ x.1 ∂K.fiberKernel (PDE.isOpen_euclideanBall c ρ).measurableSet σ τ hστ p :=
    integral_master_eq_fiber K (PDE.isOpen_euclideanBall c ρ).measurableSet
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
    have hmove t : movingDomain (PDE.euclideanBall 0 ρ) center t =
        movingDomain (PDE.euclideanBall c ρ) γ t := by
      ext w
      simp only [mem_movingDomain_euclideanBall_iff, add_zero, hcenter]
    have hu' : IsClassicalTerminalSolution (PDE.euclideanBall 0 ρ) center
        (zIndependentCoefficient B) b τ φ u := by
      simpa only [IsClassicalTerminalSolution, evolutionPastClosedCylinder,
        evolutionPastInteriorRaw, evolutionPastOpenCylinder, evolutionTerminalClosure,
        evolutionLateralFrontier, hmove] using hu
    have hφ' : IsSmoothCompactTerminalDatum (PDE.euclideanBall 0 ρ) center τ φ := by
      simpa only [IsSmoothCompactTerminalDatum, evolutionStateSet, hmove] using hφ
    have hnonpos := classical_phase_test_nonpos B b center σ τ Lb ρ ht' hρ ξ z0 hξ
      hsetting.2.2.2.2.1.1 hc hB sgn hsgn φ hφ' hbound hs u hu' v (by rwa [hmove])
    have huintegral : ∫ x, φ x ∂K.master (movingQuery σ τ hστ v z0 hv) =
        u ⟨σ, v, z0⟩ := by
      rw [hi]
      exact (hreal.2.1 σ τ hστ p (terminalStateDatum φ)).symm.trans (hup σ hστ p).symm
    apply le_antisymm
    · exact huintegral.trans_le hnonpos
    · exact integral_nonneg (fun x => (hbound x).1)


/-- The supplied moving kernel is concentrated in the source closed phase strip. -/
theorem phase_localization_of_center_curve
    : ∀ᵐ x ∂K.master (movingQuery σ τ hστ v z0 hv),
      |phaseCoordinate ξ z0 x - phaseCenter ξ b center σ τ| ≤ Lb * ρ * (τ - σ) := by
  let μ := K.master (movingQuery σ τ hστ v z0 hv)
  have hfinite : IsFiniteMeasure μ := ⟨(K.mass_le_one _).trans_lt ENNReal.one_lt_top⟩
  let U := evolutionStateSet (PDE.euclideanBall c ρ) γ τ
  have hU : IsOpen U := (isOpen_movingDomain (PDE.isOpen_euclideanBall c ρ) τ).prod
    isOpen_univ
  have hμ : μ Uᶜ = 0 := by
    have hr : μ.restrict U = μ := K.terminal_support _
    calc
      μ Uᶜ = (μ.restrict U) Uᶜ := by rw [hr]
      _ = μ (Uᶜ ∩ U) := Measure.restrict_apply hU.measurableSet.compl
      _ = 0 := by simp only [compl_inter_self, measure_empty]
  have hq : Continuous (fun x : EvolutionAmbientState d =>
      phaseCoordinate ξ z0 x - phaseCenter ξ b center σ τ) := by
    unfold phaseCoordinate PDE.vecDot
    simp only [Pi.sub_apply]
    fun_prop
  apply ae_phase_strip_of_forbidden_tests hU hμ hq (Lb * ρ * (τ - σ))
  intro sgn hsgn φ hφ hcompact hs hbound
  let φB := smoothTestDatum φ hφ hbound
  have hdatum : IsSmoothCompactTerminalDatum (PDE.euclideanBall c ρ)
      γ τ φB := ⟨hφ, hcompact, fun x hx => (hs hx).2⟩
  exact phase_test_zero lam Lam m Lb D B b hsetting σ τ ρ c γ center hρ hc hcenter S K hreal
    ξ z0 v hξ hστ hv sgn hsgn φB hdatum hbound (fun x hx => (hs hx).1)

end


end HypoellipticAleksandrov.KineticAleksandrov.Decay
