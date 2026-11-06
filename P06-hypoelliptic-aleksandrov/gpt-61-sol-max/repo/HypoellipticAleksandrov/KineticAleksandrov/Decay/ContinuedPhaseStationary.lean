module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.ContinuedPhaseLocalization
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonEvolution
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Decay.MinorantScaling
import Mathlib.Tactic.FunProp

/-! # Phase localization in a stationary ball with arbitrary center -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory

open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

variable (d : ℕ) (lam Lam : ℝ) (m Lb : ℝ) (D : PDE.VelocityRegion d) (B : CoefficientField d) (b : PDE.Vec d → PDE.Vec d) (hsetting : SourceSetting lam Lam m Lb D B b) (σ τ ρ : ℝ) (c : PDE.Vec d) (hρ : 0 < ρ) (S : TerminalOperatorFamily (PDE.euclideanBall c ρ) stationary) (K : MovingFiberKernel (PDE.euclideanBall c ρ) stationary) (hreal : RealizesTerminalEvolution (PDE.euclideanBall c ρ) stationary (PDE.isOpen_euclideanBall c ρ).measurableSet (zIndependentCoefficient B) b S K) (ξ z0 v : PDE.Vec d) (hξ : PDE.vecNormSq ξ = 1) (hστ : σ ≤ τ) (hv : v ∈ movingDomain (PDE.euclideanBall c ρ) stationary σ)

include hsetting hρ hreal hξ
/-- Smooth forbidden-phase tests have zero integral against the supplied moving kernel. -/
theorem stationary_phase_test_zero
    (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1)
    (φ : BoundedBorel (EvolutionAmbientState d))
    (hφ : IsSmoothCompactTerminalDatum (PDE.euclideanBall c ρ)
      stationary τ φ)
    (hbound : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hs : tsupport (φ : EvolutionAmbientState d → ℝ) ⊆
      {x | 0 < sgn * (phaseCoordinate ξ z0 x - phaseCenter ξ b (fun _ => c) σ τ) -
        Lb * ρ * (τ - σ)}) :
    ∫ x, φ x ∂K.master (movingQuery σ τ hστ v z0 hv) = 0 := by


  let p : EvolutionState (PDE.euclideanBall c ρ) stationary σ := ⟨(v, z0), hv, mem_univ _⟩
  have hi : ∫ x, φ x ∂K.master (movingQuery σ τ hστ v z0 hv) =
      ∫ x, φ x.1 ∂K.fiberKernel (PDE.isOpen_euclideanBall c ρ).measurableSet σ τ hστ p :=
    integral_master_eq_fiber K _
      σ τ hστ p φ φ.measurable
  by_cases ht : σ = τ
  · subst τ
    rw [hi, hreal.2.2.1 σ]
    simp only [ProbabilityTheory.Kernel.id_apply, integral_dirac]
    change φ (v, z0) = 0
    by_contra hn
    have hs' := hs (subset_tsupport _
      (show (v, z0) ∈ Function.support (φ : EvolutionAmbientState d → ℝ) from hn))
    simp only [Set.mem_ofPred_eq, phaseCoordinate, phaseCenter, sub_self,
      PDE.vecDot, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero, intervalIntegral.integral_same, sub_zero, lt_self_iff_false]
      at hs'
  ·
    obtain ⟨u, hu, hup, -⟩ := hreal.1 τ φ hφ

    have hmove : ∀ t, movingDomain (PDE.euclideanBall 0 ρ) (fun _ => c) t =
        movingDomain (PDE.euclideanBall c ρ) stationary t := by
      intro t
      rw [movingDomain_stationary]
      ext w
      rw [mem_movingDomain_euclideanBall_iff]
      simp only [add_zero, PDE.euclideanBall, PDE.euclideanSqDist, mem_ofPred_eq]



    have hnonpos := classical_phase_test_nonpos B b (fun _ => c) σ τ Lb ρ (lt_of_le_of_ne hστ ht) hρ ξ z0 hξ
      hsetting.2.2.2.2.1.1 continuous_const (by
          intro t v

          exact posSemidef_of_hasEverywhereLoewnerBounds hsetting.1.1.le ((sectionTwoCoefficient_fullBounds lam Lam B hsetting.1).2.2) t v 0) sgn hsgn
      φ (by
          simpa only [IsSmoothCompactTerminalDatum, evolutionStateSet, hmove] using hφ) hbound hs u (by
          simpa only [IsClassicalTerminalSolution, evolutionPastClosedCylinder,
            evolutionPastInteriorRaw, evolutionPastOpenCylinder, evolutionTerminalClosure,
            evolutionLateralFrontier, hmove] using hu) v (by
          rw [hmove]
          exact hv)

    apply le_antisymm
    · exact (show ∫ x, φ x ∂K.master (movingQuery σ τ hστ v z0 hv) =
        u ⟨σ, v, z0⟩ by
        rw [hi]
        exact (hreal.2.1 σ τ hστ p (terminalStateDatum φ)).symm.trans (hup σ hστ p).symm).trans_le hnonpos
    · exact integral_nonneg (fun x => (hbound x).1)


/-- The supplied moving kernel is concentrated in the source closed phase strip. -/
theorem stationary_phase_localization
    : ∀ᵐ x ∂K.master (movingQuery σ τ hστ v z0 hv),
      |phaseCoordinate ξ z0 x - phaseCenter ξ b (fun _ => c) σ τ| ≤ Lb * ρ * (τ - σ) := by
  let μ := K.master (movingQuery σ τ hστ v z0 hv)
  have hfinite : IsFiniteMeasure μ := ⟨(K.mass_le_one _).trans_lt ENNReal.one_lt_top⟩
  let U := evolutionStateSet (PDE.euclideanBall c ρ) stationary τ
  have hU : IsOpen U := (isOpen_movingDomain (PDE.isOpen_euclideanBall c ρ) τ).prod
    isOpen_univ


  apply ae_phase_strip_of_forbidden_tests hU (by
      have hr : μ.restrict U = μ := K.terminal_support _
      calc
        μ Uᶜ = (μ.restrict U) Uᶜ := by rw [hr]
        _ = μ (Uᶜ ∩ U) := Measure.restrict_apply hU.measurableSet.compl
        _ = 0 := by simp) (show _ by
      unfold phaseCoordinate PDE.vecDot
      simp only [Pi.sub_apply]
      fun_prop) (Lb * ρ * (τ - σ))
  intro sgn hsgn φ hφ hc hs hbound
  let φB := smoothTestDatum φ hφ hbound
  have hdatum : IsSmoothCompactTerminalDatum (PDE.euclideanBall c ρ)
      stationary τ φB := ⟨hφ, hc, fun x hx => (hs hx).2⟩
  exact stationary_phase_test_zero d lam Lam
    m Lb D B b hsetting σ τ ρ c hρ S K hreal
    ξ z0 v hξ hστ hv sgn hsgn φB hdatum hbound (fun x hx => (hs hx).1)


end HypoellipticAleksandrov.KineticAleksandrov.Decay
