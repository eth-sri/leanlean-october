module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.DecayIteration
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierPremises

/-! # Whole-space Fourier decay from the exact source predecessors

Constants precede every coefficient and supplied realization. The consumer headline
returns the Green family proposition, with only the unit-block estimate and the terminal
evolution statement as hypotheses.
-/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

variable (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)

/-- Source case W exponential decay for every characterized Fourier projection. -/
theorem fourier_decay_whole_space_of_unitBlock 
    (hEvol : IterationEvolutionStatement)
    (hblock : UnitBlockStatementW d hd lam Lam 1 1 hlam hlamLam zero_lt_one le_rfl) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (B : CoefficientField d), IsSectionTwoCoefficient lam Lam B →
      ∀ (S : TerminalOperatorFamily univ stationary) (K : MovingFiberKernel univ stationary),
        RealizesTerminalEvolution univ stationary MeasurableSet.univ
          (zIndependentCoefficient B) id S K →
      ∀ (σ τ : ℝ), σ < τ →
      ∀ (v ξ : PDE.Vec d) (q : EvolutionQuery univ stationary), q.1 = (σ, τ, v, 0) →
      ∀ (ν : ComplexMeasure (PDE.Vec d)), IsFourierProjection K q ξ ν →
        TV ν ≤ C * Real.exp (-c * (τ - σ) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ)) := by
  obtain ⟨L, δ, hL, hδ, hδ1, hiter⟩ :=
    fourier_decay_frequency_iteration_of_unitBlock d hd lam Lam hlam hlamLam hEvol hblock
  obtain ⟨hC1, hc⟩ := decay_constants hδ hδ1 hL
  refine ⟨(1 - δ)⁻¹, -Real.log _ / L, lt_of_lt_of_le zero_lt_one hC1, hc, ?_⟩
  intro B hB S K hreal σ τ hστ v ξ q hq ν hν
  by_cases hξ : ξ = 0
  · subst ξ
    have he := iteration_projection_eq K σ τ hστ.le v 0 q hq ν hν
    rw [he]
    have ht := ENNReal.toReal_mono ENNReal.one_ne_top
      (fourierKernel_totalVariation_le_one K σ τ hστ.le 0 v)
    have hz : PDE.vecEuclideanNorm (0 : PDE.Vec d) = 0 :=
      PDE.vecEuclideanNorm_eq_zero_iff.mpr rfl
    simp only [hz, Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0), mul_zero,
      Real.exp_zero, mul_one]
    have htv : TV (fourierKernel K σ τ hστ.le 0 v) ≤ 1 := by
      simp_all
    linarith
  grind

/-- The Green family, conditional on the unit-block estimate and the terminal evolution statement.
-/
theorem fourierDecayFamily_of_unitBlock 
    (hEvol : IterationEvolutionStatement)
    (hblock : UnitBlockStatementW d hd lam Lam 1 1 hlam hlamLam zero_lt_one le_rfl) :
    HypoellipticAleksandrov.KineticAleksandrov.Green.FourierDecayFamily d lam Lam := by
  obtain ⟨C, c, hC, hc, hdecay⟩ :=
    fourier_decay_whole_space_of_unitBlock d hd lam Lam hlam hlamLam hEvol hblock
  refine ⟨C, c, hC, hc, ?_⟩
  intro B hB S K hreal σ τ hστ v ξ
  have ht := hdecay B hB S K hreal σ τ hστ v ξ
    _ rfl _ (fourierKernel_spec K σ τ hστ.le ξ v)
  have hf  :=
    ne_of_lt ((fourierKernel_totalVariation_le_one K σ τ hστ.le ξ v).trans_lt
      ENNReal.one_lt_top)
  calc
    _ = ENNReal.ofReal _ :=
      (ENNReal.ofReal_toReal hf).symm
    _ ≤ ENNReal.ofReal _ :=
      ENNReal.ofReal_le_ofReal ht
    _ = _ := by ring

end HypoellipticAleksandrov.KineticAleksandrov.Decay
