module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Realization
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Uniqueness of supplied terminal-evolution realizations

Two supplied realizations `(S, K)` and `(S', K')` of the same terminal-evolution data are
equal.  Classical uniqueness identifies the operators on smooth compactly supported data; the
integral representation then identifies the finite kernel measures against all smooth
compactly supported tests in the open terminal fiber, which determine finite Borel measures.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

open MeasureTheory Set


variable {d : ℕ} {Ω : PDE.VelocityRegion d} {γ : ℝ → PDE.Vec d}

/-- A smooth `[0,1]`-valued function, viewed as a bounded Borel datum. -/
def smoothTestDatum (φ : EvolutionAmbientState d → ℝ) (hφ : ContDiff ℝ PDE.smoothOrder φ)
    (hr : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) : BoundedBorel (EvolutionAmbientState d) :=
  ⟨φ, hφ.continuous.measurable, 1, zero_le_one, fun x => by
    rw [abs_of_nonneg (hr x).1]; exact (hr x).2⟩

/-- Two realizations give the same operator value on every smooth compact datum. -/
theorem realizes_fiber_integral_eq {B : FullKineticCoefficient d} {b : PDE.VectorField d}
    {S S' : TerminalOperatorFamily Ω γ} {K K' : MovingFiberKernel Ω γ}
    (hΩ : MeasurableSet Ω)
    (h : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (h' : RealizesTerminalEvolution Ω γ hΩ B b S' K')
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ)
    (F : BoundedBorel (EvolutionAmbientState d)) (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
    ∫ q, F q.1 ∂K.fiberKernel hΩ σ τ hστ p = ∫ q, F q.1 ∂K'.fiberKernel hΩ σ τ hστ p := (Exists.casesOn (h.left τ F hF) fun u h_1 =>
  And.casesOn h_1 fun hu right =>
    And.casesOn right fun hup huniq =>
      Exists.casesOn (h'.left τ F hF) fun u' h_2 =>
        And.casesOn h_2 fun hu' right =>
          And.casesOn right fun hup' right =>
            Trans.trans
              (Trans.trans
                (Trans.trans
                  (Trans.trans (Eq.symm (h.right.left σ τ hστ p (terminalStateDatum F))) (Eq.symm (hup σ hστ p)))
                  (Eq.symm (huniq u' hu' ⟨hστ, subset_closure p.property.left⟩)))
                (hup' σ hστ p))
              (h'.right.left σ τ hστ p (terminalStateDatum F)))

/-- The ambient master integral of a measurable function is the fiber integral of its
restriction. -/
theorem integral_master_eq_fiber (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ) (F : EvolutionAmbientState d → ℝ)
    (hF : Measurable F) :
    ∫ x, F x ∂K.master (evolutionQueryOfState Ω γ σ τ hστ p) =
      ∫ q, F q.1 ∂K.fiberKernel hΩ σ τ hστ p := by
  rw [← K.map_fiberKernel_eq_master hΩ σ τ hστ p,
    integral_map measurable_subtype_coe.aemeasurable hF.aestronglyMeasurable]

section
variable {B : FullKineticCoefficient d} {b : PDE.VectorField d} {S S' : TerminalOperatorFamily Ω γ} {K K' : MovingFiberKernel Ω γ} (hΩo : IsOpen Ω) (h : RealizesTerminalEvolution Ω γ hΩo.measurableSet B b S K) (h' : RealizesTerminalEvolution Ω γ hΩo.measurableSet B b S' K')

include h h'
/-- Master kernels of two realizations of the same data agree. -/
theorem realizes_master_eq  :
    K.master = K'.master := by
  ext q : 1
  have hU : IsOpen (evolutionStateSet Ω γ q.1.2.1) :=
    (isOpen_movingDomain hΩo _).prod isOpen_univ
  have hq : evolutionQueryOfState Ω γ q.1.1 q.1.2.1 q.2.1 ⟨q.1.2.2, q.2.2⟩ = q := rfl
  have : ProbabilityTheory.IsFiniteKernel K.master := ⟨1, ENNReal.one_lt_top, fun q => by
    exact K.mass_le_one q⟩
  have : ProbabilityTheory.IsFiniteKernel K'.master := ⟨1, ENNReal.one_lt_top, fun q => by
    exact K'.mass_le_one q⟩
  have hz : ∀ m : Measure (EvolutionAmbientState d),
      m.restrict (evolutionStateSet Ω γ q.1.2.1) = m → m (evolutionStateSet Ω γ q.1.2.1)ᶜ = 0 := by
    intro m hm
    rw [← hm, Measure.restrict_apply hU.measurableSet.compl, compl_inter_self, measure_empty]
  refine measure_eq_of_smooth_integral_eq hU (hz _ (K.terminal_support q))
    (hz _ (K'.terminal_support q)) ?_
  intro φ hφ hφc hφU hφr
  have hF : IsSmoothCompactTerminalDatum Ω γ q.1.2.1 (smoothTestDatum φ hφ hφr) :=
    ⟨hφ, hφc, hφU⟩
  have key := realizes_fiber_integral_eq hΩo.measurableSet h h' q.1.1 q.1.2.1 q.2.1
    ⟨q.1.2.2, q.2.2⟩ _ hF
  rw [← hq]
  rw [integral_master_eq_fiber K hΩo.measurableSet _ _ _ _ φ hφ.continuous.measurable,
    integral_master_eq_fiber K' hΩo.measurableSet _ _ _ _ φ hφ.continuous.measurable]
  exact key

/-- Terminal evolution for open base domain: the kernel is unique. -/
theorem realizes_kernel_unique  : K = K' := by
  have hm := realizes_master_eq hΩo h h'
  obtain ⟨m, hs, hl⟩ := K
  obtain ⟨m', hs', hl'⟩ := K'
  cases hm
  rfl
end


/-- Source uniqueness extends from compact smooth data to kernels and all Borel data. -/
theorem terminalEvolution_unique {d : ℕ} (Ω : PDE.VelocityRegion d)
    (γ : ℝ → PDE.Vec d) (hΩ : IsAdmissibleEvolutionDomain Ω)
    (B : FullKineticCoefficient d) (b : PDE.VectorField d)
    (S S' : TerminalOperatorFamily Ω γ) (K K' : MovingFiberKernel Ω γ)
    (h : RealizesTerminalEvolution Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ) B b S K)
    (h' : RealizesTerminalEvolution Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ) B b S' K') :
    S = S' ∧ K = K' := by
  have hΩo := isOpen_of_isAdmissibleEvolutionDomain hΩ
  have hK := realizes_kernel_unique hΩo h h'
  subst hK
  refine ⟨?_, rfl⟩
  funext σ τ hστ
  apply LinearMap.ext
  intro f
  apply BoundedBorel.ext
  intro p
  rw [h.2.1 σ τ hστ p f, h'.2.1 σ τ hστ p f]

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
