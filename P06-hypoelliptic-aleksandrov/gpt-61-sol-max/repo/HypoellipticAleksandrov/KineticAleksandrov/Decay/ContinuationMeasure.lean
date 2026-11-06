module

public import HypoellipticAleksandrov.KineticAleksandrov.MovingKernel
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Continued measures by kernel integration

For a measure `R` on the fixed-time moving fiber `EvolutionState Ω γ s` and a moving-fiber
kernel `K`, the *continued measure* `E` is the ambient measure
`E A = ∫⁻ p, K.master (query s T p) A ∂R` (the killed continuation of `R` from time `s` to
time `T`).  It is characterised by these set integrals on measurable sets alone: this module
proves existence and uniqueness of such an `E` (`exists_unique_continuedMeasure`) without any
integrability, measurability or composition premise beyond the bundled Borel kernel, and
records the elementary mass, support, additivity and domination facts consumed by the
domination and trimming steps.

The integrand query is `evolutionQueryOfState Ω γ s T hsT p`, which unfolds to the source
`movingQuery s T hsT p.1.1 p.1.2 p.2.1` (`evolutionQueryOfState_eq`).
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

open MeasureTheory Set


variable {d : ℕ} {Ω : PDE.VelocityRegion d} {γ : ℝ → PDE.Vec d}

/-- The canonical valid query of a fiber state is the explicit source query
`(s, T, v, z)` with `v` in the moving domain. -/
theorem evolutionQueryOfState_eq (s T : ℝ) (hsT : s ≤ T) (p : EvolutionState Ω γ s) :
    evolutionQueryOfState Ω γ s T hsT p =
      ⟨(s, T, p.1.1, p.1.2), hsT, p.2.1, Set.mem_univ _⟩ := rfl

variable (K : MovingFiberKernel Ω γ) {s T : ℝ} (hsT : s ≤ T)

/-- The kernel from fiber states at time `s` to ambient states: run the master kernel from
`s` to `T`. -/
noncomputable def continuationKernel  :
    ProbabilityTheory.Kernel (EvolutionState Ω γ s) (EvolutionAmbientState d) :=
  ProbabilityTheory.Kernel.comap K.master _
    (measurable_evolutionQueryOfState Ω γ s T hsT)

/-- The continuation kernel evaluated at a fiber state is the master measure of its query. -/
theorem continuationKernel_apply
    (p : EvolutionState Ω γ s) :
    continuationKernel K hsT p = K.master (evolutionQueryOfState Ω γ s T hsT p) := rfl

variable (R : Measure (EvolutionState Ω γ s))

/-- The continued measure of `R`: the integral of the continuation kernel against `R`. -/
noncomputable def continuedMeasure
     : Measure (EvolutionAmbientState d) :=
  R.bind (continuationKernel K hsT)

/-- Set-integral formula for the continued measure on measurable sets. -/
theorem continuedMeasure_apply
     {A : Set (EvolutionAmbientState d)}
    (hA : MeasurableSet A) :
    continuedMeasure K hsT R A =
      ∫⁻ p, K.master (evolutionQueryOfState Ω γ s T hsT p) A ∂R :=
  Measure.bind_apply hA (continuationKernel K hsT).measurable.aemeasurable

/-- Any measure with the displayed set integrals is the continued measure. -/
theorem eq_continuedMeasure_of_apply
     {E : Measure (EvolutionAmbientState d)}
    (hE : ∀ A : Set (EvolutionAmbientState d), MeasurableSet A →
      E A = ∫⁻ p, K.master (evolutionQueryOfState Ω γ s T hsT p) A ∂R) :
    E = continuedMeasure K hsT R :=
  Measure.ext fun A hA => (hE A hA).trans (continuedMeasure_apply K hsT R hA).symm

/-- The continued measure has at most the mass of the initial measure. -/
theorem continuedMeasure_univ_le
     :
    continuedMeasure K hsT R Set.univ ≤ R Set.univ := by
  rw [continuedMeasure_apply K hsT R MeasurableSet.univ]
  calc ∫⁻ p, K.master (evolutionQueryOfState Ω γ s T hsT p) Set.univ ∂R
      ≤ ∫⁻ _p, 1 ∂R := lintegral_mono fun p => K.mass_le_one _
    _ = R Set.univ := by simp

/-- The continued measure of a finite measure is finite. -/
instance isFiniteMeasure_continuedMeasure (K : MovingFiberKernel Ω γ) {s T : ℝ}
    (hsT : s ≤ T) (R : Measure (EvolutionState Ω γ s)) [IsFiniteMeasure R] :
    IsFiniteMeasure (continuedMeasure K hsT R) :=
  ⟨(continuedMeasure_univ_le K hsT R).trans_lt (measure_lt_top R _)⟩

variable (K : MovingFiberKernel Ω γ) {s T : ℝ} (hsT : s ≤ T)

/-- Continuation is additive in the initial measure. -/
theorem continuedMeasure_add
    (R₁ R₂ : Measure (EvolutionState Ω γ s)) :
    continuedMeasure K hsT (R₁ + R₂) =
      continuedMeasure K hsT R₁ + continuedMeasure K hsT R₂ := by
  refine Measure.ext fun A hA => ?_
  rw [Measure.add_apply, continuedMeasure_apply K hsT _ hA,
    continuedMeasure_apply K hsT _ hA, continuedMeasure_apply K hsT _ hA,
    lintegral_add_measure]

/-- Continuation is monotone in the initial measure. -/
theorem continuedMeasure_mono
    {R R' : Measure (EvolutionState Ω γ s)} (h : R ≤ R') :
    continuedMeasure K hsT R ≤ continuedMeasure K hsT R' := by
  refine Measure.le_iff.mpr fun A hA => ?_
  rw [continuedMeasure_apply K hsT _ hA, continuedMeasure_apply K hsT _ hA]
  exact lintegral_mono' h le_rfl

end HypoellipticAleksandrov.KineticAleksandrov.Decay
