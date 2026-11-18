module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitFunctionalProbes
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonLinear
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitFunctionalDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalFunctionalExtension

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic SectionTwo TheoremA Evolution
open scoped Topology CompactlySupported

/-- The actual scalar kinetic source of a probe, as bounded Borel data. -/
def exitProbeOperatorDatum {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (f : exitProbeSubmodule) : BoundedBorel Point :=
  ⟨forwardScalarOperator A.a (exitProbePhysical f), by
    have hm := (exitProbe_operator_smooth_compact A f).1.continuous.measurable.comp
      reconstructionPhysicalHomeomorph.symm.continuous.measurable
    have heq : forwardScalarOperator A.a (exitProbePhysical f) =
        transportedOperator (evolutionCoefficient A.a) (identityDrift 1) f.1 ∘
          reconstructionPhysicalHomeomorph.symm := funext (exitProbePhysical_operator A f)
    rw [heq]
    exact hm, by
    obtain ⟨M, hM⟩ := exitProbePhysical_bounded_source A f
    exact ⟨max M 0, le_max_right _ _, fun p => (hM p).2.trans (le_max_left _ _)⟩⟩

/-- The homogeneous value is the actual test value plus its actual kinetic-source integral. -/
def exitProbeValue {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (H : Interval)
    (E : StripEvolution H) (T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (f : exitProbeSubmodule) : ℝ :=
  exitProbePhysical f e.1 + ∫ p, forwardScalarOperator A.a (exitProbePhysical f) p
    ∂stripGreenOfKernel H E.2 T e

private theorem probe_operator_add {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (f g : exitProbeSubmodule) :
    forwardScalarOperator A.a (exitProbePhysical (f + g)) =
      fun p => forwardScalarOperator A.a (exitProbePhysical f) p +
        forwardScalarOperator A.a (exitProbePhysical g) p := by
  funext p
  have h := comparison_forwardOperator_add
    (exitProbePhysical_isKineticC112On f univ isOpen_univ)
    (exitProbePhysical_isKineticC112On g univ isOpen_univ) (autonomousCoefficient A.a) (mem_univ p)
  simp only [forwardOperator_autonomous] at h
  exact h

private theorem probe_operator_smul {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (c : ℝ) (f : exitProbeSubmodule) :
    forwardScalarOperator A.a (exitProbePhysical (c • f)) =
      fun p => c * forwardScalarOperator A.a (exitProbePhysical f) p := by
  funext p
  have h := comparison_forwardOperator_const_mul
    (exitProbePhysical_isKineticC112On f univ isOpen_univ) c (autonomousCoefficient A.a)
      (mem_univ p)
  simp only [forwardOperator_autonomous] at h
  exact h

/-- Homogeneous probe values form a linear functional before boundary restriction. -/
def exitProbeValueLinear {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (H : Interval)
    (E : StripEvolution H) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    exitProbeSubmodule →ₗ[ℝ] ℝ where
  toFun := exitProbeValue A H E T e
  map_add' f g := by
    unfold exitProbeValue
    rw [probe_operator_add]
    have hf : Integrable (forwardScalarOperator A.a (exitProbePhysical f))
        (stripGreenOfKernel H E.2 T e) :=
      stripGreen_integrable_boundedBorel H E.2 T e (exitProbeOperatorDatum A f)
    have hg : Integrable (forwardScalarOperator A.a (exitProbePhysical g))
        (stripGreenOfKernel H E.2 T e) :=
      stripGreen_integrable_boundedBorel H E.2 T e (exitProbeOperatorDatum A g)
    rw [integral_add hf hg]
    change exitProbePhysical f e.1 + exitProbePhysical g e.1 + _ = _
    ring
  map_smul' c f := by
    unfold exitProbeValue
    rw [probe_operator_smul, integral_const_mul]
    change c * exitProbePhysical f e.1 + _ = c * _
    ring





/-- The actual homogeneous values extend to exactly one positive contraction functional
on all compactly supported continuous exit data. -/
theorem existsUnique_stripBoundaryFunctional
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    ∃! ℓ : C_c(stripClosedExit H T, ℝ) →ₚ[ℝ] ℝ,
      (∀ (f : C_c(stripClosedExit H T, ℝ)) (c : ℝ), 0 ≤ c →
        (∀ p, |f p| ≤ c) → |ℓ f| ≤ c) ∧
      ∀ f : exitProbeSubmodule, ℓ (exitProbeCcLinear H T f) = exitProbeValueLinear A H E T e f    := by
  have exitProbeValue_le_of_boundary (f : exitProbeSubmodule) (c : ℝ) (hbd : ∀ p ∈ stripClosedExit H T, exitProbePhysical f p ≤ c) :
      exitProbeValue A H E T e f ≤ c := by
    obtain ⟨M, hM⟩ := exitProbePhysical_bounded_source A f
    simpa only [exitProbeValue, integral_neg, sub_neg_eq_add] using (reconstruction_boundary_comparison hH hlam hLam A H E hE (e.1.time - 1) T e (by linarith) (exitProbePhysical f) (exitProbePhysical_isKineticC112On f _ (isOpen_reconstructionStrip H _ T)) (exitProbePhysical_continuous_compact f).1 ⟨M, fun p _ => hM p⟩ M (fun p => (hM p).1) c hbd)
  have exitProbeValueLinear_nonneg (f : exitProbeSubmodule) (hbd : ∀ p, 0 ≤ exitProbeCcLinear H T f p) :
      0 ≤ exitProbeValueLinear A H E T e f := by
    have hn := exitProbeValue_le_of_boundary (-f) 0
      (fun p hp => by
        exact neg_nonpos.mpr (hbd ⟨p, hp⟩))
    have heq := (exitProbeValueLinear A H E T e).map_neg f
    change exitProbeValue A H E T e (-f) = -exitProbeValue A H E T e f at heq
    rw [heq] at hn
    exact neg_nonpos.mp hn
  have exitProbeValueLinear_bound (f : exitProbeSubmodule) (c : ℝ) (_hc : 0 ≤ c) (hbd : ∀ p, |exitProbeCcLinear H T f p| ≤ c) :
      |exitProbeValueLinear A H E T e f| ≤ c := by
    have hn := exitProbeValue_le_of_boundary (-f) c
      (fun p hp => by
        exact (neg_le_abs _).trans (hbd ⟨p, hp⟩))
    have heq := (exitProbeValueLinear A H E T e).map_neg f
    change exitProbeValue A H E T e (-f) = -exitProbeValue A H E T e f at heq
    rw [heq] at hn
    exact abs_le.mpr ⟨neg_le.mp hn, (exitProbeValue_le_of_boundary f c (fun p hp => (le_abs_self _).trans (hbd ⟨p, hp⟩)))⟩
  obtain ⟨ℓ, hbd, hagree⟩ := exists_positive_extension_of_dense (exitProbeCcLinear H T)
    (exitProbeValueLinear A H E T e)
    (exitProbeValueLinear_bound)
    (exitProbeValueLinear_nonneg)
    (exitProbeCc_sq H T) (exitProbeCc_dense H T)
  refine ⟨ℓ, ⟨hbd, hagree⟩, fun k hk => ?_⟩
  exact PositiveLinearMap.ext (fun f => LinearMap.congr_fun (eq_of_bounded_of_dense (exitProbeCcLinear H T) k.toLinearMap ℓ.toLinearMap hk.1 hbd (fun f => (hk.2 f).trans (hagree f).symm) (exitProbeCc_dense H T)) f)

/-- The strip boundary functional is chosen only from its proved unique characterization. -/
def stripBoundaryFunctional
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    C_c(stripClosedExit H T, ℝ) →ₚ[ℝ] ℝ :=
  (existsUnique_stripBoundaryFunctional hH hlam hLam A H E hE T e).exists.choose

/-- Full contraction and smooth-probe characterization of the unique boundary functional. -/
theorem stripBoundaryFunctional_spec
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    (∀ (f : C_c(stripClosedExit H T, ℝ)) (c : ℝ), 0 ≤ c → (∀ p, |f p| ≤ c) →
      |stripBoundaryFunctional hH hlam hLam A H E hE T e f| ≤ c) ∧
    ∀ f : exitProbeSubmodule, stripBoundaryFunctional hH hlam hLam A H E hE T e
      (exitProbeCcLinear H T f) = exitProbeValueLinear A H E T e f :=
  (existsUnique_stripBoundaryFunctional hH hlam hLam A H E hE T e).exists.choose_spec

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

