module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeBochner
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Reverse-time scalar tests

This module supplies the literal scalar test carrier for the reverse-time
interval and its routine smoothness, support, and integrability consequences.
It deliberately contains no endpoint, weak-derivative, or PDE assertions.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The bundled open set underlying reverse-time scalar tests. -/
def reverseTimeOpenIntervalOpens (T : ℝ) : TopologicalSpace.Opens ℝ :=
  ⟨reverseTimeOpenInterval T, by
    simpa only [reverseTimeOpenInterval] using
      (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) T))⟩

/-- Smooth scalar tests compactly supported in the literal reverse-time interval. -/
abbrev ReverseTimeScalarTest (T : ℝ) : Type _ :=
  TestFunction (reverseTimeOpenIntervalOpens T) ℝ (⊤ : ℕ∞)

namespace ReverseTimeScalarTest
section
variable {T : ℝ} (eta : ReverseTimeScalarTest T)

/-- The ordinary scalar derivative of a reverse-time test. -/
noncomputable def deriv
     : ℝ → ℝ :=
  _root_.deriv (eta : ℝ → ℝ)

@[simp] theorem deriv_apply
    {T : ℝ} (eta : ReverseTimeScalarTest T) (tau : ℝ) :
    eta.deriv tau = _root_.deriv (eta : ℝ → ℝ) tau :=
  rfl

/-- The smoothness packaged in the test carrier. -/
theorem contDiff
     :
    ContDiff ℝ (⊤ : ℕ∞) (eta : ℝ → ℝ) :=
  TestFunction.contDiff eta

/-- The compact support packaged in the test carrier. -/
theorem hasCompactSupport
     :
    HasCompactSupport (eta : ℝ → ℝ) :=
  TestFunction.hasCompactSupport eta

/-- The literal reverse-time support inclusion packaged in the carrier. -/
theorem tsupport_subset
     :
    tsupport (eta : ℝ → ℝ) ⊆ reverseTimeOpenInterval T := by
  exact TestFunction.tsupport_subset eta

/-- A smooth reverse-time test has a smooth ordinary derivative. -/
theorem contDiff_deriv
     :
    ContDiff ℝ (⊤ : ℕ∞) eta.deriv := by
  change ContDiff ℝ (⊤ : ℕ∞) (_root_.deriv (eta : ℝ → ℝ))
  exact (contDiff_infty_iff_deriv.mp eta.contDiff).2

/-- The ordinary derivative of a test has compact support. -/
theorem hasCompactSupport_deriv
     :
    HasCompactSupport eta.deriv := by
  simpa only [deriv] using eta.hasCompactSupport.deriv

/-- A global norm bound for the scalar test function. -/
theorem exists_norm_le
     :
    ∃ C : ℝ, ∀ tau : ℝ, ‖eta tau‖ ≤ C :=
  eta.contDiff.continuous.bounded_above_of_compact_support eta.hasCompactSupport

/-- A global norm bound for the ordinary derivative. -/
theorem exists_norm_deriv_le
     :
    ∃ C : ℝ, ∀ tau : ℝ, ‖eta.deriv tau‖ ≤ C :=
  eta.contDiff_deriv.continuous.bounded_above_of_compact_support
    eta.hasCompactSupport_deriv

/-- Every scalar reverse-time test belongs to every `Lᵖ` over the time measure. -/
theorem memLp
     (p : ℝ≥0∞) :
    MeasureTheory.MemLp (eta : ℝ → ℝ) p (reverseTimeVolume T) := by
  change MeasureTheory.MemLp (eta : ℝ → ℝ) p
    (volume.restrict (reverseTimeOpenInterval T))
  exact (eta.contDiff.continuous.memLp_of_hasCompactSupport
    eta.hasCompactSupport).restrict (reverseTimeOpenInterval T)

/-- The ordinary derivative belongs to every `Lᵖ` over the time measure. -/
theorem memLp_deriv
     (p : ℝ≥0∞) :
    MeasureTheory.MemLp eta.deriv p (reverseTimeVolume T) := by
  change MeasureTheory.MemLp eta.deriv p
    (volume.restrict (reverseTimeOpenInterval T))
  exact (eta.contDiff_deriv.continuous.memLp_of_hasCompactSupport
    eta.hasCompactSupport_deriv).restrict (reverseTimeOpenInterval T)

/-- A scalar reverse-time test is integrable over the time measure. -/
theorem integrable
     :
    MeasureTheory.Integrable (eta : ℝ → ℝ) (reverseTimeVolume T) :=
  MeasureTheory.memLp_one_iff_integrable.mp (eta.memLp (1 : ℝ≥0∞))
end

end ReverseTimeScalarTest

end HypoellipticAleksandrov.Parabolic.Dirichlet
