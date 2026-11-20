module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests

/-!
# Original-time scalar tests

This module supplies smooth compactly supported scalar tests on open original-time intervals.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- Smooth compactly supported scalar tests on the open original-time interval. -/
abbrev OriginalTimeScalarTest (r₀ r₁ : ℝ) :=
  TestFunction
    (⟨Set.Ioo r₀ r₁, isOpen_Ioo⟩ : TopologicalSpace.Opens ℝ) ℝ (⊤ : ℕ∞)

namespace OriginalTimeScalarTest

section
variable {r₀ r₁ : ℝ} (phi : OriginalTimeScalarTest r₀ r₁)
include r₀ r₁ phi

/-- The ordinary scalar derivative of an original-time test. -/
noncomputable def deriv : ℝ → ℝ :=
  _root_.deriv (phi : ℝ → ℝ)

@[simp] theorem deriv_apply (r : ℝ) :
    phi.deriv r = _root_.deriv (phi : ℝ → ℝ) r :=
  rfl

end

end OriginalTimeScalarTest

end HypoellipticAleksandrov.Parabolic.Dirichlet
