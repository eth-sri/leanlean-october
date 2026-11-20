module

public import QPBT.Games.Defs
public import QPBT.Upstream
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! Applying positive unital additive maps to the effects of a measurement. -/

@[expose] public section

open scoped MatrixOrder ComplexOrder
open MIPStarRE.Quantum

namespace MIPStarRE.Quantum.Measurement

variable {α β I J : Type*} [Fintype α] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

section

variable (M : Measurement α I) (f : Op I →+ Op J) (h₁ : f 1 = 1)
    (hpos : ∀ ⦃A⦄, 0 ≤ A → 0 ≤ f A)
include M f h₁ hpos

/-- A positive unital additive map takes POVMs to POVMs. -/
def mapEffects : Measurement α J :=
  ofSumEqOne (fun a => f (M.effect a)) (fun a => hpos (M.pos a))
    (by rw [← map_sum, M.sum_eq_one, h₁])

@[simp] theorem mapEffects_effect (a : α) :
    (M.mapEffects f h₁ hpos).effect a = f (M.effect a) := rfl

end

/-- The map of effects commutes with coarse-graining. -/
theorem mapEffects_postprocess [Fintype β] [DecidableEq α] [DecidableEq β]
    (M : Measurement α I) (f : Op I →+ Op J) (h₁ : f 1 = 1)
    (hpos : ∀ ⦃A⦄, 0 ≤ A → 0 ≤ f A) (g : α → β) :
    (M.mapEffects f h₁ hpos).postprocess g = (M.postprocess g).mapEffects f h₁ hpos := by
  apply Measurement.ext
  intro b
  simp only [postprocess_effect, mapEffects_effect, map_sum]

end MIPStarRE.Quantum.Measurement

namespace MIPStarRE.QPBT

variable {α I J : Type*} [Fintype α] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

/-- An effect map that preserves squares also preserves projectivity. -/
theorem Measurement.mapEffects_isProjective (M : Quantum.Measurement α I)
    (hM : Measurement.IsProjective M) (f : Op I →+ Op J) (h₁ : f 1 = 1)
    (hpos : ∀ ⦃A⦄, 0 ≤ A → 0 ≤ f A) (hsq : ∀ A, f (A * A) = f A * f A) :
    Measurement.IsProjective (M.mapEffects f h₁ hpos) := fun a =>
  ⟨by rw [IsIdempotentElem, Quantum.Measurement.mapEffects_effect, ← hsq, (hM a).isIdempotentElem.eq],
    (Matrix.nonneg_iff_posSemidef.mp ((M.mapEffects f h₁ hpos).pos a)).isHermitian.isSelfAdjoint⟩

end MIPStarRE.QPBT
