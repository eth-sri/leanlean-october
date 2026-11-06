/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/CircleInterpolation.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`). No other line was
changed; see docs/PORT-LOG.md.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.CircleGeometry

@[expose] public section

namespace OAI

/- The secant equations and quadratic isolators have coefficients in the coordinate field. -/
noncomputable section
namespace EuclideanRamsey.CircleConsequence

def secantValue {s : ℕ} (a : Fin s → Space 2) (i j k : Fin s) : Coeff a :=
  (coordinate a j 0-coordinate a i 0)*(coordinate a k 1-coordinate a i 1) -
  (coordinate a j 1-coordinate a i 1)*(coordinate a k 0-coordinate a i 0)

/-- Nonzero evaluation follows from actual planar circle equations. -/
theorem secantValue_ne_zero {s : ℕ} (a : Fin s → Space 2)
    (ha : Function.Injective a) (c : Space 2) (R : ℝ)
    (hc : ∀ m, (a m 0-c 0)^2 + (a m 1-c 1)^2 = R)
    (i j k : Fin s) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    secantValue a i j k ≠ 0 := by
  have different (u v : Fin s) (huv : u ≠ v) :
      a u 0 ≠ a v 0 ∨ a u 1 ≠ a v 1 := by
    by_contra h
    push Not at h
    apply huv
    apply ha
    ext q
    fin_cases q <;> simp_all
  have h := secant_nonzero (a i 0) (a i 1) (a j 0) (a j 1)
    (a k 0) (a k 1) (c 0) (c 1) R (hc i) (hc j) (hc k)
    (different i j hij) (different i k hik) (different j k hjk)
  intro hz
  apply h
  have he := congrArg (fun z : Coeff a => (z : ℝ)) hz
  simpa [secantValue, coordinate] using he

end EuclideanRamsey.CircleConsequence

end

end OAI
