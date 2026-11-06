/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/NineGeometry.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`). No other line was
changed; see docs/PORT-LOG.md.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.CircleExtension
public import OAI.Combinatorics.EuclideanRamsey.CircleSpan
public import Mathlib.RingTheory.AlgebraicIndependent.Basic

@[expose] public section

namespace OAI

/-! Rational parametrization of the unit circle and its coordinate field. -/

noncomputable section
namespace EuclideanRamsey.NineGeometry

def circlePoint (x : ℝ) : Space 2 :=
  CircleConsequence.stereographic (0 : Space 2) 1 x

@[simp] theorem circlePoint_zero (x : ℝ) :
    circlePoint x 0 = (1 - x^2) / (1 + x^2) := by
  simp [circlePoint, CircleConsequence.stereographic]

@[simp] theorem circlePoint_one (x : ℝ) :
    circlePoint x 1 = (2*x) / (1 + x^2) := by
  simp [circlePoint, CircleConsequence.stereographic]

/-- Restriction to the first five points. -/
def firstFive (i : Fin 5) : Fin 9 := ⟨i.val, by omega⟩

theorem firstFive_injective : Function.Injective firstFive := by
  intro i j h
  apply Fin.ext
  simpa only [firstFive] using congrArg (fun k : Fin 9 => k.val) h

end EuclideanRamsey.NineGeometry

end

end OAI
