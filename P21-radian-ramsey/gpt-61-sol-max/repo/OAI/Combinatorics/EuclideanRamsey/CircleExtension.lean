/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/CircleExtension.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`). No other line was
changed; see docs/PORT-LOG.md.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.CircleGeometry
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

namespace OAI
noncomputable section
namespace EuclideanRamsey.CircleConsequence

/-- Rational parametrization of a genuine radius-r circle. -/
def stereographic (c : Space 2) (r t : ℝ) : Space 2 :=
  c + r • WithLp.toLp 2 ![(1-t^2)/(1+t^2), (2*t)/(1+t^2)]

end EuclideanRamsey.CircleConsequence

end

end OAI
