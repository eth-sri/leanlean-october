/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Statements.Defs.Distr
import DOZZ.Statements.Defs.ExtendedSeiberg3
import DOZZ.Statements.Defs.IsEquatorGFF
import DOZZ.Statements.Defs.IsGMCOf
import DOZZ.Statements.Defs.NormPlus
import DOZZ.Statements.Defs.Q
import DOZZ.Statements.Defs.StructureConstant
import DOZZ.Statements.Defs.UnitVolumeStructureConstant
import DOZZ.Statements.GMC.CoulombMass
import DOZZ.Statements.Brownian.BrownianPath
import DOZZ.Statements.Brownian.IsReflectionData
import DOZZ.Statements.Brownian.IsSourceLateralProjection
import DOZZ.Statements.Brownian.ReflectionBarR
import DOZZ.Statements.Brownian.ReflectionExponent
import DOZZ.Statements.Brownian.ReflectionPoleFree
import DOZZ.Statements.Brownian.ReflectionR
import Mathlib.Analysis.Analytic.Basic

/-! The definition `DOZZ.nPointSExp`. -/


open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The charge sum in the N-insertion zero-mode exponent. -/
noncomputable def nPointSExp {N : ℕ} (γ : ℝ) (α : Fin N → ℝ) : ℝ :=
  ((∑ i : Fin N, α i) - 2 * Q γ) / γ

end DOZZ
