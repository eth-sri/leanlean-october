/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Statements.Defs.UnitVolumeStructureConstant
import DOZZ.Statements.Defs.ReflectionDOZZ
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-! The definition `DOZZ.BrownianPath`. -/


open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- A continuous real path indexed by nonnegative time. -/
abbrev BrownianPath := C(ℝ≥0, ℝ)

end DOZZ
