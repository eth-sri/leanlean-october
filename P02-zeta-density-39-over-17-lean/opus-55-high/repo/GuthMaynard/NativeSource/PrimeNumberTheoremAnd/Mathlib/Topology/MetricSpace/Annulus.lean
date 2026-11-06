/-
Copyright (c) 2024 James Sundstrom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Sundstrom
-/
module

public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Order.Interval.Set.LinearOrder
public import Mathlib.Order.SuccPred.IntervalSucc
public import Mathlib.Topology.MetricSpace.Basic

/-!
# Annulus

In this file we define annuli in (pseudo)(e)metric spaces.

For a point `x` and radii `r R`, the set `Metric.annulusIoo x r R` consists of all `y` such that
`dist y x ∈ Set.Ioo r R`. We provide analogous definitions for `Ioc`, `Ico`, `Icc`, and also for the
half-infinite intervals `Ioi`, `Ici` (these are complements of `closedBall`/`ball`).

We also define `Metric.eannulusIxx` using `edist` (hence radii in `ℝ≥0∞`), and relate these to
`Metric.annulusIxx` via `ENNReal.ofReal` when `edist = ENNReal.ofReal ∘ dist`.

## Tags

annulus
-/

@[expose] public section

open Set

open scoped ENNReal

namespace Metric

variable {X : Type*} [PseudoMetricSpace X]

/-! ### Annulus defined using `dist` -/

variable {x : X} {r R : ℝ}

/-! ### Pairwise disjoint annuli over succ orders -/

open scoped Function -- required for scoped `on` notation

variable {ι : Type*} [LinearOrder ι] [SuccOrder ι]

end Metric

namespace Metric

variable {X : Type*} [PseudoEMetricSpace X]

/-! ### Annulus defined using `edist` -/

/-! ### Pairwise disjoint eannuli over succ orders -/

open scoped Function -- required for scoped `on` notation

variable {ι : Type*} [LinearOrder ι] [SuccOrder ι]

end Metric

namespace Metric

/-! ### `ENNReal.ofReal` bridge lemmas in a pseudo metric space -/

variable {X : Type*} [PseudoMetricSpace X]
variable {x : X} {r R : ℝ}

end Metric
