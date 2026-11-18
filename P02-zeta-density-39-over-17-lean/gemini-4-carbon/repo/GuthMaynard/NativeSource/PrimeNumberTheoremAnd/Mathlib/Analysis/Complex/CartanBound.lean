/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# Cartan bounds for Hadamard factorization

Probabilistic-radius and averaging lemmas for the minimum-modulus step in the intrinsic Hadamard
pipeline. The basic pointwise input is

`log⁺ (1 / |1 - t|) ≤ √(2 / |1 - t|)`,

which majorizes the logarithmic singularity on dyadic intervals.

## References

* [tao246bComplexAnalysis] for the disk and averaging viewpoint
* [MR886677] for disk automorphisms and canonical factors on the unit disk
* [boas1954] and [levin1980] for the minimum-modulus estimates used in Hadamard factorization
-/

@[expose] public section

namespace Complex
namespace CartanBound

open Real MeasureTheory intervalIntegral
open scoped Topology ENNReal

/-!
### Pointwise bound for the logarithmic singularity

Used as an integrable majorant when averaging `log⁺ (1 / |1 - t|)` on dyadic intervals.
-/

/-! ### A radial majorant for the logarithmic singularity on a circle -/

/-! ### A coarse dyadic-interval bound for the singularity average -/

/-- The one-dimensional logarithmic singularity used in the Cartan/dyadic averaging argument. -/
noncomputable def φ (t : ℝ) : ℝ :=
  log⁺ (1 / |1 - t|)

/-!
### Bridge lemma: from the 1D singularity `φ` to a complex lower bound

On a circle `‖u‖ = r`, the quantity `log ‖1 - u/a‖` is bounded below in terms of `φ(r/‖a‖)`.
This is the local estimate in the probabilistic-radius argument.
-/

/-- The integral of the square-root majorant for `φ` on `[1/4, 4]`. -/
noncomputable def K : ℝ :=
  ∫ (t : ℝ) in (1 / 4 : ℝ)..(4 : ℝ), Real.sqrt (2 / |1 - t|) ∂volume

/-!
### A “good radius” lemma (probabilistic-radius / Cartan averaging)

This is the abstract selection principle used in the dyadic averaging: if an averaged singularity
kernel has controlled integral on `[R,2R]`, then there exists a radius `r ∈ (R,2R]` where the
pointwise sum is controlled.
-/

open scoped BigOperators

end CartanBound
end Complex
