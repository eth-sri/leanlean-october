module
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_STATIONARY_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import Mathlib

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # The actual signed carrier phase and its derivatives

This narrow extraction does not assert a source or amplitude factorization.
Both real signs of the frequency parameter b remain unrestricted.
-/
noncomputable section
open Complex
namespace MathCollab.Density.Stronger.Atkinson

def zetaAtkinsonPhase (T b x : ℝ) : ℝ :=
  T * Real.log x - 2 * Real.pi * x + 4 * Real.pi * b * Real.sqrt x


