/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Data.Set.Countable
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.Lindelof

/-!
# Support of the divisor of a meromorphic function

This file contains topological properties of the support of `MeromorphicOn.divisor`.
In particular, the support is discrete, and in hereditarily Lindelöf spaces it is countable.
It is also locally finite within the domain, hence meets compact subsets of the domain in finitely
many points.

## Main results

* `MeromorphicOn.divisor_support_discrete`: the divisor support is discrete.
* `MeromorphicOn.divisor_support_countable`: in a hereditarily Lindelöf space, the support is
  countable.
* `MeromorphicOn.divisor_support_inter_compact_finite`: a compact set meets the support in finitely
  many points.
* `MeromorphicOn.exists_ball_inter_divisor_support_eq_singleton`: isolating balls around support
  points.
-/

@[expose] public section

open Filter Topology Set

namespace MeromorphicOn

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U K : Set 𝕜} {z : 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
## Discreteness and countability of the divisor support
-/

/-!
## Finiteness of the divisor support on compact subsets of the domain
-/

/-!
## Local singleton balls and enumerations of the divisor support
-/

end MeromorphicOn
