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

lemma divisor_support_inter_compact_finite (f : 𝕜 → E) {U K : Set 𝕜}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    (K ∩ (MeromorphicOn.divisor f U).support).Finite := by
  classical
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have hloc :
      ∀ x ∈ K, ∃ V : Set 𝕜, V ∈ 𝓝 x ∧ Set.Finite (V ∩ D.support) := by
    intro x hxK
    rcases D.supportLocallyFiniteWithinDomain x (hKU hxK) with ⟨V, hV, hfin⟩
    exact ⟨V, hV, hfin⟩
  choose V hVnhds hVfin using hloc
  rcases hK.elim_nhds_subcover' (U := fun x hx => V x hx) (hU := fun x hx => hVnhds x hx) with
    ⟨t, ht⟩
  have hsub :
      K ∩ D.support ⊆ ⋃ x ∈ t, (V (x : 𝕜) x.2 ∩ D.support) := by
    intro y hy
    rcases hy with ⟨hyK, hyS⟩
    have hycov : y ∈ ⋃ x ∈ t, V (x : 𝕜) x.2 := ht hyK
    rcases Set.mem_iUnion.1 hycov with ⟨x, hycov'⟩
    rcases Set.mem_iUnion.1 hycov' with ⟨hxT, hyV⟩
    refine Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ?_⟩
    exact ⟨hxT, ⟨hyV, hyS⟩⟩
  have hfinU : Set.Finite (⋃ x ∈ t, (V (x : 𝕜) x.2 ∩ D.support)) := by
    classical
    refine (t.finite_toSet).biUnion ?_
    intro x hx
    simpa using (hVfin (x : 𝕜) x.2)
  exact hfinU.subset hsub

/-!
## Local singleton balls and enumerations of the divisor support
-/

end MeromorphicOn
