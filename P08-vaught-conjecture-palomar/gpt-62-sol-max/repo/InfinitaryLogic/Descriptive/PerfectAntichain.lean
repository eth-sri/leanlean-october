/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Topology.MetricSpace.CantorScheme
public import Mathlib.Topology.MetricSpace.Perfect
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.SetTheory.Cardinal.Continuum
public import Architect
public import Mathlib.Topology.DerivedSet


public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

open Cardinal Set

open scoped Filter

universe u v

variable {X : Type u} [TopologicalSpace X]

/-- `A` carries a **perfect antichain** for `r`: a nonempty perfect subset of `A` whose points
are pairwise `r`-inequivalent. -/
@[blueprint "def:perfect-antichain"
  (title := /-- Perfect antichain -/)
  (statement := /-- A set $A$ carries a \emph{perfect antichain} for an equivalence relation $r$
    if some nonempty perfect $P \subseteq A$ has pairwise $r$-inequivalent points. -/)]
def HasPerfectAntichainOn (r : Setoid X) (A : Set X) : Prop :=
  ∃ P, Perfect P ∧ P.Nonempty ∧ P ⊆ A ∧ ∀ x ∈ P, ∀ y ∈ P, r.r x y → x = y

/-- `A` carries a **Cantor antichain** for `r`: a continuous map from Cantor space into `A`
sending distinct points to `r`-inequivalent ones.  This is what the Cantor-scheme builders
produce directly, and it is the form a thinness proof must refute. -/
@[blueprint "def:cantor-antichain"
  (title := /-- Cantor antichain -/)
  (statement := /-- A set $A$ carries a \emph{Cantor antichain} for $r$ if there is a continuous
    $f : 2^{\mathbb{N}} \to A$ sending distinct points to $r$-inequivalent ones.  This is the
    constructive form the Cantor-scheme builders produce, and the load-bearing intermediary
    between perfect antichains and cardinality. -/)]
def HasCantorAntichainOn (r : Setoid X) (A : Set X) : Prop :=
  ∃ f : (ℕ → Bool) → X,
    Continuous f ∧ (∀ x, f x ∈ A) ∧ ∀ x y, x ≠ y → ¬r.r (f x) (f y)

/-- `A` is **thin** for `r`: no perfect antichain. -/
@[blueprint "def:thin-on"
  (title := /-- Thinness -/)
  (statement := /-- $A$ is \emph{thin} for $r$ if it carries no perfect antichain. -/)
  (uses := ["def:perfect-antichain"])]
def IsThinOn (r : Setoid X) (A : Set X) : Prop :=
  ¬HasPerfectAntichainOn r A

variable {r : Setoid X} {A : Set X}

/-- A perfect antichain yields a Cantor antichain: `Perfect.exists_nat_bool_injection` together
with the observation that the injection's range lies in the perfect set, hence in `A`. -/
theorem HasPerfectAntichainOn.hasCantorAntichainOn {α : Type u} [MetricSpace α]
    [CompleteSpace α] {r : Setoid α} {A : Set α}
    (h : HasPerfectAntichainOn r A) : HasCantorAntichainOn r A := by
  obtain ⟨P, hperf, hne, hsub, hanti⟩ := h
  obtain ⟨f, hrange, hcont, hinj⟩ := hperf.exists_nat_bool_injection hne
  grind +locals

/-- Refuting Cantor antichains suffices for thinness. -/
theorem IsThinOn.of_no_cantorAntichain {α : Type u} [MetricSpace α] [CompleteSpace α]
    {r : Setoid α} {A : Set α} (h : ¬HasCantorAntichainOn r A) : IsThinOn r A :=
  fun hp => h hp.hasCantorAntichainOn
