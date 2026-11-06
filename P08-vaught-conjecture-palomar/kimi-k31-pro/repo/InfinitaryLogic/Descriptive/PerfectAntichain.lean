/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Descriptive.CantorAntichain
public import InfinitaryLogic.Topology.Perfect
public import Architect
public import Mathlib.Topology.DerivedSet
public import Mathlib.Topology.MetricSpace.Perfect
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Perfect and Cantor antichains, and thinness

The vocabulary a dichotomy theorem is stated in, separated from any particular dichotomy.

* `HasPerfectAntichainOn r A` — a nonempty perfect subset of `A` of pairwise `r`-inequivalent
  points;
* `HasCantorAntichainOn r A` — a *continuous* Cantor-space parametrization of such an antichain,
  the constructive form the Cantor-scheme builders actually produce;
* `IsThinOn r A` — the negation of the first.

The two positive forms are related by `HasPerfectAntichainOn.hasCantorAntichainOn`, which is
`Perfect.exists_nat_bool_injection` plus bookkeeping.  Injectivity of a Cantor antichain is not
an extra hypothesis: it follows from *reflexivity* of the setoid, since distinct arguments have
inequivalent images and every point is equivalent to itself.

The file also carries the cardinal facts these statements are measured against: a nonempty
perfect set in a complete, second-countable metric space has size continuum
(`Perfect.mk_eq_continuum`, which lives in the topology-only module
`InfinitaryLogic/Topology/Perfect.lean`, imported here); a perfect transversal forces
continuum-many classes (`continuum_classes_of_perfect_transversal`,
with its two-sided companion); and a Polish space, hence any quotient of one, has at most
continuum-many points (`mk_le_continuum_of_polish`, `mk_quotient_le_continuum_of_polish`).
None of them mentions a dichotomy, an equivalence relation being closed, or a splitting
hypothesis.  It also carries the purely set-theoretic `countable_quotient_of_countable_range`: a
quotient is countable when a map with countable range refines the relation.

**Hypotheses are kept minimal, and the ordering below is what makes that possible.**  Only three
results need `SecondCountableTopology`: the two Polish cardinality bounds and the *upper* half of
`Perfect.mk_eq_continuum`.  Everything else needs at most `MetricSpace` + `CompleteSpace` (for the
Cantor injection) or nothing beyond `TopologicalSpace`.  In particular
`continuum_classes_of_perfect_transversal` is proved through the Cantor antichain rather than
through `mk_eq_continuum`, which is what lets it drop second countability — it only ever needed
the lower bound.
-/

@[expose] public section

open Cardinal Set

-- `𝓟` only; opening `Filter` itself would clash with `Set` on names like `map`.
open scoped Filter

universe u v

/-! ### The generic vocabulary -/

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

/-! ### Adapters that need no metric structure -/

variable {r : Setoid X} {A B : Set X}




omit [TopologicalSpace X] in

omit [TopologicalSpace X] in


/-! ### Cantor antichain → perfect antichain

The converse direction to `HasPerfectAntichainOn.hasCantorAntichainOn` below, and the one that
needs no metric or completeness assumption — only that the ambient space is Hausdorff. -/



/-! ### Adapters needing the Cantor injection

`Perfect.exists_nat_bool_injection` needs a complete metric space, but **not** second
countability. -/

/-- A perfect antichain yields a Cantor antichain: `Perfect.exists_nat_bool_injection` together
with the observation that the injection's range lies in the perfect set, hence in `A`. -/
theorem HasPerfectAntichainOn.hasCantorAntichainOn {α : Type u} [MetricSpace α]
    [CompleteSpace α] {r : Setoid α} {A : Set α}
    (h : HasPerfectAntichainOn r A) : HasCantorAntichainOn r A := by
  obtain ⟨P, hperf, hne, hsub, hanti⟩ := h
  obtain ⟨f, hrange, hcont, hinj⟩ := hperf.exists_nat_bool_injection hne
  refine ⟨f, hcont, fun x => hsub (hrange (mem_range_self x)), fun x y hxy hr => ?_⟩
  exact hxy (hinj (hanti _ (hrange (mem_range_self x)) _ (hrange (mem_range_self y)) hr))

/-- Refuting Cantor antichains suffices for thinness. -/
theorem IsThinOn.of_no_cantorAntichain {α : Type u} [MetricSpace α] [CompleteSpace α]
    {r : Setoid α} {A : Set α} (h : ¬HasCantorAntichainOn r A) : IsThinOn r A :=
  fun hp => h hp.hasCantorAntichainOn

/-! ### Perfect transversal → continuum classes -/

/-! ### Polish space cardinality upper bound -/



/-! ### Packaging the Cantor-scheme builders

Wrappers only: the existential content is `CantorAntichain.lean`'s, restated in the vocabulary
above so that consumers need not unpack it.  Each concludes at the scheme's own root; use
`HasCantorAntichainOn.mono` to enlarge to an ambient set. -/

/-! ### Countable quotients from countable ranges -/

namespace FirstOrder.Language

/-- A quotient is countable when a map with countable range refines the relation: fibres of the
map lie inside classes.  The proof chooses one preimage for each value in the range (classical
choice; not a Borel selector and not a choice of canonical structures). -/
theorem countable_quotient_of_countable_range {X T : Type*} (s : Setoid X) (t : X → T)
    (hrange : (Set.range t).Countable) (h : ∀ x y, t x = t y → s.r x y) :
    Countable (Quotient s) := by

  have : Countable (Set.range t) := hrange.to_subtype
  refine Function.Surjective.countable (f := fun v : Set.range t => Quotient.mk s v.2.choose) ?_
  intro q
  induction q using Quotient.inductionOn with | _ x =>
  refine ⟨⟨t x, x, rfl⟩, Quotient.sound (h _ _ ?_)⟩
  exact (⟨x, rfl⟩ : t x ∈ Set.range t).choose_spec

