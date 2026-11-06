/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReductModel
public import VaughtConjecture.Knight.Reduction
public import VaughtConjecture.Knight.ActualOccurrence

/-! # Extension sets over a tuple: syntactic, realized, reduced

Three different sets of one-point extensions of a stage type `p : S α n` are in play, and the
Scott-process reading of the tower (Larson, Def. 3.1) must not identify them:

* the **syntactic coface fibre** `cofaceSet p = {q | IsCoface p q}`: every same-stage type
  restricting to `p` along the initial face, with no model in sight;
* the extensions **actually realized** over a tuple `t` in a realization `R`,
  `R.realizedExt t = {q | ∃ y ∉ range t, R (t⌢y) = some q}`;
* the **lower-stage extensions obtained by reducing higher-stage cofaces**,
  `reducedExt h p = reduceType '' cofaceSet p`, for `p` at the higher stage.

Laws proved here, unconditionally or under exact parent consistency / modelhood only:

* realized extensions are cofaces (`realizedExt_subset_cofaceSet`), and Knight's
  `RealizesSome` is nonemptiness of `realizedExt ∩ U` (`realizesSome_iff`);
* restriction along a coordinate embedding `e`, through `onePointProj e`, for each of the
  three sets (`cofaceSet_restrict`, `realizedExt_restrict`, `reducedExt_restrict`);
* reduction: the reduct realizes exactly the reductions of what `R` realizes
  (`realizedExt_reduct`, an equality), reduced cofaces are cofaces of the reduced type
  (`reducedExt_subset_cofaceSet`), and what a reduct realizes over `t` is the reduction of a
  higher-stage coface of the label of `t` (`realizedExt_reduct_subset_reducedExt`);
* class-wide eligibility: `eligible α p` is the set of extensions realized over some tuple of
  type `p` in some model; `eligible_subset_cofaceSet`, `realizedExt_subset_eligible`, and
  reduction maps eligible to eligible (`reduceType_mem_eligible`, via `IsModel.reduct`).

**What is not proved: the lifting clause.**  Larson's coherence condition (2b) for a Scott
process reads, for `α < β`, `E(V_{α+1,β} φ) ⊆ V_{α,β}[{ψ ∈ Φ^{n+1}_β | H(ψ, i_n) = φ}]`: every
extension asserted at the lower stage by the reduction of `φ` is the reduction of a
higher-stage coface of `φ`.  Its analogue here is `LiftingLaw h`:
`eligible α (reduceType p) ⊆ reducedExt h p` for every `p` at the higher stage, with the
realized strengthening `RealizedLiftingLaw h` (the lift is realized over the given tuple).
Nothing in this file supplies either: the tower's existential clauses (`genSat`,
`bottomPattern`, uniformity, dominance) assert realization of *some* member of prescribed
families only, and the converse inclusion `reducedExt ⊆ eligible` is likewise not asserted.
`RealizedLiftingLaw` is the form a cross-stage back-and-forth argument should consume directly:
it speaks only of tuples realized in a model.  `LiftingLaw` is its type-level shadow; passing
from one to the other (`LiftingLaw.of_realized`) needs every type to be realized in some model,
which is **not** to be added as a hypothesis merely to reach the all-types interface.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

universe w

variable {n : ℕ}

/-! ### The syntactic coface fibre -/

section Syntactic

variable {α : Ordinal.{0}}

/-- The syntactic coface fibre of `p`, as a set: every same-stage type restricting to `p` along
the initial face `Fin.castSuccEmb`. -/
def cofaceSet (p : S α n) : Set (S α (n + 1)) := {q | IsCoface p q}

@[simp] theorem mem_cofaceSet {p : S α n} {q : S α (n + 1)} :
    q ∈ cofaceSet p ↔ IsCoface p q := Iff.rfl

end Syntactic

/-! ### Lower-stage extensions obtained by reducing higher-stage cofaces -/

section Reduced

variable {α β : LimitStage}

end Reduced

/-! ### Extensions actually realized over a tuple -/

namespace KnightRealization

variable {M : Type w} {α β : LimitStage}

variable {R : KnightRealization α M} {t : Fin n ↪ M} {p : S α.1 n}

end KnightRealization

/-! ### Class-wide eligibility and the unsupplied lifting clause -/

section Eligible

variable {α β : LimitStage}

end Eligible

end VaughtConjecture.Knight
