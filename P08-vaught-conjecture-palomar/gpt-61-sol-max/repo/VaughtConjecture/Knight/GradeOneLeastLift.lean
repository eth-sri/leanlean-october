/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.VisibleOrderInterpolation
public import VaughtConjecture.Knight.FullRowCoverage

/-! # A finite least-lift test at grade one

For a fixed full controller, propagate the prescribed values and the ambient's
capped values upward along source order. The maximum of these lower bounds is
the least order-compatible candidate. Check only its pinned inactive values,
protected values, and bottom-source reads. At a nonbottom visible cap, consistency
and the interpolation theorem make a passing candidate a genuine lawful lift.

Taking the finite disjunction over full controllers is exact. The result is not
a proof that every input passes. No mixed-grade claim or general transitivity
of faithful transformations is used.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FullRowLifting

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

namespace Propagation

section Order

variable {Y X S L : Type*} [Fintype Y] [Fintype X]
  [LinearOrder S] [LinearOrder L] [OrderBot L]

/-- Least source-monotone candidate above the two sets of required lower bounds.
It is computed by finite maxima, not an iteration to an unspecified fixed point. -/
def close (E : Y → S) (embed : X → Y) (p : X → L) (q : Y → L) (γ : L) (d : Y) : L :=
  max (Finset.univ.sup (fun e => if E e ≤ E d then min (q e) γ else ⊥))
    (Finset.univ.sup (fun x => if E (embed x) ≤ E d then p x else ⊥))

variable [OrderBot S]

/-- The remaining upper bounds after lower-bound propagation. -/
def Check (E : Y → S) (embed : X → Y) (p : X → L) (q : Y → L) (γ : L) : Prop :=
  (∀ d, q d < γ → close E embed p q γ d ≤ q d) ∧
  (∀ x, close E embed p q γ (embed x) ≤ p x) ∧
  (∀ d, E d = ⊥ → close E embed p q γ d = ⊥)

end Order

section Visibility

variable {Y X S : Type*} [Fintype Y] [Fintype X] [LinearOrder S]

end Visibility

end Propagation

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ : Finset ι × ℕ}

noncomputable local instance : Fintype (D.below BJ) := Fintype.ofFinite _

end VaughtConjecture.Knight.FullRowLifting
