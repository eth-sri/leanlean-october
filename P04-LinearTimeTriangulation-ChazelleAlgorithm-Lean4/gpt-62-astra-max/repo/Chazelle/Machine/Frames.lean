module

public import Chazelle.Spec

/-! # Vocabulary for frame conditions

An array may change on a write set; typical clients read below a frontier, inside an
untouched band, or away from a short list of destination registers. The last predicate is
curried in the non-aliasing proofs so that a client at a known index need not build lists
of membership proofs. -/

@[expose] public section
namespace Chazelle

abbrev AgreeBelow {α : Type*} (n : ℕ) (f g : ℕ → α) : Prop := ∀ i < n, f i = g i

abbrev AgreeOnBand {α : Type*} (lo hi : ℕ) (f g : ℕ → α) : Prop :=
  ∀ i ≥ lo, i < hi → f i = g i

/-- Guard a read at `i` against each destination of a block. -/
@[reducible, simp] def OffWrites (i : ℕ) (Q : Prop) : List ℕ → Prop
  | [] => Q
  | j :: js => i ≠ j → OffWrites i Q js

abbrev AgreeExcept {α : Type*} (writes : List ℕ) (f g : ℕ → α) : Prop :=
  ∀ i, OffWrites i (f i = g i) writes

/-- A block writing only natural-number state leaves the real state and the output alone. -/
abbrev Config.NatFrame (d c : Config) : Prop :=
  d.rreg = c.rreg ∧ d.rmem = c.rmem ∧ d.output = c.output

abbrev Config.NRegFrame (d c : Config) : Prop := d.nmem = c.nmem ∧ d.NatFrame c

/-- Right-associated sequencing, for both structured programs and their execution proofs. -/
scoped syntax:60 term:61 " ;; " term:60 : term
macro_rules | `($a ;; $b) => `(.seq $a $b)

end Chazelle
