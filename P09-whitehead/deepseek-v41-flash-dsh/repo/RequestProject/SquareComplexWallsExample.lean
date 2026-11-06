module

public import RequestProject.SquareComplexWalls

@[expose] public section

/-!
# The four-cycle with its square: non-vacuity of the wall theorems

`RequestProject/SquareComplexWalls.lean` proves that in a simply connected square complex every
square-closed family of edges is two-sided.  Here the hypotheses are checked on an explicit
complex which really has a two-cell: the four-cycle `ZMod 4` with its square glued in
(`FiniteChains.cycleFour`).  We prove

* `FiniteChains.cycleFour_simplyConnected` — every closed walk contracts by elementary moves, so
  the complex is simply connected (this is where the two-cell is used);
* `FiniteChains.cycleFour_connected` — it is connected;
* `FiniteChains.cycleFour_bipartition`, `FiniteChains.cycleFour_wall` — the conclusions of
  `SquareComplex.exists_bipartition` and `SquareComplex.exists_side` therefore apply to it;
* `FiniteChains.cycleFourNoSquare_not_simplyConnected` — the same graph *without* the two-cell is
  not simply connected, so the two-cell is genuinely needed and the notion of simple connectivity
  used in the wall theorems is not vacuous.
-/

namespace FiniteChains

/-- Adjacency of the four-cycle. -/
def cycleFourAdj (x y : ZMod 4) : Prop := y = x + 1 ∨ y = x - 1

instance : DecidableRel cycleFourAdj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The single two-cell of the four-cycle, read from any vertex and in either orientation. -/
def cycleFourSq (a b c d : ZMod 4) : Prop :=
  (b = a + 1 ∧ c = a + 2 ∧ d = a + 3) ∨ (b = a - 1 ∧ c = a - 2 ∧ d = a - 3)

instance : ∀ a b c d, Decidable (cycleFourSq a b c d) := fun _ _ _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

theorem cycleFourAdj_symm : ∀ a b : ZMod 4, cycleFourAdj a b → cycleFourAdj b a := by decide

theorem cycleFourAdj_irrefl : ∀ a : ZMod 4, ¬ cycleFourAdj a a := by decide

theorem cycleFourSq_adj : ∀ a b c d : ZMod 4, cycleFourSq a b c d →
    cycleFourAdj a b ∧ cycleFourAdj b c ∧ cycleFourAdj c d ∧ cycleFourAdj d a := by decide

theorem cycleFourSq_rotate : ∀ a b c d : ZMod 4, cycleFourSq a b c d → cycleFourSq b c d a := by
  decide

theorem cycleFourSq_reverse : ∀ a b c d : ZMod 4, cycleFourSq a b c d → cycleFourSq d c b a := by
  decide

/-- The four-cycle with its square glued in. -/
def cycleFour : SquareComplex (ZMod 4) where
  adj := cycleFourAdj
  adj_symm := fun {a b} h => cycleFourAdj_symm a b h
  adj_irrefl := cycleFourAdj_irrefl
  sq := cycleFourSq
  sq_adj := fun {a b c d} h => cycleFourSq_adj a b c d h
  sq_rotate := fun {a b c d} h => cycleFourSq_rotate a b c d h
  sq_reverse := fun {a b c d} h => cycleFourSq_reverse a b c d h

end FiniteChains
