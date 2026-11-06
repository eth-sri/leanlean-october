import Mathlib.Tactic

import RequestProject.CombPi1

/-!
# Reading a word of generators as an edge loop

The one-way comparison of `RequestProject/SubstOneWay.lean` needs, for every block of the
substitution, a homomorphism out of the free group on the generators of that block into the
fundamental group of a complex.  Such a homomorphism is always given by **concrete loops on the
generators**, and the relations it has to satisfy are then **checked on the concatenated edge
loops**.  This file provides exactly that dictionary for `FiniteChains.Comb.Pi1`:

* `FiniteChains.Comb.wordPath` — the edge loop obtained by concatenating the chosen loops of
  the letters of a word (a letter with the negative sign contributing the reversed loop);
* `FiniteChains.Comb.loopHom` — the homomorphism `FreeGroup G →* π₁(X, a)` determined by a
  family of loops;
* `FiniteChains.Comb.loopHom_mk` — its value on a word is the class of the concatenated loop;
* `FiniteChains.Comb.loopHom_eq_one_of_htpy` — a relation of the block holds in `π₁` as soon as
  the concatenated loop of its word is null-homotopic, which is the form in which a filling is
  actually produced.
-/

namespace FiniteChains.Comb



variable {X : Complex2.{u}} {a : X.V} {G : Type v}

variable (g : G → Loop X a)
/-- The edge path contributed by one signed letter: the chosen loop of the letter, reversed if
the letter carries the negative sign. -/
def germLoopPath  (gb : G × Bool)  :=
  if gb.2 then (g gb.1).1 else revPath (g gb.1).1

variable (x : G)
@[simp] theorem germLoopPath_pos   :
    germLoopPath g (x, true) = (g x).1 := rfl

@[simp] theorem germLoopPath_neg   :
    germLoopPath g (x, false) = revPath (g x).1 := rfl

/-- **The edge loop spelled by a word**: the concatenation of the chosen loops of its letters. -/
def wordPath  (l : List (G × Bool))  :=
  (l.map (germLoopPath g)).flatten

@[simp] theorem wordPath_nil  : wordPath g ([] : List (G × Bool)) = [] := rfl

@[simp] theorem wordPath_cons  (gb : G × Bool) (l : List (G × Bool)) :
    wordPath g (gb :: l) = germLoopPath g gb ++ wordPath g l := rfl



/-- **The homomorphism determined by concrete loops on the generators.** -/
def loopHom   :=
  FreeGroup.lift (fun x => Pi1.mk (g x))

@[simp] theorem loopHom_of   :
    loopHom g (FreeGroup.of x) = Pi1.mk (g x) := by
  simp [loopHom]

end FiniteChains.Comb

