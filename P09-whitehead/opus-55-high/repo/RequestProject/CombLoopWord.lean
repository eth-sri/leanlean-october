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

universe u v

variable {X : Complex2.{u}} {a : X.V} {G : Type v}

/-- The edge path contributed by one signed letter: the chosen loop of the letter, reversed if
the letter carries the negative sign. -/
def germLoopPath (g : G → Loop X a) (gb : G × Bool) :=
  if gb.2 then (g gb.1).1 else revPath (g gb.1).1

@[simp] theorem germLoopPath_pos (g : G → Loop X a) x :
    germLoopPath g (x, true) = (g x).1 := rfl

@[simp] theorem germLoopPath_neg (g : G → Loop X a) x :
    germLoopPath g (x, false) = revPath (g x).1 := rfl

/-- **The edge loop spelled by a word**: the concatenation of the chosen loops of its letters. -/
def wordPath (g : G → Loop X a) (l : List (G × Bool)) :=
  (l.map (germLoopPath g)).flatten

@[simp] theorem wordPath_nil (g : G → Loop X a) : wordPath g ([]) = [] := rfl

@[simp] theorem wordPath_cons (g : G → Loop X a) gb l :
    wordPath g (gb :: l) = germLoopPath g gb ++ wordPath g l := rfl

theorem wordPath_append (g : G → Loop X a) l l' :
    wordPath g (l ++ l') = wordPath g l ++ wordPath g l' := by
  simp [wordPath]

/-- **The homomorphism determined by concrete loops on the generators.** -/
def loopHom (g : G → Loop X a) :=
  FreeGroup.lift (fun x => Pi1.mk (g x))

@[simp] theorem loopHom_of (g : G → Loop X a) x :
    loopHom g (FreeGroup.of x) = Pi1.mk (g x) := by
  simp [loopHom]
