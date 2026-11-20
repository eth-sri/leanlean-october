module

public import Mathlib

@[expose] public section

/-!
# Traces: words modulo commutation of letters

This file develops, from scratch, the elementary combinatorics of words over an alphabet `V`
equipped with a symmetric irreflexive *commutation* relation `Cm`.  This is the combinatorial
heart of a right-angled Coxeter group

  `W = ⟨ s ∈ V | s² = 1, (s t)² = 1 for Cm s t ⟩`,

whose Cayley graph is the one-skeleton of the universal cover of the cube complexes `C(L)` used
in the paper.  Everything here is about *words*; the group is built in
`RequestProject/RACGGroup.lean`.

Main definitions:

* `FiniteChains.RACG.Swap` and `FiniteChains.RACG.CEq` — swapping two adjacent commuting letters
  and the equivalence relation it generates (equality of *traces*);
* `FiniteChains.RACG.canStart Cm s l` — the letter `s` can be moved to the front of `l`;
* `FiniteChains.RACG.popStart s l` — the word `l` with that occurrence of `s` deleted;
* `FiniteChains.RACG.IsRed Cm l` — `l` is *reduced*: no letter of `l` can be moved next to an
  earlier equal letter.

Main results:

* `FiniteChains.RACG.canStart_ceq`, `FiniteChains.RACG.isRed_ceq` — both notions only depend on
  the trace;
* `FiniteChains.RACG.ceq_popStart` — if `canStart Cm s l` then `l` is the trace `s :: popStart s l`;
* `FiniteChains.RACG.cancel_head` — traces are left cancellable;
* `FiniteChains.RACG.canStart_two` — **two distinct letters that can both be moved to the front
  commute, and can be moved there together**: this is the right-angled descent lemma.
-/

namespace FiniteChains
namespace RACG

universe u

variable {V : Type u}

/-- Swapping two adjacent commuting letters of a word. -/
inductive Swap (Cm : V → V → Prop) : List V → List V → Prop
  /-- Swap the first two letters. -/
  | head {a b : V} (h : Cm a b) (q : List V) : Swap Cm (a :: b :: q) (b :: a :: q)
  /-- Swap further along the word. -/
  | cons (x : V) {l l' : List V} : Swap Cm l l' → Swap Cm (x :: l) (x :: l')

/-- Equality of traces: words modulo commutation of adjacent commuting letters. -/
def CEq (Cm : V → V → Prop) := Relation.ReflTransGen (Swap Cm)

variable {Cm : V → V → Prop}

theorem Swap.symm' (hs : ∀ {a b : V}, Cm a b → Cm b a) {l l' : List V} (h : Swap Cm l l') :
    Swap Cm l' l := by
  induction h with
  | head h q => solve_by_elim
  | cons x _ ih => exact Swap.cons x ih

theorem Swap.length_eq {l l' : List V} (h : Swap Cm l l') : l.length = l'.length := by
  induction h with
  | head h q => simp
  | cons x _ ih => simp [ih]

theorem CEq.refl (l : List V) : CEq Cm l l := Relation.ReflTransGen.refl

theorem CEq.trans {l l' l'' : List V} (h : CEq Cm l l') (h' : CEq Cm l' l'') : CEq Cm l l'' :=
  Relation.ReflTransGen.trans h h'

theorem CEq.of_swap {l l' : List V} (h : Swap Cm l l') : CEq Cm l l' :=
  Relation.ReflTransGen.single h

theorem CEq.symm (hs : ∀ {a b : V}, Cm a b → Cm b a) {l l' : List V} (h : CEq Cm l l') :
    CEq Cm l' l := by
  induction h with
  | refl => exact CEq.refl _
  | tail _ hstep ih => exact CEq.trans (CEq.of_swap (hstep.symm' hs)) ih

theorem CEq.length_eq {l l' : List V} (h : CEq Cm l l') : l.length = l'.length := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans hstep.length_eq

theorem CEq.cons (x : V) {l l' : List V} (h : CEq Cm l l') : CEq Cm (x :: l) (x :: l') := by
  induction h with
  | refl => exact CEq.refl _
  | tail _ hstep ih => exact ih.tail (Swap.cons x hstep)

/-- `canStart Cm s l` : the letter `s` occurs in `l`, and all letters before its first
occurrence commute with `s`; equivalently `s` can be moved to the front of `l`. -/
def canStart (Cm : V → V → Prop) (s : V) : List V → Prop
  | [] => False
  | a :: t => a = s ∨ (Cm s a ∧ canStart Cm s t)

@[simp] theorem canStart_nil (s : V) : ¬ canStart Cm s ([]) := id

@[simp] theorem canStart_cons {s a : V} {t : List V} :
    canStart Cm s (a :: t) ↔ a = s ∨ (Cm s a ∧ canStart Cm s t) := Iff.rfl

section

variable [DecidableEq V]

/-- Delete the occurrence of `s` that `canStart` refers to. -/
def popStart (s : V) : List V → List V
  | [] => []
  | a :: t => if a = s then t else a :: popStart s t

@[simp] theorem popStart_nil (s : V) : popStart s ([]) = [] := rfl

@[simp] theorem popStart_cons (s a : V) (t : List V) :
    popStart s (a :: t) = if a = s then t else a :: popStart s t := rfl

end

/-- A word is **reduced** when no letter can be moved to the front to meet an equal letter. -/
def IsRed (Cm : V → V → Prop) : List V → Prop
  | [] => True
  | a :: t => IsRed Cm t ∧ ¬ canStart Cm a t

@[simp] theorem isRed_nil : IsRed Cm ([]) := trivial

@[simp] theorem isRed_cons {a : V} {t : List V} :
    IsRed Cm (a :: t) ↔ IsRed Cm t ∧ ¬ canStart Cm a t := Iff.rfl

section Basic

variable (hirr : ∀ a : V, ¬ Cm a a) (hsymm : ∀ {a b : V}, Cm a b → Cm b a)
include hirr hsymm

variable {s : V} {l l' : List V}

omit hirr in
/-- `canStart` only depends on the trace. -/
theorem canStart_swap (h : Swap Cm l l') :
    canStart Cm s l ↔ canStart Cm s l' := by
  induction h with
  | @head a b hab q =>
      grind [canStart_cons]
  | cons x _ ih => simp_all

omit hirr in
theorem canStart_ceq (h : CEq Cm l l') :
    canStart Cm s l ↔ canStart Cm s l' := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hstep ih => exact ih.trans (canStart_swap hsymm hstep)

variable {l l' : List V}

/-- Reducedness only depends on the trace. -/
theorem isRed_swap (h : Swap Cm l l') : IsRed Cm l ↔ IsRed Cm l' := by
  induction h with
  | @head a b hab q =>
      grind [isRed_cons, canStart_cons]
  | @cons x l₀ l₀' hstep ih =>
      grind [isRed_cons, canStart_swap]

theorem isRed_ceq (h : CEq Cm l l') : IsRed Cm l ↔ IsRed Cm l' := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hstep ih => grind [isRed_swap]

variable [DecidableEq V]

variable {s : V}

section

variable {l : List V} (h : canStart Cm s l)
include h

omit hirr in
/-- If `s` can be moved to the front, the trace is `s` followed by the rest. -/
theorem ceq_popStart :
    CEq Cm l (s :: popStart s l) := by
  induction l with
  | nil => simp_all
  | cons a t ih =>
      by_cases hat : a = s
      · subst hat
        simp only [popStart_cons, if_pos]
        exact CEq.refl _
      · rcases h with h | ⟨hsa, ht⟩
        · exact absurd h hat
        · have h3 := (CEq.cons a (ih ht)).trans (CEq.of_swap (Swap.head (hsymm hsa) _))
          simp_all

omit hirr in
theorem length_popStart :
    (popStart s l).length + 1 = l.length := by
  have := (ceq_popStart hsymm h).length_eq
  simp_all

end

variable {l l' : List V}

omit hsymm in
/-- `popStart` respects traces. -/
theorem popStart_swap (h : Swap Cm l l') :
    CEq Cm (popStart s l) (popStart s l') := by
  induction h with
  | @head a b hab q =>
      have hne : a ≠ b := by rintro rfl; exact hirr _ hab
      by_cases hs : a = s
      · subst hs
        have hbs : b ≠ a := fun h => hne h.symm
        simp only [popStart_cons, if_neg hbs]
        exact CEq.refl _
      · by_cases hbs : b = s
        · subst hbs
          simp only [popStart_cons, if_neg hs]
          exact CEq.refl _
        · simp only [popStart_cons, if_neg hs, if_neg hbs]
          solve_by_elim [CEq.of_swap]
  | @cons x l₀ l₀' hstep ih =>
      by_cases hx : x = s
      · subst hx; simpa using CEq.of_swap hstep
      · simpa [hx] using CEq.cons x ih

omit hsymm in
theorem popStart_ceq (h : CEq Cm l l') :
    CEq Cm (popStart s l) (popStart s l') := by
  induction h with
  | refl => exact CEq.refl _
  | tail _ hstep ih => exact ih.trans (popStart_swap hirr hstep)

omit hsymm in
/-- Traces are left cancellable. -/
theorem cancel_head (h : CEq Cm (s :: l) (s :: l')) : CEq Cm l l' := by
  simpa using popStart_ceq (s := s) hirr h

section

variable {l : List V} (hl : IsRed Cm l) (h : canStart Cm s l)
include hl h

/-- Deleting the front letter of a reduced word leaves a reduced word. -/
theorem isRed_popStart :
    IsRed Cm (popStart s l) :=
  ((isRed_ceq hirr hsymm (ceq_popStart hsymm h)).1 hl).1

/-- After deleting the front occurrence of `s` from a reduced word, `s` can no longer be moved
to the front. -/
theorem not_canStart_popStart :
    ¬ canStart Cm s (popStart s l) :=
  ((isRed_ceq hirr hsymm (ceq_popStart hsymm h)).1 hl).2

end

omit hirr in
/-- **The right-angled descent lemma.**  Two distinct letters that can both be moved to the front
of a word commute, and the second one can still be moved to the front after deleting the
first. -/
theorem canStart_two {s r : V} (hsr : s ≠ r) {l : List V}
    (hs : canStart Cm s l) (hr : canStart Cm r l) :
    Cm s r ∧ canStart Cm r (popStart s l) := by
  induction l with
  | nil => simp_all
  | cons a t ih =>
      by_cases has : a = s
      · simp_all
      · rcases hs with h | ⟨hsa, hst⟩
        · exact absurd h has
        · aesop

end Basic

end RACG
end FiniteChains
