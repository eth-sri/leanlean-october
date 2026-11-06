import Mathlib


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

namespace FiniteChains.RACG

universe u

variable {V : Type u}

/-- Swapping two adjacent commuting letters of a word. -/
inductive Swap (Cm : V → V → Prop) : List V → List V → Prop
  /-- Swap the first two letters. -/
  | head {a b : V} (h : Cm a b) (q : List V) : Swap Cm (a :: b :: q) (b :: a :: q)
  /-- Swap further along the word. -/
  | cons (x : V) {l l' : List V} : Swap Cm l l' → Swap Cm (x :: l) (x :: l')

/-- Equality of traces: words modulo commutation of adjacent commuting letters. -/
def CEq (Cm : V → V → Prop) : List V → List V → Prop := Relation.ReflTransGen (Swap Cm)

variable {Cm : V → V → Prop}

theorem Swap.symm' (hs : ∀ {a b}, Cm a b → Cm b a) {l l'} (h : Swap Cm l l') :
    Swap Cm l' l := by
  induction h with
  | head h q => tauto
  | cons x _ ih => tauto

theorem Swap.length_eq (h : Swap Cm l l') : l.length = l'.length := by
  induction h <;> simp_all

theorem CEq.refl l : CEq Cm l l := Relation.ReflTransGen.refl

theorem CEq.trans (h : CEq Cm l l') (h' : CEq Cm l' l'') : CEq Cm l l'' :=
  Relation.ReflTransGen.trans h h'

theorem CEq.of_swap (h : Swap Cm l l') : CEq Cm l l' :=
  Relation.ReflTransGen.single h

theorem CEq.symm (hs : ∀ {a b}, Cm a b → Cm b a) {l l'} (h : CEq Cm l l') :
    CEq Cm l' l := by
  induction h with
  | refl => exact CEq.refl _
  | tail _ hstep ih => exact CEq.trans (CEq.of_swap (hstep.symm' hs)) ih

theorem CEq.length_eq (h : CEq Cm l l') : l.length = l'.length := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans hstep.length_eq

theorem CEq.cons x {l l'} (h : CEq Cm l l') : CEq Cm (x :: l) (x :: l') := by
  induction h with
  | refl => exact CEq.refl _
  | tail _ hstep ih => exact ih.tail (Swap.cons x hstep)

/-- `canStart Cm s l` : the letter `s` occurs in `l`, and all letters before its first
occurrence commute with `s`; equivalently `s` can be moved to the front of `l`. -/
def canStart (Cm : V → V → Prop) (s : V) : List V → Prop
  | [] => False
  | a :: t => a = s ∨ (Cm s a ∧ canStart Cm s t)

@[simp] theorem canStart_nil s : ¬ canStart Cm s ([]) := id

@[simp] theorem canStart_cons :
    canStart Cm s (a :: t) ↔ a = s ∨ (Cm s a ∧ canStart Cm s t) := Iff.rfl

/-- Delete the occurrence of `s` that `canStart` refers to. -/
def popStart [DecidableEq V] (s : V) : List V → List V
  | [] => []
  | a :: t => if a = s then t else a :: popStart s t

@[simp] theorem popStart_nil [DecidableEq V] s : popStart s ([] : List V) = [] := rfl

@[simp] theorem popStart_cons [DecidableEq V] s a (t : List V) :
    popStart s (a :: t) = if a = s then t else a :: popStart s t := rfl

/-- A word is **reduced** when no letter can be moved to the front to meet an equal letter. -/
def IsRed (Cm : V → V → Prop) : List V → Prop
  | [] => True
  | a :: t => IsRed Cm t ∧ ¬ canStart Cm a t

@[simp] theorem isRed_nil : IsRed Cm ([]) := trivial

@[simp] theorem isRed_cons :
    IsRed Cm (a :: t) ↔ IsRed Cm t ∧ ¬ canStart Cm a t := Iff.rfl

section Basic

variable (hirr : ∀ a : V, ¬ Cm a a) (hsymm : ∀ {a b : V}, Cm a b → Cm b a)
include hirr hsymm

omit hirr in
/-- `canStart` only depends on the trace. -/
theorem canStart_swap {s : V} {l l' : List V} (h : Swap Cm l l') :
    canStart Cm s l ↔ canStart Cm s l' := by
  induction h <;> aesop

omit hirr in
theorem canStart_ceq {s : V} {l l' : List V} (h : CEq Cm l l') :
    canStart Cm s l ↔ canStart Cm s l' := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hstep ih => exact ih.trans (canStart_swap hsymm hstep)

/-- Reducedness only depends on the trace. -/
theorem isRed_swap (h : Swap Cm l l') : IsRed Cm l ↔ IsRed Cm l' := by
  induction h with
  | @head a b hab q =>
      aesop
  | @cons x l₀ l₀' hstep ih =>
      simp [isRed_cons, ih, canStart_swap (s := x) hsymm hstep]

theorem isRed_ceq (h : CEq Cm l l') : IsRed Cm l ↔ IsRed Cm l' := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hstep ih => exact ih.trans (isRed_swap hirr hsymm hstep)

variable [DecidableEq V]

omit hirr in
/-- If `s` can be moved to the front, the trace is `s` followed by the rest. -/
theorem ceq_popStart {s : V} {l : List V} (h : canStart Cm s l) :
    CEq Cm l (s :: popStart s l) := by
  induction l with
  | nil => simp_all
  | cons a t ih =>
      by_cases hat : a = s
      · subst hat
        simp [popStart_cons, if_pos]
        exact CEq.refl _
      · rcases h with h | ⟨hsa, ht⟩
        · simp_all
        · have h1 := CEq.cons a (ih ht)
          have h2 : Swap Cm (a :: s :: popStart s t) (s :: a :: popStart s t) :=
            by tauto
          have h3 := h1.trans (CEq.of_swap h2)
          simp_all

omit hirr in
theorem length_popStart {s : V} {l : List V} (h : canStart Cm s l) :
    (popStart s l).length + 1 = l.length := by
  have := (ceq_popStart hsymm h).length_eq
  simpa using this.symm

omit hsymm in
/-- `popStart` respects traces. -/
theorem popStart_swap {s : V} {l l' : List V} (h : Swap Cm l l') :
    CEq Cm (popStart s l) (popStart s l') := by
  induction h with
  | @head a b hab q =>
      have hne : a ≠ b := by grind
      by_cases hs : a = s
      · subst hs
        have hbs : b ≠ a := by tauto
        simp [popStart_cons, if_neg hbs]
        exact CEq.refl _
      · by_cases hbs : b = s
        · subst hbs
          simp [popStart_cons, if_neg hs]
          exact CEq.refl _
        · simp [popStart_cons, if_neg hs, if_neg hbs]
          exact CEq.of_swap (Swap.head hab _)
  | @cons x l₀ l₀' hstep ih =>
      by_cases hx : x = s
      · subst hx; simpa using CEq.of_swap hstep
      · simpa [hx] using CEq.cons x ih

omit hsymm in
theorem popStart_ceq {s : V} {l l' : List V} (h : CEq Cm l l') :
    CEq Cm (popStart s l) (popStart s l') := by
  induction h with
  | refl => exact CEq.refl _
  | tail _ hstep ih => exact ih.trans (popStart_swap hirr hstep)

omit hsymm in
/-- Traces are left cancellable. -/
theorem cancel_head {s : V} {l l' : List V} (h : CEq Cm (s :: l) (s :: l')) : CEq Cm l l' := by
  simpa using popStart_ceq (s := s) hirr h

/-- Deleting the front letter of a reduced word leaves a reduced word. -/
theorem isRed_popStart {l} (hl : IsRed Cm l) (h : canStart Cm s l) :
    IsRed Cm (popStart s l) :=
  ((isRed_ceq hirr hsymm (ceq_popStart hsymm h)).1 hl).1

/-- After deleting the front occurrence of `s` from a reduced word, `s` can no longer be moved
to the front. -/
theorem not_canStart_popStart {l} (hl : IsRed Cm l) (h : canStart Cm s l) :
    ¬ canStart Cm s (popStart s l) :=
  ((isRed_ceq hirr hsymm (ceq_popStart hsymm h)).1 hl).2

omit hirr in
/-- **The right-angled descent lemma.**  Two distinct letters that can both be moved to the front
of a word commute, and the second one can still be moved to the front after deleting the
first. -/
theorem canStart_two {s r : V} (hsr : s ≠ r) {l : List V}
    (hs : canStart Cm s l) (hr : canStart Cm r l) :
    Cm s r ∧ canStart Cm r (popStart s l) := by
  induction l <;> aesop
