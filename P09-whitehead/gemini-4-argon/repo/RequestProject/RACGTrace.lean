module

public import Mathlib

@[expose] public section

namespace FiniteChains.RACG

universe u

variable {V : Type u}

inductive Swap (Cm : V → V → Prop) : List V → List V → Prop
  | head {a b : V} (h : Cm a b) (q : List V) : Swap Cm (a :: b :: q) (b :: a :: q)
  | cons (x : V) {l l' : List V} : Swap Cm l l' → Swap Cm (x :: l) (x :: l')

def CEq (Cm : V → V → Prop) : List V → List V → Prop := Relation.ReflTransGen (Swap Cm)

variable {Cm : V → V → Prop}

theorem Swap.length_eq {l l' : List V} (h : Swap Cm l l') : l.length = l'.length := by
  induction h <;> simp [*]

theorem CEq.refl (l : List V) : CEq Cm l l := Relation.ReflTransGen.refl

theorem CEq.trans {l l' l'' : List V} (h : CEq Cm l l') (h' : CEq Cm l' l'') : CEq Cm l l'' :=
  Relation.ReflTransGen.trans h h'

theorem CEq.of_swap {l l' : List V} (h : Swap Cm l l') : CEq Cm l l' :=
  Relation.ReflTransGen.single h

theorem CEq.symm (hs : ∀ {a b : V}, Cm a b → Cm b a) {l l' : List V} (h : CEq Cm l l') :
    CEq Cm l' l := by
  have hsw {u v : List V} (h : Swap Cm u v) : Swap Cm v u := by
    induction h with
    | head h q => exact Swap.head (hs h) q
    | cons x _ ih => exact Swap.cons x ih
  induction h with
  | refl => exact CEq.refl _
  | tail _ hstep ih => exact CEq.trans (CEq.of_swap (hsw hstep)) ih

theorem CEq.length_eq {l l' : List V} (h : CEq Cm l l') : l.length = l'.length := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans hstep.length_eq

theorem CEq.cons (x : V) {l l' : List V} (h : CEq Cm l l') : CEq Cm (x :: l) (x :: l') := by
  induction h with
  | refl => exact CEq.refl _
  | tail _ hstep ih => exact ih.tail (Swap.cons x hstep)

def canStart (Cm : V → V → Prop) (s : V) : List V → Prop
  | [] => False
  | a :: t => a = s ∨ (Cm s a ∧ canStart Cm s t)

@[simp] theorem canStart_nil (s : V) : ¬ canStart Cm s ([] : List V) := id

@[simp] theorem canStart_cons {s a : V} {t : List V} :
    canStart Cm s (a :: t) ↔ a = s ∨ (Cm s a ∧ canStart Cm s t) := Iff.rfl

def popStart [DecidableEq V] (s : V) : List V → List V
  | [] => []
  | a :: t => if a = s then t else a :: popStart s t

@[simp] theorem popStart_cons [DecidableEq V] (s a : V) (t : List V) :
    popStart s (a :: t) = if a = s then t else a :: popStart s t := rfl

def IsRed (Cm : V → V → Prop) : List V → Prop
  | [] => True
  | a :: t => IsRed Cm t ∧ ¬ canStart Cm a t

@[simp] theorem isRed_nil : IsRed Cm ([] : List V) := trivial

@[simp] theorem isRed_cons {a : V} {t : List V} :
    IsRed Cm (a :: t) ↔ IsRed Cm t ∧ ¬ canStart Cm a t := Iff.rfl

variable (hirr : ∀ a : V, ¬ Cm a a) (hsymm : ∀ {a b : V}, Cm a b → Cm b a)
include hirr hsymm

omit hirr in
theorem canStart_swap {s : V} {l l' : List V} (h : Swap Cm l l') :
    canStart Cm s l ↔ canStart Cm s l' := by
  induction h with
  | head hab =>
      have := hsymm hab
      simp only [canStart_cons]
      exact ⟨by rintro (rfl | ⟨hsa, rfl | ⟨hsb, hq⟩⟩) <;> tauto,
        by rintro (rfl | ⟨hsb, rfl | ⟨hsa, hq⟩⟩) <;> tauto⟩
  | cons _ _ ih => simp only [canStart_cons, ih]

omit hirr in
theorem canStart_ceq {s : V} {l l' : List V} (h : CEq Cm l l') :
    canStart Cm s l ↔ canStart Cm s l' := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hstep ih => exact ih.trans (canStart_swap hsymm hstep)

variable [DecidableEq V]

omit hirr in
theorem ceq_popStart {s : V} : ∀ {l : List V}, canStart Cm s l → CEq Cm l (s :: popStart s l)
  | [], h => absurd h (canStart_nil s)
  | a :: t, h => by
      by_cases hat : a = s
      · subst hat; simp [CEq.refl]
      · rcases h with h | ⟨hsa, ht⟩
        · exact absurd h hat
        · simpa [hat] using (CEq.cons a (ceq_popStart ht)).trans (CEq.of_swap (Swap.head (hsymm hsa) _))

omit hirr in
theorem length_popStart {s : V} {l : List V} (h : canStart Cm s l) :
    (popStart s l).length + 1 = l.length := by
  simpa using (ceq_popStart hsymm h).length_eq.symm

omit hsymm in
theorem popStart_ceq {s : V} {l l' : List V} (h : CEq Cm l l') :
    CEq Cm (popStart s l) (popStart s l') := by
  have hsw {u v : List V} (h : Swap Cm u v) : CEq Cm (popStart s u) (popStart s v) := by
    induction h with
    | @head a b hab q =>
        have hne : a ≠ b := fun he => hirr _ (he ▸ hab)
        by_cases hs : a = s
        · subst hs; simp [Ne.symm hne, CEq.refl]
        · by_cases hbs : b = s
          · subst hbs; simp [hs, CEq.refl]
          · simp [hs, hbs, CEq.of_swap (Swap.head hab _)]
    | @cons x _ _ hstep ih =>
        by_cases hx : x = s
        · subst hx; simpa using CEq.of_swap hstep
        · simpa [hx] using CEq.cons x ih
  induction h with
  | refl => exact CEq.refl _
  | tail _ hstep ih => exact ih.trans (hsw hstep)

omit hsymm in
theorem cancel_head {s : V} {l l' : List V} (h : CEq Cm (s :: l) (s :: l')) : CEq Cm l l' := by
  simpa using popStart_ceq (s := s) hirr h

theorem isRed_ceq {l l' : List V} (h : CEq Cm l l') : IsRed Cm l ↔ IsRed Cm l' := by
  have hsw {u v : List V} (h : Swap Cm u v) : IsRed Cm u ↔ IsRed Cm v := by
    induction h with
    | @head a b hab q =>
        have hba := hsymm hab
        have hne : a ≠ b := fun he => hirr _ (he ▸ hab)
        simp only [isRed_cons, canStart_cons]
        exact ⟨fun ⟨⟨hq, hbq⟩, hstart⟩ =>
            ⟨⟨hq, fun hc => hstart (.inr ⟨hab, hc⟩)⟩, by rintro (h' | ⟨_, h'⟩); exacts [hne h', hbq h']⟩,
          fun ⟨⟨hq, haq⟩, hstart⟩ =>
            ⟨⟨hq, fun hc => hstart (.inr ⟨hba, hc⟩)⟩, by rintro (h' | ⟨_, h'⟩); exacts [hne h'.symm, haq h']⟩⟩
    | @cons x _ _ hstep ih =>
        simp only [isRed_cons, ih, canStart_swap (s := x) hsymm hstep]
  induction h with
  | refl => exact Iff.rfl
  | tail _ hstep ih => exact ih.trans (hsw hstep)

theorem isRed_popStart {s : V} {l : List V} (hl : IsRed Cm l) (h : canStart Cm s l) :
    IsRed Cm (popStart s l) :=
  ((isRed_ceq hirr hsymm (ceq_popStart hsymm h)).1 hl).1

theorem not_canStart_popStart {s : V} {l : List V} (hl : IsRed Cm l) (h : canStart Cm s l) :
    ¬ canStart Cm s (popStart s l) :=
  ((isRed_ceq hirr hsymm (ceq_popStart hsymm h)).1 hl).2

omit hirr in
theorem canStart_two {s r : V} (hsr : s ≠ r) : ∀ {l : List V},
    canStart Cm s l → canStart Cm r l → Cm s r ∧ canStart Cm r (popStart s l)
  | [], hs, _ => absurd hs (canStart_nil s)
  | a :: t, hs, hr => by
      by_cases has : a = s
      · subst has
        rcases hr with h | ⟨hra, hrt⟩
        · exact absurd h hsr
        · exact ⟨hsymm hra, by simpa using hrt⟩
      · rcases hs with h | ⟨hsa, hst⟩
        · exact absurd h has
        · by_cases har : a = r
          · subst har; exact ⟨hsa, by simp [has]⟩
          · rcases hr with h | ⟨hra, hrt⟩
            · exact absurd h har
            · obtain ⟨hcom, hpop⟩ := canStart_two hsr hst hrt
              exact ⟨hcom, by simp [has, har, hra, hpop]⟩
