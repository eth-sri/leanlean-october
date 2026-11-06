module

public import RequestProject.RACGTrace

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FiniteChains.RACG

universe u

structure CommRel (V : Type u) where
  rel : V → V → Prop
  rel_symm : ∀ {a b : V}, rel a b → rel b a
  rel_irrefl : ∀ a : V, ¬ rel a a

variable {V : Type u} [DecidableEq V] (A : CommRel V)

def redSetoid : Setoid {l : List V // IsRed A.rel l} where
  r a b := CEq A.rel a.1 b.1
  iseqv := ⟨fun _ => CEq.refl _, fun h => CEq.symm A.rel_symm h, fun h h' => h.trans h'⟩

def Tr : Type u := Quotient (redSetoid A)

def mkTr (l : List V) (h : IsRed A.rel l) : Tr A := Quotient.mk (redSetoid A) ⟨l, h⟩

def oneTr : Tr A := mkTr A [] trivial

def trLen : Tr A → ℕ :=
  Quotient.lift (fun l : {l : List V // IsRed A.rel l} => l.1.length)
    (fun _ _ h => CEq.length_eq h)

omit [DecidableEq V] in
@[simp] theorem trLen_mkTr (l : List V) (h : IsRed A.rel l) : trLen A (mkTr A l h) = l.length :=
  rfl

open Classical in
def actRep (s : V) (l : {l : List V // IsRed A.rel l}) : {l : List V // IsRed A.rel l} :=
  if h : canStart A.rel s l.1 then
    ⟨popStart s l.1, isRed_popStart A.rel_irrefl A.rel_symm l.2 h⟩
  else ⟨s :: l.1, ⟨l.2, h⟩⟩

theorem actRep_of_canStart {s : V} {l : {l : List V // IsRed A.rel l}}
    (h : canStart A.rel s l.1) : (actRep A s l).1 = popStart s l.1 := by
  classical simp [actRep, h]

theorem actRep_of_not_canStart {s : V} {l : {l : List V // IsRed A.rel l}}
    (h : ¬ canStart A.rel s l.1) : (actRep A s l).1 = s :: l.1 := by
  classical simp [actRep, h]

def act (s : V) : Tr A → Tr A :=
  Quotient.map (actRep A s) fun a b h => by
    classical
    show CEq A.rel (actRep A s a).1 (actRep A s b).1
    by_cases ha : canStart A.rel s a.1
    · rw [actRep_of_canStart A ha, actRep_of_canStart A ((canStart_ceq A.rel_symm h).1 ha)]
      exact popStart_ceq A.rel_irrefl h
    · rw [actRep_of_not_canStart A ha,
        actRep_of_not_canStart A (fun hb => ha ((canStart_ceq A.rel_symm h).2 hb))]
      exact CEq.cons s h

theorem act_involutive (s : V) : Function.Involutive (act A s) := by
  classical
  intro t
  induction t using Quotient.inductionOn with | _ l =>
  refine Quotient.sound ?_
  show CEq A.rel (actRep A s (actRep A s l)).1 l.1
  by_cases h : canStart A.rel s l.1
  · have h1 := actRep_of_canStart A h
    rw [actRep_of_not_canStart A (h1 ▸ not_canStart_popStart A.rel_irrefl A.rel_symm l.2 h), h1]
    exact CEq.symm A.rel_symm (ceq_popStart A.rel_symm h)
  · have h1 := actRep_of_not_canStart A h
    rw [actRep_of_canStart A (h1.symm ▸ Or.inl rfl), h1]; simp [CEq.refl]

def actPerm (s : V) : Equiv.Perm (Tr A) := (act_involutive A s).toPerm _

@[simp] theorem actPerm_apply (s : V) (t : Tr A) : actPerm A s t = act A s t := rfl

theorem actPerm_mul_self (s : V) : actPerm A s * actPerm A s = 1 := by
  ext t; simpa using act_involutive A s t

theorem act_mkTr_of_canStart {s : V} {l : List V} (hl : IsRed A.rel l)
    (h : canStart A.rel s l) :
    act A s (mkTr A l hl) = mkTr A (popStart s l) (isRed_popStart A.rel_irrefl A.rel_symm hl h) :=
  Quotient.sound (by show CEq A.rel (actRep A s ⟨l, hl⟩).1 _; rw [actRep_of_canStart A h]; exact CEq.refl _)

theorem act_mkTr_of_not_canStart {s : V} {l : List V} (hl : IsRed A.rel l)
    (h : ¬ canStart A.rel s l) :
    act A s (mkTr A l hl) = mkTr A (s :: l) ⟨hl, h⟩ :=
  Quotient.sound (by show CEq A.rel (actRep A s ⟨l, hl⟩).1 _; rw [actRep_of_not_canStart A h]; exact CEq.refl _)

theorem act_comm {s r : V} (h : A.rel s r) (t : Tr A) :
    act A s (act A r t) = act A r (act A s t) := by
  have hrs : A.rel r s := A.rel_symm h
  have hsr : s ≠ r := fun he => A.rel_irrefl s (he ▸ h)
  induction t using Quotient.inductionOn with | _ lp =>
  obtain ⟨l, hl⟩ := lp
  show act A s (act A r (mkTr A l hl)) = act A r (act A s (mkTr A l hl))
  have one_can {u v : V} (huv : A.rel u v) (hu : canStart A.rel u l) (hv : ¬ canStart A.rel v l) :
      act A u (act A v (mkTr A l hl)) = act A v (act A u (mkTr A l hl)) := by
    have hvu := A.rel_symm huv
    have huv_ne : u ≠ v := fun he => A.rel_irrefl u (he ▸ huv)
    have hv' : ¬ canStart A.rel v (popStart u l) := fun hc =>
      hv ((canStart_ceq A.rel_symm (ceq_popStart A.rel_symm hu)).2 (Or.inr ⟨hvu, hc⟩))
    have hu' : canStart A.rel u (v :: l) := Or.inr ⟨huv, hu⟩
    rw [act_mkTr_of_not_canStart A hl hv, act_mkTr_of_canStart A _ hu',
      act_mkTr_of_canStart A hl hu, act_mkTr_of_not_canStart A _ hv']
    exact Quotient.sound (by show CEq A.rel (popStart u (v :: l)) _; simp [popStart, Ne.symm huv_ne, CEq.refl])
  by_cases hs : canStart A.rel s l
  · by_cases hr : canStart A.rel r l
    · obtain ⟨-, hrs'⟩ := canStart_two A.rel_symm hsr hs hr
      obtain ⟨-, hsr'⟩ := canStart_two A.rel_symm (Ne.symm hsr) hr hs
      rw [act_mkTr_of_canStart A hl hr, act_mkTr_of_canStart A _ hsr',
        act_mkTr_of_canStart A hl hs, act_mkTr_of_canStart A _ hrs']
      refine Quotient.sound ?_
      have e1 := (ceq_popStart A.rel_symm hs).trans (CEq.cons s (ceq_popStart A.rel_symm hrs'))
      have e2 := (ceq_popStart A.rel_symm hr).trans (CEq.cons r (ceq_popStart A.rel_symm hsr'))
      exact CEq.symm A.rel_symm (cancel_head A.rel_irrefl (cancel_head A.rel_irrefl
        ((CEq.symm A.rel_symm (e1.trans (CEq.of_swap (Swap.head h _)))).trans e2)))
    · exact one_can h hs hr
  · by_cases hr : canStart A.rel r l
    · exact (one_can hrs hr hs).symm
    · have hs' : ¬ canStart A.rel s (r :: l) := by rintro (rfl | ⟨-, hc⟩); exacts [hsr rfl, hs hc]
      have hr' : ¬ canStart A.rel r (s :: l) := by rintro (rfl | ⟨-, hc⟩); exacts [hsr rfl, hr hc]
      rw [act_mkTr_of_not_canStart A hl hr, act_mkTr_of_not_canStart A _ hs',
        act_mkTr_of_not_canStart A hl hs, act_mkTr_of_not_canStart A _ hr']
      exact Quotient.sound (CEq.of_swap (Swap.head h l))

def wordPerm (l : List V) : Equiv.Perm (Tr A) := (l.map (actPerm A)).prod

@[simp] theorem wordPerm_nil : wordPerm A [] = 1 := rfl

@[simp] theorem wordPerm_singleton (s : V) : wordPerm A [s] = actPerm A s := by simp [wordPerm]

@[simp] theorem wordPerm_cons (s : V) (l : List V) :
    wordPerm A (s :: l) = actPerm A s * wordPerm A l := by simp [wordPerm]

theorem wordPerm_append (l m : List V) :
    wordPerm A (l ++ m) = wordPerm A l * wordPerm A m := by
  induction l <;> simp [*, mul_assoc]

theorem wordPerm_reverse (l : List V) : wordPerm A l.reverse = (wordPerm A l)⁻¹ := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.reverse_cons, wordPerm_append, ih, wordPerm_cons A a t, mul_inv_rev,
        inv_eq_of_mul_eq_one_left (actPerm_mul_self A a)]
      simp

theorem wordPerm_swap {l m : List V} (h : Swap A.rel l m) : wordPerm A l = wordPerm A m := by
  induction h with
  | head hab =>
      simp only [wordPerm_cons, ← mul_assoc]
      rw [show actPerm A _ * actPerm A _ = actPerm A _ * actPerm A _ by ext t; simpa using act_comm A hab t]
  | cons _ _ ih => simp only [wordPerm_cons, ih]

theorem wordPerm_ceq {l m : List V} (h : CEq A.rel l m) : wordPerm A l = wordPerm A m := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (wordPerm_swap A hstep)

theorem wordPerm_apply_one : ∀ {l : List V} (h : IsRed A.rel l),
    wordPerm A l (oneTr A) = mkTr A l h
  | [], _ => rfl
  | a :: t, ⟨ht, hna⟩ => by
      rw [show wordPerm A (a :: t) (oneTr A) = act A a (wordPerm A t (oneTr A)) by simp [wordPerm_cons],
        wordPerm_apply_one ht, act_mkTr_of_not_canStart A ht hna]

theorem exists_shorter_of_not_isRed :
    ∀ {l : List V}, ¬ IsRed A.rel l →
      ∃ m : List V, m.length < l.length ∧ wordPerm A m = wordPerm A l
  | [], h => absurd isRed_nil h
  | a :: t, h => by
      by_cases hc : canStart A.rel a t
      · refine ⟨popStart a t, by have := length_popStart A.rel_symm (Cm := A.rel) (s := a) hc; simp; omega, ?_⟩
        rw [← one_mul (wordPerm A (popStart a t)), ← actPerm_mul_self A a, mul_assoc,
          ← wordPerm_cons, ← wordPerm_ceq A (ceq_popStart A.rel_symm hc), ← wordPerm_cons]
      · obtain ⟨m, hm, hm'⟩ := exists_shorter_of_not_isRed (fun ht => h ⟨ht, hc⟩)
        exact ⟨a :: m, by simpa using hm, by simp [wordPerm_cons, hm']⟩

theorem exists_isRed_word (l : List V) :
    ∃ m : List V, IsRed A.rel m ∧ m.length ≤ l.length ∧ wordPerm A m = wordPerm A l := by
  induction hn : l.length using Nat.strong_induction_on generalizing l with | _ n ih =>
  subst hn
  by_cases hred : IsRed A.rel l
  · exact ⟨l, hred, le_rfl, rfl⟩
  · obtain ⟨m, hlt, hperm⟩ := exists_shorter_of_not_isRed A hred
    obtain ⟨m', hm', hlen, hperm'⟩ := ih m.length hlt m rfl
    exact ⟨m', hm', by omega, hperm'.trans hperm⟩

def len (w : Equiv.Perm (Tr A)) : ℕ := trLen A (w (oneTr A))

theorem len_le_length : ∀ l : List V, len A (wordPerm A l) ≤ l.length
  | [] => by simp [len, oneTr]
  | a :: t => by
      have ih := len_le_length t
      have hact : trLen A (act A a (wordPerm A t (oneTr A))) ≤ trLen A (wordPerm A t (oneTr A)) + 1 := by
        rcases Quotient.exists_rep (wordPerm A t (oneTr A)) with ⟨⟨m, hm⟩, hrep⟩
        rw [← hrep]
        change trLen A (act A a (mkTr A m hm)) ≤ trLen A (mkTr A m hm) + 1
        by_cases hc : canStart A.rel a m
        · rw [act_mkTr_of_canStart A hm hc]; have := length_popStart A.rel_symm hc; simp; omega
        · rw [act_mkTr_of_not_canStart A hm hc]; simp
      simpa only [len, wordPerm_cons, Equiv.Perm.mul_apply, actPerm_apply, List.length_cons] using
        hact.trans (Nat.add_le_add_right ih 1)
