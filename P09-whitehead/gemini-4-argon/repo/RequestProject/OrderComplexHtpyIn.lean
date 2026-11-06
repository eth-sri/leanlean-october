module

public import RequestProject.OrderComplexGluing

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb

universe u

variable {P Q : Type u} [Preorder P] [Preorder Q]

def StepIn (A : P → Prop) (a b : P) (l l' : List ((orderCx P).E × Bool)) : Prop :=
  Step (orderCx P) a b l l' ∧ PathIn A l ∧ PathIn A l'

def HtpyIn (A : P → Prop) (a b : P) (p q : List ((orderCx P).E × Bool)) : Prop :=
  Relation.ReflTransGen (fun l l' => StepIn A a b l l' ∨ StepIn A a b l' l) p q

namespace HtpyIn

variable {A B : P → Prop} {a b c d : P} {p q r : List ((orderCx P).E × Bool)}

@[refl] theorem refl (p : List ((orderCx P).E × Bool)) : HtpyIn A a b p p :=
  Relation.ReflTransGen.refl

theorem trans (h : HtpyIn A a b p q) (h' : HtpyIn A a b q r) : HtpyIn A a b p r :=
  Relation.ReflTransGen.trans h h'

theorem symm (h : HtpyIn A a b p q) : HtpyIn A a b q p := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact Relation.ReflTransGen.trans (.single hstep.symm) ih

theorem of_step (h : StepIn A a b p q) : HtpyIn A a b p q := .single (.inl h)

theorem htpy (h : HtpyIn A a b p q) : Htpy (orderCx P) a b p q :=
  Relation.ReflTransGen.mono (fun _ _ hs => hs.imp (·.1) (·.1)) _ _ h

theorem mono (hAB : ∀ x, A x → B x) (h : HtpyIn A a b p q) : HtpyIn B a b p q :=
  Relation.ReflTransGen.mono
    (fun _ _ hs => hs.imp
      (fun h => ⟨h.1, pathIn_mono hAB h.2.1, pathIn_mono hAB h.2.2⟩)
      (fun h => ⟨h.1, pathIn_mono hAB h.2.1, pathIn_mono hAB h.2.2⟩)) _ _ h

theorem pathIn (h : HtpyIn A a b p q) (hp : PathIn A p) : PathIn A q := by
  induction h with
  | refl => exact hp
  | tail _ hstep _ => rcases hstep with hs | hs; exact hs.2.2; exact hs.2.1

theorem isPath (h : HtpyIn A a b p q)
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b) :
    IsPath (orderCx P).src (orderCx P).tgt q a b := Htpy.isPath h.htpy hp

end HtpyIn

theorem StepIn.append {A : P → Prop} {a b c d : P} {l l' : List ((orderCx P).E × Bool)}
    (h : StepIn A a b l l') {r s : List ((orderCx P).E × Bool)}
    (hr : IsPath (orderCx P).src (orderCx P).tgt r c a)
    (hs : IsPath (orderCx P).src (orderCx P).tgt s b d)
    (hrA : PathIn A r) (hsA : PathIn A s) :
    StepIn A c d (r ++ l ++ s) (r ++ l' ++ s) :=
  ⟨h.1.append hr hs, pathIn_append (pathIn_append hrA h.2.1) hsA,
    pathIn_append (pathIn_append hrA h.2.2) hsA⟩

theorem HtpyIn.congr_append {A : P → Prop} {a b c d : P} {p q : List ((orderCx P).E × Bool)}
    (h : HtpyIn A a b p q) {r s : List ((orderCx P).E × Bool)}
    (hr : IsPath (orderCx P).src (orderCx P).tgt r c a)
    (hs : IsPath (orderCx P).src (orderCx P).tgt s b d)
    (hrA : PathIn A r) (hsA : PathIn A s) :
    HtpyIn A c d (r ++ p ++ s) (r ++ q ++ s) := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.tail (hstep.imp (·.append hr hs hrA hsA) (·.append hr hs hrA hsA))

theorem HtpyIn.append_congr {A : P → Prop} {a b c : P} {p p' q q' : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b)
    (hq : IsPath (orderCx P).src (orderCx P).tgt q b c)
    (hpA : PathIn A p) (hqA : PathIn A q)
    (h : HtpyIn A a b p p') (h' : HtpyIn A b c q q') :
    HtpyIn A a c (p ++ q) (p' ++ q') := by
  have h1 : HtpyIn A a c (p ++ q) (p' ++ q) := by
    simpa using h.congr_append (r := []) (s := q) rfl hq (pathIn_nil A) hqA
  have h2 : HtpyIn A a c (p' ++ q) (p' ++ q') := by
    simpa using h'.congr_append (r := p') (s := []) (h.isPath hp) rfl (h.pathIn hpA) (pathIn_nil A)
  exact h1.trans h2

theorem htpyIn_append_revPath {A : P → Prop} {p : List ((orderCx P).E × Bool)} {a b : P}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b) (hpA : PathIn A p) :
    HtpyIn A a a (p ++ revPath p) [] := by
  induction p generalizing a with
  | nil => cases hp; rfl
  | cons eb p ih =>
      obtain ⟨ha, hrest⟩ := hp
      subst ha
      obtain ⟨hebA, hpA'⟩ := pathIn_of_cons hpA
      have hcongr := (ih hrest hpA').congr_append (isPath_single eb) (s := [revGerm eb])
        ⟨(germSrc_revGerm (X := orderCx P) eb).symm, germTgt_revGerm (X := orderCx P) eb⟩
        (pathIn_cons hebA (pathIn_nil A)) (pathIn_cons hebA (pathIn_nil A))
      have hlast : HtpyIn A (germSrc (orderCx P).src (orderCx P).tgt eb)
          (germSrc (orderCx P).src (orderCx P).tgt eb) [eb, revGerm eb] [] :=
        .of_step ⟨⟨⟨rfl, (germSrc_revGerm (X := orderCx P) eb).symm,
          germTgt_revGerm (X := orderCx P) eb⟩, rfl, .inl ⟨[], [], eb, rfl, rfl⟩⟩,
          pathIn_cons hebA (pathIn_cons hebA (pathIn_nil A)), pathIn_nil A⟩
      rw [show (eb :: p) ++ revPath (eb :: p) = [eb] ++ (p ++ revPath p) ++ [revGerm eb] by
        simp [revPath, List.append_assoc]]
      exact hcongr.trans (by simpa using hlast)

theorem htpyIn_revPath_append {A : P → Prop} {p : List ((orderCx P).E × Bool)} {a b : P}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b) (hpA : PathIn A p) :
    HtpyIn A b b (revPath p ++ p) [] := by
  simpa using htpyIn_append_revPath (isPath_revPath hp) (pathIn_revPath hpA)

theorem htpyIn_mapPath {C : P → Prop} (f : Q → P) (hf : Monotone f) (hC : ∀ x, C (f x))
    {a b : Q} {p q : List ((orderCx Q).E × Bool)} (h : Htpy (orderCx Q) a b p q) :
    HtpyIn C (f a) (f b) (mapPath (orderCxMap f hf) p) (mapPath (orderCxMap f hf) q) := by
  have hpathIn (l : List ((orderCx Q).E × Bool)) : PathIn C (mapPath (orderCxMap f hf) l) := by
    intro e he; simp only [mapPath, List.mem_map] at he
    obtain ⟨_, -, rfl⟩ := he; exact ⟨hC _, hC _⟩
  have hstep {l l' : List ((orderCx Q).E × Bool)} (hs : Step (orderCx Q) a b l l') :
      StepIn C (f a) (f b) (mapPath (orderCxMap f hf) l) (mapPath (orderCxMap f hf) l') := by
    obtain ⟨hl, hl', hc⟩ := hs
    refine ⟨⟨isPath_mapPath (orderCxMap f hf) hl, isPath_mapPath (orderCxMap f hf) hl', ?_⟩,
      hpathIn l, hpathIn l'⟩
    rcases hc with ⟨p', q', eb, rfl, rfl⟩ | ⟨p', q', t, rfl, rfl⟩
    · exact .inl ⟨mapPath (orderCxMap f hf) p', mapPath (orderCxMap f hf) q',
        ((orderCxMap f hf).onE eb.1, eb.2), by simp [mapPath, revGerm], by simp [mapPath]⟩
    · exact .inr ⟨mapPath (orderCxMap f hf) p', mapPath (orderCxMap f hf) q',
        (orderCxMap f hf).onF t, by simp [mapPath, orderCxMap, orderCx], by simp [mapPath]⟩
  induction h with
  | refl => rfl
  | tail _ hs ih =>
      rcases hs with hel | hel
      · exact ih.trans (.of_step (hstep hel))
      · exact ih.trans (HtpyIn.of_step (hstep hel)).symm

variable {C : P → Prop}

theorem liftPathIn_append (l l' : List ((orderCx P).E × Bool)) (h : PathIn C l)
    (h' : PathIn C l') (hall : PathIn C (l ++ l')) :
    liftPathIn (A := C) (l ++ l') hall = liftPathIn l h ++ liftPathIn l' h' := by
  induction l with
  | nil => rfl
  | cons _ _ ih =>
      simp only [List.cons_append, liftPathIn, List.cons.injEq, true_and]
      exact ih (pathIn_of_cons h).2 (pathIn_of_cons hall).2

theorem htpy_lift_of_htpyIn {a b : P} {p q : List ((orderCx P).E × Bool)}
    (h : HtpyIn C a b p q) (ha : C a) (hb : C b) (hp : PathIn C p) (hq : PathIn C q) :
    Htpy (orderCx {x : P // C x}) ⟨a, ha⟩ ⟨b, hb⟩ (liftPathIn p hp) (liftPathIn q hq) := by
  have hstep {l l' : List ((orderCx P).E × Bool)} (hl : PathIn C l) (hl' : PathIn C l')
      (hs : StepIn C a b l l') :
      Step (orderCx {x : P // C x}) ⟨a, ha⟩ ⟨b, hb⟩ (liftPathIn l hl) (liftPathIn l' hl') := by
    obtain ⟨⟨hpl, hpl', hc⟩, -, -⟩ := hs
    refine ⟨isPath_liftPathIn l hl ha hb hpl, isPath_liftPathIn l' hl' ha hb hpl', ?_⟩
    rcases hc with ⟨p', q', eb, rfl, rfl⟩ | ⟨p', q', t, rfl, rfl⟩
    · have hp' := pathIn_of_append_left hl
      have hrest := pathIn_of_append_right hl
      have hq' := (pathIn_of_cons (pathIn_of_cons hrest).2).2
      exact .inl ⟨liftPathIn p' hp', liftPathIn q' hq', liftGermIn eb (pathIn_of_cons hrest).1,
        by rw [liftPathIn_append p' (eb :: revGerm eb :: q') hp' hrest]; rfl,
        liftPathIn_append p' q' hp' hq' _⟩
    · have hfront := pathIn_of_append_left hl
      have hp' := pathIn_of_append_left hfront
      have hatt := pathIn_of_append_right hfront
      have hq' := pathIn_of_append_right hl
      have h1 := hatt ((⟨(t.1.1, t.1.2.1), t.2.1⟩ : OrdEdge P), true) (by simp [orderCx])
      have h2 := hatt ((⟨(t.1.2.1, t.1.2.2), t.2.2⟩ : OrdEdge P), true) (by simp [orderCx])
      refine .inr ⟨liftPathIn p' hp', liftPathIn q' hq',
        ⟨(⟨t.1.1, h1.1⟩, ⟨t.1.2.1, h1.2⟩, ⟨t.1.2.2, h2.2⟩), t.2.1, t.2.2⟩, ?_,
        liftPathIn_append p' q' hp' hq' _⟩
      rw [liftPathIn_append (p' ++ (orderCx P).att t) q' hfront hq',
        liftPathIn_append p' ((orderCx P).att t) hp' hatt]; rfl
  revert hq
  induction h with
  | refl => intro _; rfl
  | @tail u v _ hs ih =>
      intro hq
      have hu : PathIn C u := by rcases hs with h' | h'; exact h'.2.1; exact h'.2.2
      refine (ih hu).trans ?_
      rcases hs with h' | h'
      · exact .of_step (hstep hu hq h')
      · exact (Htpy.of_step (hstep hq hu h')).symm
