module

public import RequestProject.CellComplex

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb

universe u v

variable {X Y Z : Complex2.{u}}

def revGerm (eb : X.E × Bool) : X.E × Bool := (eb.1, !eb.2)

@[simp] theorem revGerm_revGerm (eb : X.E × Bool) : revGerm (X := X) (revGerm eb) = eb := by
  rcases eb with ⟨_, _ | _⟩ <;> rfl

@[simp] theorem germSrc_revGerm (eb : X.E × Bool) :
    germSrc X.src X.tgt (revGerm (X := X) eb) = germTgt X.src X.tgt eb := by
  rcases eb with ⟨_, _ | _⟩ <;> rfl

@[simp] theorem germTgt_revGerm (eb : X.E × Bool) :
    germTgt X.src X.tgt (revGerm (X := X) eb) = germSrc X.src X.tgt eb := by
  rcases eb with ⟨_, _ | _⟩ <;> rfl

def revPath (p : List (X.E × Bool)) : List (X.E × Bool) := (p.map revGerm).reverse

@[simp] theorem revPath_nil : revPath ([] : List (X.E × Bool)) = [] := rfl

@[simp] theorem revPath_cons (eb : X.E × Bool) (p : List (X.E × Bool)) :
    revPath (eb :: p) = revPath p ++ [revGerm eb] := by simp [revPath]

theorem revPath_append (p q : List (X.E × Bool)) :
    revPath (p ++ q) = revPath q ++ revPath p := by simp [revPath]

@[simp] theorem revPath_revPath (p : List (X.E × Bool)) : revPath (revPath p) = p := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [revPath_append, ih]

theorem isPath_append_iff {p q : List (X.E × Bool)} {a c : X.V} :
    IsPath X.src X.tgt (p ++ q) a c ↔
      ∃ b, IsPath X.src X.tgt p a b ∧ IsPath X.src X.tgt q b c := by
  induction p generalizing a with
  | nil => exact ⟨fun h => ⟨a, rfl, h⟩, fun ⟨_, rfl, h⟩ => h⟩
  | cons _ _ ih =>
      exact ⟨fun ⟨ha, hr⟩ => let ⟨b, h1, h2⟩ := ih.mp hr; ⟨b, ⟨ha, h1⟩, h2⟩,
             fun ⟨b, ⟨ha, h1⟩, h2⟩ => ⟨ha, ih.mpr ⟨b, h1, h2⟩⟩⟩

theorem isPath_single (eb : X.E × Bool) :
    IsPath X.src X.tgt [eb] (germSrc X.src X.tgt eb) (germTgt X.src X.tgt eb) := ⟨rfl, rfl⟩

theorem isPath_revPath {p : List (X.E × Bool)} {a b : X.V}
    (hp : IsPath X.src X.tgt p a b) : IsPath X.src X.tgt (revPath p) b a := by
  induction p generalizing a with
  | nil => exact hp.symm
  | cons eb _ ih =>
      obtain ⟨rfl, hrest⟩ := hp
      rw [revPath_cons]
      exact isPath_append_iff.mpr ⟨_, ih hrest, by simp, by simp⟩

def Cancels (X : Complex2.{u}) (l l' : List (X.E × Bool)) : Prop :=
  (∃ (p q : List (X.E × Bool)) (eb : X.E × Bool),
      l = p ++ eb :: revGerm eb :: q ∧ l' = p ++ q) ∨
  (∃ (p q : List (X.E × Bool)) (f : X.F), l = p ++ X.att f ++ q ∧ l' = p ++ q)

def Step (X : Complex2.{u}) (a b : X.V) (l l' : List (X.E × Bool)) : Prop :=
  IsPath X.src X.tgt l a b ∧ IsPath X.src X.tgt l' a b ∧ Cancels X l l'

def Htpy (X : Complex2.{u}) (a b : X.V) (p q : List (X.E × Bool)) : Prop :=
  Relation.ReflTransGen (fun l l' => Step X a b l l' ∨ Step X a b l' l) p q

namespace Htpy

variable {a b c : X.V}

@[refl] theorem refl (p : List (X.E × Bool)) : Htpy X a b p p := Relation.ReflTransGen.refl

theorem trans {p q r : List (X.E × Bool)} (h : Htpy X a b p q) (h' : Htpy X a b q r) :
    Htpy X a b p r := Relation.ReflTransGen.trans h h'

theorem symm {p q : List (X.E × Bool)} (h : Htpy X a b p q) : Htpy X a b q p := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact Relation.ReflTransGen.trans (.single hstep.symm) ih

theorem of_step {p q : List (X.E × Bool)} (h : Step X a b p q) : Htpy X a b p q :=
  .single (.inl h)

theorem isPath {p q : List (X.E × Bool)} (h : Htpy X a b p q)
    (hp : IsPath X.src X.tgt p a b) : IsPath X.src X.tgt q a b := by
  induction h with
  | refl => exact hp
  | tail _ hstep _ => rcases hstep with h | h; exact h.2.1; exact h.1

end Htpy

theorem Cancels.append {l l' : List (X.E × Bool)} (h : Cancels X l l')
    (r s : List (X.E × Bool)) : Cancels X (r ++ l ++ s) (r ++ l' ++ s) := by
  rcases h with ⟨p, q, eb, rfl, rfl⟩ | ⟨p, q, f, rfl, rfl⟩
  · exact .inl ⟨r ++ p, q ++ s, eb, by simp, by simp⟩
  · exact .inr ⟨r ++ p, q ++ s, f, by simp, by simp⟩

theorem Step.append {a b c d : X.V} {l l' : List (X.E × Bool)} (h : Step X a b l l')
    {r s : List (X.E × Bool)} (hr : IsPath X.src X.tgt r c a) (hs : IsPath X.src X.tgt s b d) :
    Step X c d (r ++ l ++ s) (r ++ l' ++ s) :=
  ⟨by rw [List.append_assoc]; exact isPath_append_iff.mpr ⟨a, hr, isPath_append_iff.mpr ⟨b, h.1, hs⟩⟩,
   by rw [List.append_assoc]; exact isPath_append_iff.mpr ⟨a, hr, isPath_append_iff.mpr ⟨b, h.2.1, hs⟩⟩,
   h.2.2.append r s⟩

theorem Htpy.congr_append {a b c d : X.V} {p q : List (X.E × Bool)} (h : Htpy X a b p q)
    {r s : List (X.E × Bool)} (hr : IsPath X.src X.tgt r c a) (hs : IsPath X.src X.tgt s b d) :
    Htpy X c d (r ++ p ++ s) (r ++ q ++ s) := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.tail (hstep.imp (·.append hr hs) (·.append hr hs))

theorem Htpy.append_congr {a b c : X.V} {p p' q q' : List (X.E × Bool)}
    (hp : IsPath X.src X.tgt p a b) (hq : IsPath X.src X.tgt q b c)
    (h : Htpy X a b p p') (h' : Htpy X b c q q') :
    Htpy X a c (p ++ q) (p' ++ q') :=
  (by simpa using h.congr_append (r := []) (s := q) rfl hq : Htpy X a c (p ++ q) (p' ++ q)).trans
    (by simpa using h'.congr_append (r := p') (s := []) (h.isPath hp) rfl)

theorem htpy_append_revPath {p : List (X.E × Bool)} {a b : X.V}
    (hp : IsPath X.src X.tgt p a b) : Htpy X a a (p ++ revPath p) [] := by
  induction p generalizing a with
  | nil => cases hp; rfl
  | cons eb p ih =>
      obtain ⟨rfl, hrest⟩ := hp
      have hcongr := (ih hrest).congr_append (isPath_single eb)
        (d := germSrc X.src X.tgt eb) (s := [revGerm eb]) ⟨by simp, by simp⟩
      have hlast : Htpy X _ _ [eb, revGerm eb] [] :=
        .of_step ⟨⟨rfl, by simp, by simp⟩, rfl, .inl ⟨[], [], eb, rfl, rfl⟩⟩
      simpa using hcongr.trans (by simpa using hlast)

theorem htpy_revPath_append {p : List (X.E × Bool)} {a b : X.V}
    (hp : IsPath X.src X.tgt p a b) : Htpy X b b (revPath p ++ p) [] := by
  simpa using htpy_append_revPath (isPath_revPath hp)

theorem htpy_revPath {p q : List (X.E × Bool)} {a b : X.V} (hp : IsPath X.src X.tgt p a b)
    (h : Htpy X a b p q) : Htpy X b a (revPath p) (revPath q) := by
  have hq := h.isPath hp
  have hrp := isPath_revPath hp
  have h1 := Htpy.append_congr (q := []) hrp rfl (.refl _) (htpy_append_revPath hq).symm
  have h3 := (Htpy.append_congr hrp hq (.refl _) h.symm).trans (htpy_revPath_append hp)
  have h2 := Htpy.append_congr (isPath_append_iff.mpr ⟨a, hrp, hq⟩) (isPath_revPath hq) h3 (.refl _)
  rw [List.append_assoc] at h2
  simpa using h1.trans h2

def Loop (X : Complex2.{u}) (a : X.V) : Type u :=
  {p : List (X.E × Bool) // IsPath X.src X.tgt p a a}

instance loopSetoid (X : Complex2.{u}) (a : X.V) : Setoid (Loop X a) where
  r p q := Htpy X a a p.1 q.1
  iseqv := ⟨fun p => .refl p.1, Htpy.symm, Htpy.trans⟩

def Pi1 (X : Complex2.{u}) (a : X.V) : Type u := Quotient (loopSetoid X a)

namespace Pi1

variable {a : X.V}

def mk (p : Loop X a) : Pi1 X a := Quotient.mk _ p

instance : One (Pi1 X a) := ⟨mk ⟨[], rfl⟩⟩

instance : Mul (Pi1 X a) :=
  ⟨Quotient.map₂ (fun p q => ⟨p.1 ++ q.1, isPath_append_iff.mpr ⟨a, p.2, q.2⟩⟩)
    (fun p _ h q _ h' => Htpy.append_congr p.2 q.2 h h')⟩

instance : Inv (Pi1 X a) :=
  ⟨Quotient.map (fun p => ⟨revPath p.1, isPath_revPath p.2⟩)
    (fun p _ h => htpy_revPath p.2 h)⟩

instance : Group (Pi1 X a) where
  mul_assoc := by
    rintro ⟨p⟩ ⟨q⟩ ⟨r⟩; apply Quotient.sound
    change Htpy X a a ((p.1 ++ q.1) ++ r.1) (p.1 ++ (q.1 ++ r.1))
    rw [List.append_assoc]
  one_mul := by rintro ⟨_⟩; exact Quotient.sound (.refl _)
  mul_one := by
    rintro ⟨p⟩; apply Quotient.sound
    change Htpy X a a (p.1 ++ []) p.1
    rw [List.append_nil]
  inv_mul_cancel := by rintro ⟨p⟩; exact Quotient.sound (htpy_revPath_append p.2)

end Pi1

def SimplyConnected (X : Complex2.{u}) : Prop :=
  ∀ (a : X.V) (p : List (X.E × Bool)), IsPath X.src X.tgt p a a → Htpy X a a p []

def mapPath (h : Hom X Y) (p : List (X.E × Bool)) : List (Y.E × Bool) :=
  p.map (fun eb => (h.onE eb.1, eb.2))

@[simp] theorem mapPath_nil (h : Hom X Y) : mapPath h ([] : List (X.E × Bool)) = [] := rfl

@[simp] theorem mapPath_append (h : Hom X Y) (p q : List (X.E × Bool)) :
    mapPath h (p ++ q) = mapPath h p ++ mapPath h q := by simp [mapPath]

theorem germTgt_onE (h : Hom X Y) (eb : X.E × Bool) :
    germTgt Y.src Y.tgt (h.onE eb.1, eb.2) = h.onV (germTgt X.src X.tgt eb) := by
  rcases eb with ⟨_, _ | _⟩ <;> simp [germTgt, h.src_onE, h.tgt_onE]

theorem isPath_mapPath (h : Hom X Y) {p : List (X.E × Bool)} {a b : X.V}
    (hp : IsPath X.src X.tgt p a b) : IsPath Y.src Y.tgt (mapPath h p) (h.onV a) (h.onV b) := by
  induction p generalizing a with
  | nil => exact congrArg h.onV hp
  | cons eb _ ih =>
      obtain ⟨rfl, hrest⟩ := hp
      exact ⟨(germSrc_onE h eb).symm, (germTgt_onE h eb).symm ▸ ih hrest⟩

theorem mapPath_htpy (h : Hom X Y) {a b : X.V} {p q : List (X.E × Bool)}
    (hpq : Htpy X a b p q) :
    Htpy Y (h.onV a) (h.onV b) (mapPath h p) (mapPath h q) := by
  have hstep {l l' : List (X.E × Bool)} (hs : Step X a b l l') :
      Step Y (h.onV a) (h.onV b) (mapPath h l) (mapPath h l') := by
    obtain ⟨hl, hl', hc⟩ := hs
    refine ⟨isPath_mapPath h hl, isPath_mapPath h hl', ?_⟩
    rcases hc with ⟨p', q', eb, rfl, rfl⟩ | ⟨p', q', f, rfl, rfl⟩
    · exact .inl ⟨mapPath h p', mapPath h q', (h.onE eb.1, eb.2), by simp [mapPath, revGerm], by simp⟩
    · refine .inr ⟨mapPath h p', mapPath h q', h.onF f, ?_, by simp⟩
      have hatt : mapPath h (X.att f) = Y.att (h.onF f) := (h.att_onF f).symm
      simp [hatt]
  induction hpq with
  | refl => rfl
  | tail _ hs ih =>
      rcases hs with hel | hel
      · exact ih.trans (.of_step (hstep hel))
      · exact ih.trans (Htpy.of_step (hstep hel)).symm

def pi1Map (h : Hom X Y) (a : X.V) : Pi1 X a →* Pi1 Y (h.onV a) where
  toFun := Quotient.map (fun p => ⟨mapPath h p.1, isPath_mapPath h p.2⟩)
    (fun _ _ hpq => mapPath_htpy h hpq)
  map_one' := Quotient.sound (.refl [])
  map_mul' := by
    rintro ⟨p⟩ ⟨q⟩; apply Quotient.sound
    change Htpy Y (h.onV a) (h.onV a) (mapPath h (p.1 ++ q.1)) (mapPath h p.1 ++ mapPath h q.1)
    rw [mapPath_append]

def Pi1Trivial (h : Hom X Y) : Prop :=
  ∀ (a : X.V) (p : List (X.E × Bool)), IsPath X.src X.tgt p a a →
    Htpy Y (h.onV a) (h.onV a) (mapPath h p) []
