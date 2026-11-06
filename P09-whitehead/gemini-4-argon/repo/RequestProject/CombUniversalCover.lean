module

public import RequestProject.CombPi1

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb

universe u

variable {X : Complex2.{u}}

def endpt (X : Complex2.{u}) : X.V → List (X.E × Bool) → X.V
  | a, [] => a
  | _, eb :: t => endpt X (germTgt X.src X.tgt eb) t

@[simp] theorem endpt_nil (a : X.V) : endpt X a [] = a := rfl

@[simp] theorem endpt_cons (a : X.V) (eb : X.E × Bool) (t : List (X.E × Bool)) :
    endpt X a (eb :: t) = endpt X (germTgt X.src X.tgt eb) t := rfl

theorem endpt_eq_of_isPath {p : List (X.E × Bool)} {a b : X.V}
    (h : IsPath X.src X.tgt p a b) : endpt X a p = b := by
  induction p generalizing a with
  | nil => exact h
  | cons _ _ ih => exact ih h.2

theorem endpt_append (a : X.V) (p q : List (X.E × Bool)) :
    endpt X a (p ++ q) = endpt X (endpt X a p) q := by
  induction p generalizing a with
  | nil => rfl
  | cons eb _ ih => exact ih (germTgt X.src X.tgt eb)

variable (X) in
def PathFrom (x₀ : X.V) : Type u :=
  {p : List (X.E × Bool) // IsPath X.src X.tgt p x₀ (endpt X x₀ p)}

variable {x₀ : X.V}

instance pathFromSetoid (X : Complex2.{u}) (x₀ : X.V) : Setoid (PathFrom X x₀) where
  r p q := Htpy X x₀ (endpt X x₀ p.1) p.1 q.1
  iseqv := ⟨fun _ => .refl _,
    fun {p _} h => endpt_eq_of_isPath (h.isPath p.2) ▸ h.symm,
    fun {p _ _} h h' => h.trans (endpt_eq_of_isPath (h.isPath p.2) ▸ h')⟩

variable (X) in
def UV (x₀ : X.V) : Type u := Quotient (pathFromSetoid X x₀)

def UV.mk (p : PathFrom X x₀) : UV X x₀ := Quotient.mk _ p

@[elab_as_elim] theorem UV.ind {motive : UV X x₀ → Prop} (h : ∀ p, motive (UV.mk p)) :
    ∀ c, motive c := Quotient.ind h

theorem UV.sound {p q : PathFrom X x₀} (h : Htpy X x₀ (endpt X x₀ p.1) p.1 q.1) :
    UV.mk p = UV.mk q := Quotient.sound h

def UV.base (X : Complex2.{u}) (x₀ : X.V) : UV X x₀ := UV.mk ⟨[], rfl⟩

def endV (c : UV X x₀) : X.V :=
  Quotient.liftOn c (fun p => endpt X x₀ p.1) fun p _ h =>
    (endpt_eq_of_isPath (h.isPath p.2)).symm

@[simp] theorem endV_mk (p : PathFrom X x₀) : endV (UV.mk p) = endpt X x₀ p.1 := rfl

@[simp] theorem endV_base : endV (UV.base X x₀) = x₀ := rfl

theorem endpt_append_single (a : X.V) (p : List (X.E × Bool)) (eb : X.E × Bool)
    (h : endpt X a p = germSrc X.src X.tgt eb) :
    endpt X a (p ++ [eb]) = germTgt X.src X.tgt eb := by
  rw [endpt_append, h]; rfl

theorem isPath_append_single {p : List (X.E × Bool)} {a : X.V}
    (hp : IsPath X.src X.tgt p a (endpt X a p)) (eb : X.E × Bool)
    (h : endpt X a p = germSrc X.src X.tgt eb) :
    IsPath X.src X.tgt (p ++ [eb]) a (endpt X a (p ++ [eb])) := by
  rw [endpt_append_single a p eb h]
  exact isPath_append_iff.mpr ⟨germSrc X.src X.tgt eb, h ▸ hp, isPath_single eb⟩

open Classical in
noncomputable def extendP (eb : X.E × Bool) (p : PathFrom X x₀) : PathFrom X x₀ :=
  if h : endpt X x₀ p.1 = germSrc X.src X.tgt eb then ⟨p.1 ++ [eb], isPath_append_single p.2 eb h⟩
  else p

theorem extendP_pos {p : PathFrom X x₀} {eb : X.E × Bool}
    (h : endpt X x₀ p.1 = germSrc X.src X.tgt eb) : (extendP eb p).1 = p.1 ++ [eb] := by
  simp [extendP, h]

theorem extendP_neg {p : PathFrom X x₀} {eb : X.E × Bool}
    (h : ¬ endpt X x₀ p.1 = germSrc X.src X.tgt eb) : (extendP eb p).1 = p.1 := by
  simp [extendP, h]

noncomputable def extend (eb : X.E × Bool) (c : UV X x₀) : UV X x₀ :=
  Quotient.map (extendP eb) (fun p q hpq => by
    have he := endpt_eq_of_isPath (hpq.isPath p.2)
    by_cases h : endpt X x₀ p.1 = germSrc X.src X.tgt eb
    · show Htpy X x₀ (endpt X x₀ (extendP eb p).1) (extendP eb p).1 (extendP eb q).1
      rw [extendP_pos h, extendP_pos (he.trans h), endpt_append_single x₀ p.1 eb h]
      exact Htpy.append_congr (h ▸ p.2) (h ▸ isPath_single eb) hpq (.refl _)
    · show Htpy X x₀ (endpt X x₀ (extendP eb p).1) (extendP eb p).1 (extendP eb q).1
      rw [extendP_neg h, extendP_neg (fun hc => h (he ▸ hc))]
      exact hpq) c

theorem extend_mk (p : PathFrom X x₀) (eb : X.E × Bool) :
    extend eb (UV.mk p) = UV.mk (extendP eb p) := rfl

theorem endV_extend {c : UV X x₀} {eb : X.E × Bool} (h : endV c = germSrc X.src X.tgt eb) :
    endV (extend eb c) = germTgt X.src X.tgt eb := by
  induction c using UV.ind with | h p =>
  rw [extend_mk, endV_mk, extendP_pos h, endpt_append_single x₀ p.1 eb h]

theorem extend_revGerm {c : UV X x₀} {eb : X.E × Bool} (h : endV c = germSrc X.src X.tgt eb) :
    extend (revGerm eb) (extend eb c) = c := by
  induction c using UV.ind with | h p =>
  have h' : endpt X x₀ p.1 = germSrc X.src X.tgt eb := h
  have h1 : endpt X x₀ (extendP eb p).1 = germSrc X.src X.tgt (revGerm eb) := by
    simp [extendP_pos h', endpt_append_single x₀ p.1 eb h']
  refine Quotient.sound ?_
  show Htpy X x₀ (endpt X x₀ (extendP (revGerm eb) (extendP eb p)).1)
    (extendP (revGerm eb) (extendP eb p)).1 p.1
  rw [extendP_pos h1, extendP_pos h']
  have hbk : Htpy X (germSrc X.src X.tgt eb) (germSrc X.src X.tgt eb) [eb, revGerm eb] [] :=
    .of_step ⟨⟨rfl, by simp, by simp⟩, rfl, .inl ⟨[], [], eb, rfl, rfl⟩⟩
  simpa [endpt_append, h'] using
    Htpy.append_congr (h' ▸ p.2) (by refine ⟨rfl, ?_, ?_⟩ <;> simp) (.refl _) hbk

noncomputable def extendList (q : List (X.E × Bool)) (c : UV X x₀) : UV X x₀ :=
  q.foldl (fun d eb => extend eb d) c

@[simp] theorem extendList_nil (c : UV X x₀) : extendList [] c = c := rfl

@[simp] theorem extendList_cons (eb : X.E × Bool) (q : List (X.E × Bool)) (c : UV X x₀) :
    extendList (eb :: q) c = extendList q (extend eb c) := rfl

theorem extendList_append (q r : List (X.E × Bool)) (c : UV X x₀) :
    extendList (q ++ r) c = extendList r (extendList q c) := by
  induction q generalizing c with
  | nil => rfl
  | cons eb _ ih => exact ih (extend eb c)

theorem extendList_mk : ∀ {q : List (X.E × Bool)} {p r : PathFrom X x₀} {w : X.V},
    IsPath X.src X.tgt q (endpt X x₀ p.1) w → r.1 = p.1 ++ q →
      extendList q (UV.mk p) = UV.mk r
  | [], p, r, _, _, hr => Quotient.sound (by
      show Htpy X x₀ (endpt X x₀ p.1) p.1 r.1
      simpa [hr] using Htpy.refl p.1)
  | eb :: _, p, r, w, hq, hr => by
      rw [extendList_cons, extend_mk]
      exact extendList_mk (p := extendP eb p) (r := r) (w := w)
        (by rw [extendP_pos hq.1, endpt_append_single x₀ p.1 eb hq.1]; exact hq.2)
        (by simp [extendP_pos hq.1, hr])

theorem endV_extendList : ∀ {q : List (X.E × Bool)} {c : UV X x₀} {w : X.V},
    IsPath X.src X.tgt q (endV c) w → endV (extendList q c) = w
  | [], _, _, hq => hq
  | eb :: _, c, _, hq => endV_extendList (c := extend eb c) (endV_extend hq.1 ▸ hq.2)

variable (X x₀) in
def UE : Type u := {ce : UV X x₀ × X.E // endV ce.1 = X.src ce.2}

variable (X x₀) in
def UF : Type u := {cf : UV X x₀ × X.F // endV cf.1 = X.base cf.2}

def uSrc (ce : UE X x₀) : UV X x₀ := ce.1.1

noncomputable def uTgt (ce : UE X x₀) : UV X x₀ := extend (ce.1.2, true) ce.1.1

def uBase (cf : UF X x₀) : UV X x₀ := cf.1.1

noncomputable def liftGerm (c : UV X x₀) :
    (eb : X.E × Bool) → endV c = germSrc X.src X.tgt eb → UE X x₀ × Bool
  | (e, true), h => (⟨(c, e), h⟩, true)
  | (e, false), h =>
      (⟨(extend (e, false) c, e), endV_extend (c := c) (eb := (e, false)) h⟩, false)

@[simp] theorem liftGerm_true {c : UV X x₀} {e : X.E}
    (h : endV c = germSrc X.src X.tgt (e, true)) :
    liftGerm c (e, true) h = (⟨(c, e), h⟩, true) := rfl

@[simp] theorem liftGerm_false {c : UV X x₀} {e : X.E}
    (h : endV c = germSrc X.src X.tgt (e, false)) :
    liftGerm c (e, false) h =
      (⟨(extend (e, false) c, e), endV_extend (c := c) (eb := (e, false)) h⟩, false) := rfl

open Classical in
noncomputable def uLiftPath : List (X.E × Bool) → UV X x₀ → List (UE X x₀ × Bool)
  | [], _ => []
  | eb :: t, c =>
      if h : endV c = germSrc X.src X.tgt eb then
        liftGerm c eb h :: uLiftPath t (extend eb c)
      else []

@[simp] theorem uLiftPath_nil (c : UV X x₀) : uLiftPath [] c = [] := rfl

theorem uLiftPath_cons {eb : X.E × Bool} {t : List (X.E × Bool)} {c : UV X x₀}
    (h : endV c = germSrc X.src X.tgt eb) :
    uLiftPath (eb :: t) c = liftGerm c eb h :: uLiftPath t (extend eb c) :=
  dif_pos h

noncomputable def uAtt (cf : UF X x₀) : List (UE X x₀ × Bool) :=
  uLiftPath (X.att cf.1.2) cf.1.1

theorem germSrc_liftGerm {c : UV X x₀} {eb : X.E × Bool}
    (h : endV c = germSrc X.src X.tgt eb) :
    germSrc uSrc uTgt (liftGerm c eb h) = c := by
  rcases eb with ⟨e, _ | _⟩
  · exact extend_revGerm (eb := (e, false)) h
  · rfl

theorem germTgt_liftGerm {c : UV X x₀} {eb : X.E × Bool}
    (h : endV c = germSrc X.src X.tgt eb) :
    germTgt uSrc uTgt (liftGerm c eb h) = extend eb c := by
  rcases eb with ⟨_, _ | _⟩ <;> rfl

theorem isPath_uLiftPath : ∀ (q : List (X.E × Bool)) (c : UV X x₀) (w : X.V),
    IsPath X.src X.tgt q (endV c) w → IsPath uSrc uTgt (uLiftPath q c) c (extendList q c)
  | [], _, _, _ => rfl
  | eb :: t, c, w, hq => by
      rw [uLiftPath_cons hq.1, extendList_cons]
      exact ⟨(germSrc_liftGerm hq.1).symm,
        germTgt_liftGerm hq.1 ▸ isPath_uLiftPath t (extend eb c) w (endV_extend hq.1 ▸ hq.2)⟩

theorem extendList_att {c : UV X x₀} {f : X.F} (h : endV c = X.base f) :
    extendList (X.att f) c = c := by
  induction c using UV.ind with | h p =>
  have hatt : IsPath X.src X.tgt (X.att f) (endpt X x₀ p.1) (X.base f) := h ▸ X.att_isLoop f
  have hp := isPath_append_iff.mpr ⟨endpt X x₀ p.1, p.2, hatt⟩
  have hend := endpt_eq_of_isPath hp
  refine (extendList_mk (p := p) (r := ⟨p.1 ++ X.att f, hend ▸ hp⟩) hatt rfl).trans
    (Quotient.sound ?_)
  show Htpy X x₀ (endpt X x₀ (p.1 ++ X.att f)) (p.1 ++ X.att f) p.1
  rw [hend]
  exact .of_step ⟨hp, h ▸ p.2, .inr ⟨p.1, [], f, by simp, by simp⟩⟩

theorem uAtt_isLoop (cf : UF X x₀) : IsPath uSrc uTgt (uAtt cf) (uBase cf) (uBase cf) := by
  have := isPath_uLiftPath (X.att cf.1.2) cf.1.1 (X.base cf.1.2) (cf.2 ▸ X.att_isLoop cf.1.2)
  rwa [extendList_att cf.2] at this

theorem map_uLiftPath : ∀ (q : List (X.E × Bool)) (c : UV X x₀) (w : X.V),
    IsPath X.src X.tgt q (endV c) w →
      (uLiftPath q c).map (fun eb => ((eb.1 : UE X x₀).1.2, eb.2)) = q
  | [], _, _, _ => rfl
  | eb :: t, c, w, hq => by
      rw [uLiftPath_cons hq.1, List.map_cons, map_uLiftPath t (extend eb c) w (endV_extend hq.1 ▸ hq.2)]
      rcases eb with ⟨_, _ | _⟩ <;> rfl

variable (X x₀) in
noncomputable def uCover : Complex2.{u} where
  V := UV X x₀
  E := UE X x₀
  F := UF X x₀
  src := uSrc
  tgt := uTgt
  base := uBase
  att := uAtt
  att_isLoop := uAtt_isLoop

variable (X x₀) in
noncomputable def univProj : Hom (uCover X x₀) X where
  onV := endV
  onE := fun ce => ce.1.2
  onF := fun cf => cf.1.2
  src_onE := fun ce => ce.2.symm
  tgt_onE := fun ce => (endV_extend (eb := (ce.1.2, true)) ce.2).symm
  base_onF := fun cf => cf.2.symm
  att_onF := fun cf => (map_uLiftPath (X.att cf.1.2) cf.1.1 (X.base cf.1.2)
    (cf.2 ▸ X.att_isLoop cf.1.2)).symm

theorem endV_surjective (hX : IsConnected X) : Function.Surjective (endV (X := X) (x₀ := x₀)) := by
  intro v
  obtain ⟨p, hp⟩ := hX x₀ v
  exact ⟨UV.mk ⟨p, (endpt_eq_of_isPath hp).symm ▸ hp⟩, endpt_eq_of_isPath hp⟩

theorem isCovering_univProj (hX : IsConnected X) : IsCovering (univProj X x₀) := by
  refine ⟨endV_surjective hX, fun c => ⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨⟨E, b⟩, hE⟩ ⟨⟨E', b'⟩, hE'⟩ heq
    obtain ⟨he, rfl⟩ : E.1.2 = E'.1.2 ∧ b = b' := Prod.mk.inj (congrArg Subtype.val heq)
    have hEE : E = E' := by
      cases b with
      | true => exact Subtype.ext (Prod.ext (hE.trans hE'.symm) he)
      | false =>
          have k1 : E.1.1 = extend (E.1.2, false) c :=
            hE ▸ (extend_revGerm (eb := (E.1.2, true)) E.2).symm
          have k2 : E'.1.1 = extend (E'.1.2, false) c :=
            hE' ▸ (extend_revGerm (eb := (E'.1.2, true)) E'.2).symm
          exact Subtype.ext (Prod.ext (by rw [k1, k2, he]) he)
    subst hEE; rfl
  · rintro ⟨⟨e, _ | _⟩, hb⟩
    · exact ⟨⟨(⟨(extend (e, false) c, e), endV_extend hb.symm⟩, false),
        extend_revGerm (eb := (e, false)) hb.symm⟩, Subtype.ext rfl⟩
    · exact ⟨⟨(⟨(c, e), hb.symm⟩, true), rfl⟩, Subtype.ext rfl⟩
  · rintro ⟨⟨c, f⟩, h⟩ ⟨⟨c', f'⟩, h'⟩ heq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (congrArg Subtype.val heq)
    rfl
  · rintro ⟨⟨f, c⟩, h⟩
    exact ⟨⟨(c, f), h.symm⟩, rfl⟩

theorem isConnected_univCover : IsConnected (uCover X x₀) := by
  have key (c : UV X x₀) : ∃ l : List ((uCover X x₀).E × Bool),
      IsPath (uCover X x₀).src (uCover X x₀).tgt l (UV.base X x₀) c := by
    induction c using UV.ind with | h p =>
    refine ⟨uLiftPath p.1 (UV.base X x₀), ?_⟩
    have hlift := isPath_uLiftPath p.1 (UV.base X x₀) (endpt X x₀ p.1) p.2
    have hext : extendList p.1 (UV.base X x₀) = UV.mk p :=
      extendList_mk (p := ⟨[], rfl⟩) (r := p) p.2 (by simp)
    rwa [hext] at hlift
  intro c d
  obtain ⟨l, hl⟩ := key c
  obtain ⟨m, hm⟩ := key d
  exact ⟨revPath (X := uCover X x₀) l ++ m,
    isPath_append_iff (X := uCover X x₀).mpr ⟨UV.base X x₀, isPath_revPath (X := uCover X x₀) hl, hm⟩⟩

theorem uLiftPath_append : ∀ (l m : List (X.E × Bool)) (c : UV X x₀)
    (w : X.V), IsPath X.src X.tgt l (endV c) w →
      uLiftPath (l ++ m) c = uLiftPath l c ++ uLiftPath m (extendList l c)
  | [], _, _, _, _ => rfl
  | eb :: t, m, c, w, hl => by
      rw [List.cons_append, uLiftPath_cons hl.1, uLiftPath_cons hl.1, extendList_cons,
        uLiftPath_append t m (extend eb c) w (endV_extend hl.1 ▸ hl.2)]
      rfl

theorem extendList_htpy {c : UV X x₀} {l l' : List (X.E × Bool)} {w : X.V}
    (hl : IsPath X.src X.tgt l (endV c) w) (h : Htpy X (endV c) w l l') :
    extendList l c = extendList l' c := by
  induction c using UV.ind with | h p =>
  have hl' := h.isPath hl
  have hpl := isPath_append_iff.mpr ⟨endpt X x₀ p.1, p.2, hl⟩
  have hpl' := isPath_append_iff.mpr ⟨endpt X x₀ p.1, p.2, hl'⟩
  have hend := endpt_eq_of_isPath hpl
  have hend' := endpt_eq_of_isPath hpl'
  rw [extendList_mk (p := p) (r := ⟨p.1 ++ l, hend ▸ hpl⟩) hl rfl,
    extendList_mk (p := p) (r := ⟨p.1 ++ l', hend' ▸ hpl'⟩) hl' rfl]
  refine Quotient.sound ?_
  show Htpy X x₀ (endpt X x₀ (p.1 ++ l)) (p.1 ++ l) (p.1 ++ l')
  exact hend.symm ▸ Htpy.append_congr p.2 hl (.refl _) h

theorem htpy_step_uLiftPath {c : UV X x₀} {l l' : List (X.E × Bool)} {w : X.V}
    (hstep : Step X (endV c) w l l') :
    Htpy (uCover X x₀) c (extendList l c) (uLiftPath l c) (uLiftPath l' c) := by
  obtain ⟨hl, hl', hc⟩ := hstep
  have hext : extendList l' c = extendList l c := (extendList_htpy hl (.of_step ⟨hl, hl', hc⟩)).symm
  have hpath := isPath_uLiftPath l c w hl
  have hpath' : IsPath (uCover X x₀).src (uCover X x₀).tgt (uLiftPath l' c) c (extendList l c) :=
    hext ▸ isPath_uLiftPath l' c w hl'
  rcases hc with ⟨p, q, eb, rfl, rfl⟩ | ⟨p, q, f, rfl, rfl⟩
  · obtain ⟨b₁, hp, hrest⟩ := isPath_append_iff.mp hl
    have hc₁ : endV (extendList p c) = b₁ := endV_extendList hp
    set c₁ := extendList p c with hc₁def
    have h₁ : endV c₁ = germSrc X.src X.tgt eb := hc₁.trans hrest.1
    have h₂ : endV (extend eb c₁) = germSrc X.src X.tgt (revGerm eb) := by simp [endV_extend h₁]
    have hrev : liftGerm (extend eb c₁) (revGerm eb) h₂
        = revGerm (X := uCover X x₀) (liftGerm c₁ eb h₁) := by
      rcases eb with ⟨e, _ | _⟩
      · rfl
      · exact Prod.ext (Subtype.ext (Prod.ext (extend_revGerm (eb := (e, true)) h₁) rfl)) rfl
    refine Htpy.of_step ⟨hpath, hpath', .inl ⟨uLiftPath p c, uLiftPath q c₁,
      liftGerm c₁ eb h₁, ?_, uLiftPath_append p q c b₁ hp⟩⟩
    rw [uLiftPath_append p (eb :: revGerm eb :: q) c b₁ hp, ← hc₁def,
      uLiftPath_cons h₁, uLiftPath_cons h₂, hrev, extend_revGerm h₁]
  · by_cases hnil : X.att f = []
    · simp only [hnil, List.append_nil]; exact .refl _
    · obtain ⟨g, t, hgt⟩ := List.exists_cons_of_ne_nil hnil
      obtain ⟨b₂, hpa, hq⟩ := isPath_append_iff.mp hl
      obtain ⟨b₁, hp, hatt⟩ := isPath_append_iff.mp hpa
      have hc₁ : endV (extendList p c) = b₁ := endV_extendList hp
      set c₁ := extendList p c with hc₁def
      have hb₁ : b₁ = X.base f := by
        have h1 := hatt; have h2 := X.att_isLoop f; rw [hgt] at h1 h2; exact h1.1.trans h2.1.symm
      have hbase : endV c₁ = X.base f := hc₁.trans hb₁
      have hattpath : IsPath X.src X.tgt (X.att f) (endV c₁) (X.base f) := hbase ▸ X.att_isLoop f
      have hpq : IsPath X.src X.tgt (p ++ X.att f) (endV c) (X.base f) :=
        isPath_append_iff.mpr ⟨b₁, hp, hc₁ ▸ hattpath⟩
      have hextpa : extendList (p ++ X.att f) c = c₁ := by
        rw [extendList_append, ← hc₁def, extendList_att hbase]
      refine Htpy.of_step ⟨hpath, hpath', .inr ⟨uLiftPath p c, uLiftPath q c₁,
        ⟨(c₁, f), hbase⟩, ?_, uLiftPath_append p q c b₁ hp⟩⟩
      rw [uLiftPath_append (p ++ X.att f) q c (X.base f) hpq, hextpa,
        uLiftPath_append p (X.att f) c b₁ hp, ← hc₁def]; rfl

theorem htpy_uLiftPath {c : UV X x₀} {q q' : List (X.E × Bool)} {w : X.V}
    (hq : IsPath X.src X.tgt q (endV c) w) (h : Htpy X (endV c) w q q') :
    Htpy (uCover X x₀) c (extendList q c) (uLiftPath q c) (uLiftPath q' c) := by
  induction h with
  | refl => exact .refl _
  | @tail m m' hstep hlast ih =>
      have hextm : extendList m c = extendList q c := (extendList_htpy hq hstep).symm
      refine ih.trans ?_
      rcases hlast with hs | hs
      · exact hextm ▸ htpy_step_uLiftPath hs
      · have hextm' : extendList m' c = extendList q c :=
          (extendList_htpy hs.1 (.of_step hs)).trans hextm
        exact (hextm' ▸ htpy_step_uLiftPath hs).symm

theorem eq_uLiftPath_of_isPath : ∀ (L : List ((uCover X x₀).E × Bool)) (c d : UV X x₀),
    IsPath (uCover X x₀).src (uCover X x₀).tgt L c d →
      L = uLiftPath (mapPath (univProj X x₀) L) c
  | [], _, _, _ => rfl
  | (E, b) :: T, c, d, ⟨hc, hrest⟩ => by
      cases b with
      | true =>
          have h : endV c = germSrc X.src X.tgt (E.1.2, true) := hc.symm ▸ E.2
          have hlift : liftGerm c (E.1.2, true) h = (E, true) :=
            Prod.ext (Subtype.ext (Prod.ext hc rfl)) rfl
          have hnext : extend (E.1.2, true) c =
              germTgt (uCover X x₀).src (uCover X x₀).tgt (E, true) := congrArg _ hc
          show (E, true) :: T = uLiftPath ((E.1.2, true) :: mapPath (univProj X x₀) T) c
          rw [uLiftPath_cons h, hlift, hnext]
          exact congrArg _ (eq_uLiftPath_of_isPath T _ d hrest)
      | false =>
          have hEc : extend (E.1.2, false) c = E.1.1 :=
            hc.symm ▸ extend_revGerm (eb := (E.1.2, true)) E.2
          have h : endV c = germSrc X.src X.tgt (E.1.2, false) :=
            hc.symm ▸ endV_extend (c := E.1.1) (eb := (E.1.2, true)) E.2
          have hlift : liftGerm c (E.1.2, false) h = (E, false) :=
            Prod.ext (Subtype.ext (Prod.ext hEc rfl)) rfl
          show (E, false) :: T = uLiftPath ((E.1.2, false) :: mapPath (univProj X x₀) T) c
          rw [uLiftPath_cons h, hlift, hEc]
          exact congrArg _ (eq_uLiftPath_of_isPath T _ d hrest)

theorem simplyConnected_univCover : SimplyConnected (uCover X x₀) := by
  intro c L hL
  set q := mapPath (univProj X x₀) L
  have hLq : L = uLiftPath q c := eq_uLiftPath_of_isPath L c c hL
  have hq : IsPath X.src X.tgt q (endV c) (endV c) := isPath_mapPath (univProj X x₀) hL
  have hext : extendList q c = c :=
    (endpt_eq_of_isPath (isPath_uLiftPath q c (endV c) hq)).symm.trans
      (hLq ▸ endpt_eq_of_isPath hL)
  have hnull : Htpy X (endV c) (endV c) q [] := by
    induction c using UV.ind with | h p =>
    have hpq := isPath_append_iff.mpr ⟨endpt X x₀ p.1, p.2, hq⟩
    have hendpq : endpt X x₀ (p.1 ++ q) = endpt X x₀ p.1 := endpt_eq_of_isPath hpq
    have hclass : UV.mk (⟨p.1 ++ q, hendpq ▸ hpq⟩ : PathFrom X x₀) = UV.mk p :=
      (extendList_mk (p := p) (r := ⟨p.1 ++ q, hendpq ▸ hpq⟩) hq rfl).symm.trans hext
    have h1 : Htpy X x₀ (endpt X x₀ p.1) (p.1 ++ q) p.1 := by
      have h' : Htpy X x₀ (endpt X x₀ (p.1 ++ q)) (p.1 ++ q) p.1 := Quotient.exact hclass
      rwa [hendpq] at h'
    set v := endpt X x₀ p.1
    have hrp : IsPath X.src X.tgt (revPath p.1) v x₀ := isPath_revPath p.2
    have hA := Htpy.append_congr hrp hpq (.refl _) h1
    have hB := htpy_revPath_append p.2
    have hC := Htpy.append_congr (isPath_append_iff.mpr ⟨x₀, hrp, p.2⟩) hq hB (.refl _)
    have hqA : Htpy X v v q (revPath p.1 ++ (p.1 ++ q)) := by simpa using hC.symm
    exact (hqA.trans hA).trans hB
  have := htpy_uLiftPath (c := c) (q := q) (q' := []) hq hnull
  rw [hext, ← hLq] at this
  simpa using this

def deckP (g : Loop X x₀) (p : PathFrom X x₀) : PathFrom X x₀ :=
  ⟨g.1 ++ p.1, by
    rw [endpt_append, endpt_eq_of_isPath g.2]
    exact isPath_append_iff.mpr ⟨x₀, g.2, p.2⟩⟩

theorem endpt_deckP (g : Loop X x₀) (p : PathFrom X x₀) :
    endpt X x₀ (deckP g p).1 = endpt X x₀ p.1 := by
  show endpt X x₀ (g.1 ++ p.1) = endpt X x₀ p.1
  rw [endpt_append, endpt_eq_of_isPath g.2]

def deckV (γ : Pi1 X x₀) (c : UV X x₀) : UV X x₀ :=
  Quotient.map₂ deckP (fun g g' hg p p' hp => by
    show Htpy X x₀ (endpt X x₀ (deckP g p).1) (deckP g p).1 (deckP g' p').1
    rw [endpt_deckP]
    exact Htpy.append_congr g.2 p.2 hg hp) γ c

@[simp] theorem deckV_mk (g : Loop X x₀) (p : PathFrom X x₀) :
    deckV (Quotient.mk _ g) (UV.mk p) = UV.mk (deckP g p) := rfl

@[simp] theorem endV_deckV (γ : Pi1 X x₀) (c : UV X x₀) : endV (deckV γ c) = endV c := by
  induction γ using Quotient.ind with | _ g =>
  induction c using UV.ind with | h p => exact endpt_deckP g p

theorem deckV_one (c : UV X x₀) : deckV (1 : Pi1 X x₀) c = c := by
  induction c using UV.ind with | h p =>
  exact Quotient.sound (Htpy.refl p.1)

theorem deckV_mul (γ δ : Pi1 X x₀) (c : UV X x₀) :
    deckV (γ * δ) c = deckV γ (deckV δ c) := by
  induction γ using Quotient.ind with | _ g =>
  induction δ using Quotient.ind with | _ g' =>
  induction c using UV.ind with | h p =>
  refine Quotient.sound ?_
  show Htpy X x₀ (endpt X x₀ ((g.1 ++ g'.1) ++ p.1)) ((g.1 ++ g'.1) ++ p.1) (g.1 ++ (g'.1 ++ p.1))
  simpa using Htpy.refl ((g.1 ++ g'.1) ++ p.1)

theorem extend_deckV (γ : Pi1 X x₀) (eb : X.E × Bool) (c : UV X x₀) :
    extend eb (deckV γ c) = deckV γ (extend eb c) := by
  induction γ using Quotient.ind with | _ g =>
  induction c using UV.ind with | h p =>
  have hl : (extendP eb (deckP g p)).1 = (deckP g (extendP eb p)).1 := by
    by_cases h : endpt X x₀ p.1 = germSrc X.src X.tgt eb
    · rw [extendP_pos (by rwa [endpt_deckP])]; show (g.1 ++ p.1) ++ [eb] = g.1 ++ (extendP eb p).1
      simp [extendP_pos h]
    · rw [extendP_neg (by rwa [endpt_deckP])]; show g.1 ++ p.1 = g.1 ++ (extendP eb p).1
      simp [extendP_neg h]
  refine Quotient.sound ?_
  show Htpy X x₀ (endpt X x₀ (extendP eb (deckP g p)).1) (extendP eb (deckP g p)).1
    (deckP g (extendP eb p)).1
  exact hl ▸ .refl _

def deckE (γ : Pi1 X x₀) (E : UE X x₀) : UE X x₀ :=
  ⟨(deckV γ E.1.1, E.1.2), by rw [endV_deckV]; exact E.2⟩

def deckF (γ : Pi1 X x₀) (F : UF X x₀) : UF X x₀ :=
  ⟨(deckV γ F.1.1, F.1.2), by rw [endV_deckV]; exact F.2⟩

theorem liftGerm_deckV {c : UV X x₀} {eb : X.E × Bool} (γ : Pi1 X x₀)
    (h : endV c = germSrc X.src X.tgt eb) (h' : endV (deckV γ c) = germSrc X.src X.tgt eb) :
    liftGerm (deckV γ c) eb h' = (deckE γ (liftGerm c eb h).1, (liftGerm c eb h).2) := by
  rcases eb with ⟨e, _ | _⟩
  · exact Prod.ext (Subtype.ext (Prod.ext (extend_deckV γ (e, false) c) rfl)) rfl
  · rfl

theorem uLiftPath_deckV (γ : Pi1 X x₀) : ∀ (q : List (X.E × Bool)) (c : UV X x₀) (w : X.V),
    IsPath X.src X.tgt q (endV c) w →
      uLiftPath q (deckV γ c) = (uLiftPath q c).map (fun Eb => (deckE γ Eb.1, Eb.2))
  | [], _, _, _ => rfl
  | eb :: t, c, w, hq => by
      have h' : endV (deckV γ c) = germSrc X.src X.tgt eb := (endV_deckV γ c).trans hq.1
      rw [uLiftPath_cons h', uLiftPath_cons hq.1, List.map_cons, liftGerm_deckV γ hq.1 h',
        extend_deckV γ eb c, uLiftPath_deckV γ t (extend eb c) w (endV_extend hq.1 ▸ hq.2)]

variable (X x₀) in
noncomputable def univDeck : DeckAction (uCover X x₀) (Pi1 X x₀) where
  smulV := deckV
  smulE := deckE
  smulF := deckF
  one_smulV := deckV_one
  mul_smulV := deckV_mul
  one_smulE := fun E => Subtype.ext (Prod.ext (deckV_one E.1.1) rfl)
  mul_smulE := fun γ δ E => Subtype.ext (Prod.ext (deckV_mul γ δ E.1.1) rfl)
  one_smulF := fun F => Subtype.ext (Prod.ext (deckV_one F.1.1) rfl)
  mul_smulF := fun γ δ F => Subtype.ext (Prod.ext (deckV_mul γ δ F.1.1) rfl)
  src_smul := fun _ _ => rfl
  tgt_smul := fun γ E => extend_deckV γ (E.1.2, true) E.1.1
  base_smul := fun _ _ => rfl
  att_smul := fun γ F => uLiftPath_deckV γ (X.att F.1.2) F.1.1 (X.base F.1.2)
    (F.2 ▸ X.att_isLoop F.1.2)

theorem isRegular_univProj : IsRegular (univProj X x₀) (univDeck X x₀) := by
  refine ⟨endV_deckV, fun c d hcd => ?_⟩
  induction c using UV.ind with | h p =>
  induction d using UV.ind with | h r =>
  have hv : endpt X x₀ p.1 = endpt X x₀ r.1 := hcd
  have hvp : IsPath X.src X.tgt p.1 x₀ (endpt X x₀ r.1) := hv ▸ p.2
  have hrev := isPath_revPath hvp
  have hrp := isPath_append_iff.mpr ⟨endpt X x₀ r.1, r.2, hrev⟩
  refine ⟨Quotient.mk _ ⟨r.1 ++ revPath p.1, hrp⟩, Quotient.sound ?_, ?_⟩
  · show Htpy X x₀ (endpt X x₀ ((r.1 ++ revPath p.1) ++ p.1)) ((r.1 ++ revPath p.1) ++ p.1) r.1
    have hend : endpt X x₀ ((r.1 ++ revPath p.1) ++ p.1) = endpt X x₀ r.1 := by
      rw [endpt_append, endpt_eq_of_isPath hrp]; exact hv
    rw [hend, List.append_assoc]
    simpa using Htpy.append_congr r.2 (isPath_append_iff.mpr ⟨x₀, hrev, hvp⟩)
      (.refl _) (htpy_revPath_append hvp)
  · rintro γ hγ
    induction γ using Quotient.ind with | _ g =>
    refine Quotient.sound ?_
    show Htpy X x₀ x₀ g.1 (r.1 ++ revPath p.1)
    have hgp := isPath_append_iff.mpr ⟨x₀, g.2, hvp⟩
    have hg : Htpy X x₀ (endpt X x₀ r.1) (g.1 ++ p.1) r.1 :=
      endpt_eq_of_isPath hgp ▸ (Quotient.exact hγ : Htpy X x₀ (endpt X x₀ (g.1 ++ p.1)) _ _)
    have h1 := Htpy.append_congr hgp hrev hg (.refl _)
    rw [List.append_assoc] at h1
    have h2 := Htpy.append_congr g.2 (isPath_append_iff.mpr ⟨endpt X x₀ r.1, hvp, hrev⟩)
      (.refl _) (htpy_append_revPath hvp)
    exact (by simpa using h2.symm : Htpy X x₀ x₀ g.1 _).trans h1
