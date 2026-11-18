module

public import RequestProject.CombPi1
public import Mathlib

@[expose] public section
noncomputable section
section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains
namespace Comb

universe u

variable {X : Complex2.{u}}

/-! ### The endpoint of an edge path -/

/-- The endpoint of a list of oriented edges read from `a`. -/
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
  | cons eb t ih => exact ih h.2

theorem endpt_append (a : X.V) (p q : List (X.E × Bool)) :
    endpt X a (p ++ q) = endpt X (endpt X a p) q := by
  induction p generalizing a with
  | nil => rfl
  | cons eb t ih => simpa using ih (germTgt X.src X.tgt eb)

/-! ### The vertices of the universal cover -/

variable (X) in
/-- An edge path issued from `x₀`. -/
def PathFrom (x₀ : X.V) : Type u :=
  {p : List (X.E × Bool) // IsPath X.src X.tgt p x₀ (endpt X x₀ p)}

variable {x₀ : X.V}

/-- Two paths from `x₀` are equivalent when they are homotopic with fixed endpoints. -/
instance pathFromSetoid (X : Complex2.{u}) (x₀ : X.V) : Setoid (PathFrom X x₀) where
  r p q := Htpy X x₀ (endpt X x₀ p.1) p.1 q.1
  iseqv := by
    refine ⟨fun p => Htpy.refl _, ?_, ?_⟩
    · intro p q h
      have hq : IsPath X.src X.tgt q.1 x₀ (endpt X x₀ p.1) := h.isPath p.2
      have he : endpt X x₀ q.1 = endpt X x₀ p.1 := endpt_eq_of_isPath hq
      rw [he]
      exact h.symm
    · intro p q r h h'
      have hq : IsPath X.src X.tgt q.1 x₀ (endpt X x₀ p.1) := h.isPath p.2
      have he : endpt X x₀ q.1 = endpt X x₀ p.1 := endpt_eq_of_isPath hq
      rw [he] at h'
      exact h.trans h'

variable (X) in
/-- The vertices of the universal cover: homotopy classes of edge paths from `x₀`. -/
def UV (x₀ : X.V) : Type u := Quotient (pathFromSetoid X x₀)

/-- The class of a path from `x₀`. -/
def UV.mk (p : PathFrom X x₀) : UV X x₀ := Quotient.mk _ p

/-- Induction on classes of paths. -/
@[elab_as_elim] theorem UV.ind {motive : UV X x₀ → Prop} (h : ∀ p, motive (UV.mk p)) :
    ∀ c, motive c := Quotient.ind h

theorem UV.sound {p q : PathFrom X x₀} (h : Htpy X x₀ (endpt X x₀ p.1) p.1 q.1) :
    UV.mk p = UV.mk q := Quotient.sound h

/-- The base vertex of the universal cover: the class of the empty path. -/
def UV.base (X : Complex2.{u}) (x₀ : X.V) : UV X x₀ := UV.mk ⟨[], rfl⟩

/-- The endpoint of (any representative of) a class. -/
def endV (c : UV X x₀) : X.V :=
  Quotient.liftOn c (fun p => endpt X x₀ p.1) (by
    intro p q h
    have hq : IsPath X.src X.tgt q.1 x₀ (endpt X x₀ p.1) := h.isPath p.2
    exact (endpt_eq_of_isPath hq).symm)

@[simp] theorem endV_mk (p : PathFrom X x₀) : endV (UV.mk p) = endpt X x₀ p.1 := rfl

@[simp] theorem endV_base : endV (UV.base X x₀) = x₀ := rfl

/-! ### Extending a class by an edge -/

theorem endpt_append_single (a : X.V) (p : List (X.E × Bool)) (eb : X.E × Bool)
    (h : endpt X a p = germSrc X.src X.tgt eb) :
    endpt X a (p ++ [eb]) = germTgt X.src X.tgt eb := by
  rw [endpt_append, h]
  rfl

theorem isPath_append_single {p : List (X.E × Bool)} {a : X.V}
    (hp : IsPath X.src X.tgt p a (endpt X a p)) (eb : X.E × Bool)
    (h : endpt X a p = germSrc X.src X.tgt eb) :
    IsPath X.src X.tgt (p ++ [eb]) a (endpt X a (p ++ [eb])) := by simp_all [endpt_append_single, isPath_append_iff.mpr, endpt]

open Classical in
/-- Appending an oriented edge to a path from `x₀` (the path is left unchanged if the edge
does not start at its endpoint). -/
def extendP (eb : X.E × Bool) (p : PathFrom X x₀) : PathFrom X x₀ :=
  if h : endpt X x₀ p.1 = germSrc X.src X.tgt eb then ⟨p.1 ++ [eb], isPath_append_single p.2 eb h⟩
  else p

theorem extendP_pos {p : PathFrom X x₀} {eb : X.E × Bool}
    (h : endpt X x₀ p.1 = germSrc X.src X.tgt eb) : (extendP eb p).1 = p.1 ++ [eb] := by
  simp only [extendP, dif_pos h]

theorem extendP_neg {p : PathFrom X x₀} {eb : X.E × Bool}
    (h : ¬ endpt X x₀ p.1 = germSrc X.src X.tgt eb) : (extendP eb p).1 = p.1 := by
  simp only [extendP, dif_neg h]

/-- Appending an oriented edge to a class of paths. -/
def extend (eb : X.E × Bool) (c : UV X x₀) : UV X x₀ :=
  Quotient.map (extendP eb) (by
    intro p q hpq
    have hq : IsPath X.src X.tgt q.1 x₀ (endpt X x₀ p.1) := hpq.isPath p.2
    have he : endpt X x₀ q.1 = endpt X x₀ p.1 := endpt_eq_of_isPath hq
    by_cases h : endpt X x₀ p.1 = germSrc X.src X.tgt eb
    · show Htpy X x₀ (endpt X x₀ (extendP eb p).1) (extendP eb p).1 (extendP eb q).1
      rw [extendP_pos h, extendP_pos (he.trans h), endpt_append_single x₀ p.1 eb h]
      exact Htpy.append_congr (h ▸ p.2) (h ▸ isPath_single eb) hpq (Htpy.refl _)
    · show Htpy X x₀ (endpt X x₀ (extendP eb p).1) (extendP eb p).1 (extendP eb q).1
      rw [extendP_neg h, extendP_neg (fun hc => h (he ▸ hc))]
      exact hpq) c

theorem extend_mk (p : PathFrom X x₀) (eb : X.E × Bool) :
    extend eb (UV.mk p) = UV.mk (extendP eb p) := rfl

theorem endV_extend {c : UV X x₀} {eb : X.E × Bool} (h : endV c = germSrc X.src X.tgt eb) :
    endV (extend eb c) = germTgt X.src X.tgt eb := by
  induction c using UV.ind with
  | h p =>
      have h'  := h
      rw [extend_mk, endV_mk, extendP_pos h', endpt_append_single x₀ p.1 eb h']

/-- Extending by an edge and then by its reverse returns the original class. -/
theorem extend_revGerm {c : UV X x₀} {eb : X.E × Bool} (h : endV c = germSrc X.src X.tgt eb) :
    extend (revGerm eb) (extend eb c) = c := by
  induction c using UV.ind with
  | h p =>
      have h' : endpt X x₀ p.1 = germSrc X.src X.tgt eb := h
      have h1 : endpt X x₀ (extendP eb p).1 = germSrc X.src X.tgt (revGerm eb) := by
        rw [extendP_pos h', endpt_append_single x₀ p.1 eb h']
        simp
      rw [extend_mk, extend_mk]
      refine Quotient.sound ?_
      show Htpy X x₀ (endpt X x₀ (extendP (revGerm eb) (extendP eb p)).1)
        (extendP (revGerm eb) (extendP eb p)).1 p.1
      rw [extendP_pos h1, extendP_pos h']
      have hp  := h' ▸ p.2
      have hbk : Htpy X (germSrc X.src X.tgt eb) (germSrc X.src X.tgt eb) [eb, revGerm eb] [] := by
        refine Htpy.of_step ⟨?_, rfl, Or.inl ⟨[], [], eb, rfl, rfl⟩⟩
        exact ⟨rfl, by simp, by simp⟩
      have hcongr :=
        Htpy.append_congr hp (by refine ⟨rfl, ?_, ?_⟩ <;> simp) (Htpy.refl _) hbk
      have hrw : p.1 ++ [eb] ++ [revGerm eb] = p.1 ++ [eb, revGerm eb] := by simp
      have hend : endpt X x₀ (p.1 ++ [eb] ++ [revGerm eb]) = germSrc X.src X.tgt eb := by
        rw [endpt_append, endpt_append, h']
        simp
      rw [hend, hrw]
      simpa using hcongr

/-- Extending a class by a whole path. -/
def extendList (q : List (X.E × Bool)) (c : UV X x₀) : UV X x₀ :=
  q.foldl (fun d eb => extend eb d) c

@[simp] theorem extendList_nil (c : UV X x₀) : extendList [] c = c := rfl

@[simp] theorem extendList_cons (eb : X.E × Bool) (q : List (X.E × Bool)) (c : UV X x₀) :
    extendList (eb :: q) c = extendList q (extend eb c) := rfl

theorem extendList_append (q r : List (X.E × Bool)) (c : UV X x₀) :
    extendList (q ++ r) c = extendList r (extendList q c) := by simp_all [UV, extendList]

/-- Extending the class of `p` by a path `q` issued from its endpoint gives the class of the
concatenation. -/
theorem extendList_mk : ∀ {q : List (X.E × Bool)} {p r : PathFrom X x₀} {w : X.V},
    IsPath X.src X.tgt q (endpt X x₀ p.1) w → r.1 = p.1 ++ q →
      extendList q (UV.mk p) = UV.mk r := by
  intro q
  induction q with
  | nil =>
      intro p r w _ hr
      refine Quotient.sound ?_
      show Htpy X x₀ (endpt X x₀ p.1) p.1 r.1
      rw [hr]
      simpa using Htpy.refl p.1
  | cons eb t ih =>
      intro p r w hq hr
      have h'  := hq.1
      have hend : endpt X x₀ (extendP eb p).1 = germTgt X.src X.tgt eb := by
        rw [extendP_pos h', endpt_append_single x₀ p.1 eb h']
      rw [extendList_cons, extend_mk]
      refine ih (w := w) ?_ ?_
      · simp_all
      · rw [extendP_pos h', hr]; simp

theorem endV_extendList : ∀ {q : List (X.E × Bool)} {c : UV X x₀} {w : X.V},
    IsPath X.src X.tgt q (endV c) w → endV (extendList q c) = w := by
  intro q
  induction q with
  | nil => intro c w hq; exact hq
  | cons eb t ih =>
      intro c w hq
      have h  := hq.1
      refine ih ?_
      rw [endV_extend h]
      exact hq.2

/-! ### The universal cover as a complex -/

variable (X x₀) in
/-- The edges of the universal cover: a vertex together with an edge of `X` issued from its
endpoint. -/
def UE : Type u := {ce : UV X x₀ × X.E // endV ce.1 = X.src ce.2}

variable (X x₀) in
/-- The two-cells of the universal cover: a vertex together with a two-cell of `X` based at
its endpoint. -/
def UF : Type u := {cf : UV X x₀ × X.F // endV cf.1 = X.base cf.2}

/-- The initial vertex of an edge of the universal cover. -/
def uSrc (ce : UE X x₀) : UV X x₀ := ce.1.1

/-- The terminal vertex of an edge of the universal cover. -/
def uTgt (ce : UE X x₀) : UV X x₀ := extend (ce.1.2, true) ce.1.1

/-- The basepoint of a two-cell of the universal cover. -/
def uBase (cf : UF X x₀) : UV X x₀ := cf.1.1

/-- The lift of an oriented edge at a vertex of the cover. -/
def liftGerm (c : UV X x₀) :
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
/-- The lift of an edge path at a vertex of the cover. -/
def uLiftPath : List (X.E × Bool) → UV X x₀ → List (UE X x₀ × Bool)
  | [], _ => []
  | eb :: t, c =>
      if h : endV c = germSrc X.src X.tgt eb then
        liftGerm c eb h :: uLiftPath t (extend eb c)
      else []

@[simp] theorem uLiftPath_nil (c : UV X x₀) : uLiftPath [] c = [] := rfl

theorem uLiftPath_cons {eb : X.E × Bool} {t : List (X.E × Bool)} {c : UV X x₀}
    (h : endV c = germSrc X.src X.tgt eb) :
    uLiftPath (eb :: t) c = liftGerm c eb h :: uLiftPath t (extend eb c) := by
  rw [uLiftPath, dif_pos h]

/-- The attaching path of a two-cell of the universal cover. -/
def uAtt (cf : UF X x₀) : List (UE X x₀ × Bool) :=
  uLiftPath (X.att cf.1.2) cf.1.1



/-- The lift of a path is a path of the cover, from the given vertex to the extended one. -/
theorem isPath_uLiftPath : ∀ (q : List (X.E × Bool)) (c : UV X x₀) (w : X.V),
    IsPath X.src X.tgt q (endV c) w → IsPath uSrc uTgt (uLiftPath q c) c (extendList q c) := by
  intro q
  induction q with
  | nil => intro c w _; rfl
  | cons eb t ih =>
      intro c w hq
      have h  := hq.1
      rw [uLiftPath_cons h, extendList_cons]
      refine ⟨(show germSrc uSrc uTgt (liftGerm c eb h) = c by
        obtain ⟨e, b⟩ := eb
        cases b with
        | true => rfl
        | false =>
            exact extend_revGerm h).symm, ?_⟩
      rw [(show germTgt uSrc uTgt (liftGerm c eb h) = extend eb c by
        obtain ⟨e, b⟩ := eb
        cases b with
        | true => rfl
        | false => rfl)]
      refine ih (extend eb c) w ?_
      rw [endV_extend h]
      exact hq.2

/-- Extending a class along the attaching loop of a two-cell based at its endpoint returns
the same class: this is exactly the two-cell cancellation. -/
theorem extendList_att {c : UV X x₀} {f : X.F} (h : endV c = X.base f) :
    extendList (X.att f) c = c := by
  induction c using UV.ind with
  | h p =>
      have h'  := h
      have hatt : IsPath X.src X.tgt (X.att f) (endpt X x₀ p.1) (X.base f) := h' ▸ X.att_isLoop f
      have hp  :=
        isPath_append_iff.mpr ⟨endpt X x₀ p.1, p.2, hatt⟩
      have hend  := endpt_eq_of_isPath hp
      refine (extendList_mk (r := ⟨p.1 ++ X.att f, by rw [hend]; exact hp⟩) hatt
        rfl).trans ?_
      refine Quotient.sound ?_
      show Htpy X x₀ (endpt X x₀ (p.1 ++ X.att f)) (p.1 ++ X.att f) p.1
      rw [hend]
      refine Htpy.of_step ⟨hp, h' ▸ p.2, Or.inr ⟨p.1, [], f, ?_, ?_⟩⟩ <;> simp

theorem uAtt_isLoop (cf : UF X x₀) : IsPath uSrc uTgt (uAtt cf) (uBase cf) (uBase cf) := by
  have h  := cf.2
  have hatt : IsPath X.src X.tgt (X.att cf.1.2) (endV cf.1.1) (X.base cf.1.2) :=
    h ▸ X.att_isLoop cf.1.2
  have := isPath_uLiftPath (X.att cf.1.2) cf.1.1 (X.base cf.1.2) hatt
  rwa [extendList_att h] at this

/-- The lift of a path projects back to the path. -/
theorem map_uLiftPath : ∀ (q : List (X.E × Bool)) (c : UV X x₀) (w : X.V),
    IsPath X.src X.tgt q (endV c) w →
      (uLiftPath q c).map (fun eb => ((eb.1 : UE X x₀).1.2, eb.2)) = q := by
  intro q
  induction q with
  | nil => intro c w _; rfl
  | cons eb t ih =>
      intro c w hq
      have h  := hq.1
      rw [uLiftPath_cons h, List.map_cons, ih (extend eb c) w (by rw [endV_extend h]; exact hq.2)]
      obtain ⟨e, b⟩ := eb
      cases b <;> rfl

variable (X x₀) in
/-- **The universal cover** of a combinatorial two-complex. -/
def uCover : Complex2.{u} where
  V := UV X x₀
  E := UE X x₀
  F := UF X x₀
  src := uSrc
  tgt := uTgt
  base := uBase
  att := uAtt
  att_isLoop := uAtt_isLoop

variable (X x₀) in
/-- The projection of the universal cover to the complex. -/
def univProj : Hom (uCover X x₀) X where
  onV := endV
  onE := fun ce => ce.1.2
  onF := fun cf => cf.1.2
  src_onE := fun ce => ce.2.symm
  tgt_onE := by
    intro ce
    show X.tgt ce.1.2 = endV (extend (ce.1.2, true) ce.1.1)
    have h : endV ce.1.1 = germSrc X.src X.tgt (ce.1.2, true) := ce.2
    rw [endV_extend h]
    rfl
  base_onF := fun cf => cf.2.symm
  att_onF := by
    intro cf
    have h : endV cf.1.1 = X.base cf.1.2 := cf.2
    have hatt : IsPath X.src X.tgt (X.att cf.1.2) (endV cf.1.1) (X.base cf.1.2) :=
      h ▸ X.att_isLoop cf.1.2
    exact (map_uLiftPath (X.att cf.1.2) cf.1.1 (X.base cf.1.2) hatt).symm

/-! ### The projection is a covering -/

theorem endV_surjective (hX : IsConnected X) : Function.Surjective (endV (X := X) (x₀ := x₀)) := by
  intro v
  obtain ⟨p, hp⟩ := hX x₀ v
  have he  := endpt_eq_of_isPath hp
  exact ⟨UV.mk ⟨p, by rw [he]; exact hp⟩, he⟩

theorem isCovering_univProj (hX : IsConnected X) : IsCovering (univProj X x₀) := by
  refine ⟨endV_surjective hX, ?_, ?_⟩
  · intro c
    constructor
    · rintro ⟨⟨E, b⟩, hE⟩ ⟨⟨E', b'⟩, hE'⟩ heq
      have hpair  := congrArg Subtype.val heq
      have hb  := congrArg Prod.snd hpair
      have he : E.1.2 = E'.1.2 := congrArg Prod.fst hpair
      subst hb
      have hEE : E = E' := by
        cases b with
        | true =>
            have h1  := hE
            have h2  := hE'
            exact Subtype.ext (Prod.ext (h1.trans h2.symm) he)
        | false =>
            have h1  := hE
            have h2  := hE'
            have k1 : E.1.1 = extend (E.1.2, false) c := by
              rw [← h1]
              exact (extend_revGerm (eb := (E.1.2, true)) E.2).symm
            have k2 : E'.1.1 = extend (E'.1.2, false) c := by
              rw [← h2]
              exact (extend_revGerm (eb := (E'.1.2, true)) E'.2).symm
            refine Subtype.ext (Prod.ext ?_ he)
            rw [k1, k2, he]
      subst hEE
      rfl
    · rintro ⟨⟨e, b⟩, hb⟩
      cases b with
      | true =>
          have hsrc  := hb.symm
          refine ⟨⟨(⟨(c, e), hsrc⟩, true), rfl⟩, ?_⟩
          exact Subtype.ext rfl
      | false =>
          have h  := hb.symm
          have hend  := endV_extend h
          refine ⟨⟨(⟨(extend (e, false) c, e), hend⟩, false), ?_⟩, ?_⟩
          · show extend (e, true) (extend (e, false) c) = c
            exact extend_revGerm h
          · rfl
  · constructor
    · rintro ⟨⟨c, f⟩, h⟩ ⟨⟨c', f'⟩, h'⟩ heq
      have hpair  := congrArg Subtype.val heq
      exact Subtype.ext (Prod.ext (congrArg Prod.snd hpair) (congrArg Prod.fst hpair))
    · rintro ⟨⟨f, c⟩, h⟩
      exact ⟨⟨(c, f), h.symm⟩, rfl⟩

theorem isConnected_univCover : IsConnected (uCover X x₀) := by
  -- every vertex is joined to the base vertex
  have key : ∀ c : UV X x₀, ∃ l : List ((uCover X x₀).E × Bool),
      IsPath (uCover X x₀).src (uCover X x₀).tgt l (UV.base X x₀) c := by
    intro c
    induction c using UV.ind with
    | h p =>
        have hp  := p.2
        refine ⟨uLiftPath p.1 (UV.base X x₀), ?_⟩
        have hlift := isPath_uLiftPath p.1 (UV.base X x₀) (endpt X x₀ p.1) hp
        have hext : extendList p.1 (UV.base X x₀) = UV.mk p :=
          extendList_mk
            hp (by simp)
        rwa [hext] at hlift
  intro c d
  obtain ⟨l, hl⟩ := key c
  obtain ⟨m, hm⟩ := key d
  refine ⟨revPath l ++ m, ?_⟩
  exact isPath_append_iff.mpr
    ⟨UV.base X x₀, isPath_revPath hl, hm⟩

/-! ### The cover is simply connected -/

/-- Lifting is additive along concatenation. -/
theorem uLiftPath_append : ∀ (l : List (X.E × Bool)) (m : List (X.E × Bool)) (c : UV X x₀)
    (w : X.V), IsPath X.src X.tgt l (endV c) w →
      uLiftPath (l ++ m) c = uLiftPath l c ++ uLiftPath m (extendList l c) := by
  intro l
  induction l with
  | nil => intro m c w _; rfl
  | cons eb t ih =>
      intro m c w hl
      have h  := hl.1
      rw [List.cons_append, uLiftPath_cons h, uLiftPath_cons h, extendList_cons,
        ih m (extend eb c) w (by rw [endV_extend h]; exact hl.2)]
      rfl

/-- Homotopic paths extend a class in the same way. -/
theorem extendList_htpy {c : UV X x₀} {l l' : List (X.E × Bool)} {w : X.V}
    (hl : IsPath X.src X.tgt l (endV c) w) (h : Htpy X (endV c) w l l') :
    extendList l c = extendList l' c := by
  induction c using UV.ind with
  | h p =>
      have hl'  := h.isPath hl
      have hpl  :=
        isPath_append_iff.mpr ⟨endpt X x₀ p.1, p.2, hl⟩
      have hpl'  :=
        isPath_append_iff.mpr ⟨endpt X x₀ p.1, p.2, hl'⟩
      have hend  := endpt_eq_of_isPath hpl
      have hend'  := endpt_eq_of_isPath hpl'
      rw [extendList_mk (r := ⟨p.1 ++ l, by rw [hend]; exact hpl⟩) hl rfl,
        extendList_mk (r := ⟨p.1 ++ l', by rw [hend']; exact hpl'⟩) hl' rfl]
      refine Quotient.sound ?_
      show Htpy X x₀ (endpt X x₀ (p.1 ++ l)) (p.1 ++ l) (p.1 ++ l')
      rw [hend]
      exact Htpy.append_congr p.2 hl (Htpy.refl _) h

/-- Lifting turns an elementary homotopy of the base into a homotopy of the cover. -/
theorem htpy_step_uLiftPath {c : UV X x₀} {l l' : List (X.E × Bool)} {w : X.V}
    (hstep : Step X (endV c) w l l') :
    Htpy (uCover X x₀) c (extendList l c) (uLiftPath l c) (uLiftPath l' c) := by
  obtain ⟨hl, hl', hc⟩ := hstep
  have hext  :=
    (extendList_htpy hl (Htpy.of_step ⟨hl, hl', hc⟩)).symm
  have hpath  := isPath_uLiftPath l c w hl
  have hpath' : IsPath (uCover X x₀).src (uCover X x₀).tgt (uLiftPath l' c) c
      (extendList l c) := by
    rw [← hext]; exact isPath_uLiftPath l' c w hl'
  rcases hc with ⟨p, q, eb, hleq, hl'eq⟩ | ⟨p, q, f, hleq, hl'eq⟩
  · subst hleq; subst hl'eq
    obtain ⟨b₁, hp, hrest⟩ := isPath_append_iff.mp hl
    have hc₁ : endV (extendList p c) = b₁ := endV_extendList hp
    set c₁ := extendList p c with hc₁def
    have h₁ : endV c₁ = germSrc X.src X.tgt eb := by rw [hc₁]; exact hrest.1
    have h₂ : endV (extend eb c₁) = germSrc X.src X.tgt (revGerm eb) := by
      rw [endV_extend h₁]; simp
    have hrev : liftGerm (extend eb c₁) (revGerm eb) h₂
        = revGerm (X := uCover X x₀) (liftGerm c₁ eb h₁) := by
      obtain ⟨e, bb⟩ := eb
      cases bb with
      | true =>
          refine Prod.ext ?_ rfl
          refine Subtype.ext (Prod.ext ?_ rfl)
          exact extend_revGerm h₁
      | false =>
          refine Prod.ext ?_ rfl
          exact Subtype.ext (Prod.ext rfl rfl)
    refine Htpy.of_step ⟨hpath, hpath', Or.inl ⟨uLiftPath p c, uLiftPath q c₁,
      liftGerm c₁ eb h₁, ?_, ?_⟩⟩
    · rw [uLiftPath_append p (eb :: revGerm eb :: q) c b₁ hp, ← hc₁def,
        uLiftPath_cons h₁, uLiftPath_cons h₂, hrev, extend_revGerm h₁]
    · rw [uLiftPath_append p q c b₁ hp, ← hc₁def]
  · subst hleq; subst hl'eq
    by_cases hnil : X.att f = []
    · -- a two-cell with empty attaching path cancels nothing
      rw [hnil]
      simp
      exact Htpy.refl _
    · obtain ⟨g, t, hgt⟩ : ∃ g t, X.att f = g :: t := by
        cases hc : X.att f with
        | nil => exact absurd hc hnil
        | cons g t => exact ⟨g, t, rfl⟩
      obtain ⟨b₂, hpa, hq⟩ := isPath_append_iff.mp hl
      obtain ⟨b₁, hp, hatt⟩ := isPath_append_iff.mp hpa
      have hc₁ : endV (extendList p c) = b₁ := endV_extendList hp
      set c₁ := extendList p c with hc₁def
      have hb₁ : b₁ = X.base f := by
        have h1 : b₁ = germSrc X.src X.tgt g := by
          have h := hatt; rw [hgt] at h; exact h.1
        have h2 : X.base f = germSrc X.src X.tgt g := by
          have h := X.att_isLoop f; rw [hgt] at h; exact h.1
        rw [h1, h2]
      have hbase : endV c₁ = X.base f := by rw [hc₁, hb₁]
      have hattpath : IsPath X.src X.tgt (X.att f) (endV c₁) (X.base f) := by
        rw [hbase]; exact X.att_isLoop f
      have hpq  :=
        isPath_append_iff.mpr ⟨b₁, hp, hc₁ ▸ hattpath⟩
      have hextpa : extendList (p ++ X.att f) c = c₁ := by
        rw [extendList_append, ← hc₁def, extendList_att hbase]
      refine Htpy.of_step ⟨hpath, hpath', Or.inr ⟨uLiftPath p c, uLiftPath q c₁,
        ⟨(c₁, f), hbase⟩, ?_, ?_⟩⟩
      · rw [uLiftPath_append (p ++ X.att f) q c (X.base f) hpq, hextpa,
          uLiftPath_append p (X.att f) c b₁ hp, ← hc₁def]
        rfl
      · rw [uLiftPath_append p q c b₁ hp, ← hc₁def]

/-- **Lifting is compatible with homotopy**: homotopic paths of the base have homotopic
lifts. -/
theorem htpy_uLiftPath {c : UV X x₀} {q q' : List (X.E × Bool)} {w : X.V}
    (hq : IsPath X.src X.tgt q (endV c) w) (h : Htpy X (endV c) w q q') :
    Htpy (uCover X x₀) c (extendList q c) (uLiftPath q c) (uLiftPath q' c) := by
  induction h with
  | refl => exact Htpy.refl _
  | @tail m m' hstep hlast ih =>
      have hm  := Htpy.isPath hstep hq
      have hextm  := (extendList_htpy hq hstep).symm
      refine (ih).trans ?_
      rcases hlast with hs | hs
      · have := htpy_step_uLiftPath hs
        rwa [hextm] at this
      · have hm'  := hs.1
        have hextm'  :=
          (extendList_htpy hm' (Htpy.of_step hs)).trans hextm
        have := htpy_step_uLiftPath hs
        rw [hextm'] at this
        exact this.symm

/-- **Unique path lifting**: a path of the cover is the lift of its projection. -/
theorem eq_uLiftPath_of_isPath : ∀ (L : List ((uCover X x₀).E × Bool)) (c d : UV X x₀),
    IsPath (uCover X x₀).src (uCover X x₀).tgt L c d →
      L = uLiftPath (mapPath (univProj X x₀) L) c := by
  intro L
  induction L with
  | nil => intro c d _; rfl
  | cons Eb T ih =>
      rintro c d ⟨hc, hrest⟩
      obtain ⟨E, b⟩ := Eb
      have hE  := E.2
      cases b with
      | true =>
          have hcE : c = E.1.1 := hc
          have h : endV c = germSrc X.src X.tgt (E.1.2, true) := by rw [hcE]; exact hE
          have hlift : liftGerm c (E.1.2, true) h = (E, true) := by
            refine Prod.ext ?_ rfl
            exact Subtype.ext (Prod.ext hcE rfl)
          have hnext : extend (E.1.2, true) c
              = germTgt (uCover X x₀).src (uCover X x₀).tgt (E, true) := by
            show extend (E.1.2, true) c = extend (E.1.2, true) E.1.1
            rw [hcE]
          show (E, true) :: T = uLiftPath ((E.1.2, true) :: mapPath (univProj X x₀) T) c
          rw [uLiftPath_cons h, hlift, hnext]
          congr 1
          exact ih _ d hrest
      | false =>
          have hcE : c = extend (E.1.2, true) E.1.1 := hc
          have hEc : extend (E.1.2, false) c = E.1.1 := by
            rw [hcE]
            exact extend_revGerm (eb := (E.1.2, true)) hE
          have h : endV c = germSrc X.src X.tgt (E.1.2, false) := by
            rw [hcE, endV_extend hE]
            rfl
          have hlift : liftGerm c (E.1.2, false) h = (E, false) := by
            refine Prod.ext ?_ rfl
            exact Subtype.ext (Prod.ext hEc rfl)
          have hnext : extend (E.1.2, false) c
              = germTgt (uCover X x₀).src (uCover X x₀).tgt (E, false) := hEc
          show (E, false) :: T = uLiftPath ((E.1.2, false) :: mapPath (univProj X x₀) T) c
          rw [uLiftPath_cons h, hlift, hnext]
          congr 1
          exact ih _ d hrest

/-- **The universal cover is simply connected.** -/
theorem simplyConnected_univCover : SimplyConnected (uCover X x₀) := by
  intro c L hL
  -- `L` is the lift of its projection
  set q := mapPath (univProj X x₀) L with hqdef
  have hLq  := eq_uLiftPath_of_isPath L c c hL
  have hq  := isPath_mapPath (univProj X x₀) hL
  -- the lift of `q` ends where `L` ends, that is at `c`
  have hext : extendList q c = c := by
    have h1  := endpt_eq_of_isPath hL
    have h2 : endpt (uCover X x₀) c L = extendList q c := by
      rw [hLq]
      exact endpt_eq_of_isPath (isPath_uLiftPath q c (endV c) hq)
    rw [← h2, h1]
  -- hence `q` is null-homotopic downstairs
  have hnull : Htpy X (endV c) (endV c) q [] := by
    induction c using UV.ind with
    | h p =>
        have hv : endV (UV.mk p) = endpt X x₀ p.1 := rfl
        have hpq  :=
          isPath_append_iff.mpr ⟨endpt X x₀ p.1, p.2, hq⟩
        have hendpq  := endpt_eq_of_isPath hpq
        have hclass : UV.mk ⟨p.1 ++ q, by rw [hendpq]; exact hpq⟩ = UV.mk p := by
          rw [← extendList_mk hq rfl]
          exact hext
        have h1 : Htpy X x₀ (endpt X x₀ p.1) (p.1 ++ q) p.1 := by
          have := Quotient.exact hclass
          have h' : Htpy X x₀ (endpt X x₀ (p.1 ++ q)) (p.1 ++ q) p.1 := this
          rwa [hendpq] at h'
        set v := endpt X x₀ p.1 with hvdef
        have hrp  := isPath_revPath p.2
        have hA  :=
          Htpy.append_congr hrp hpq (Htpy.refl _) h1
        have hB := htpy_revPath_append p.2
        have hC : Htpy X v v ((revPath p.1 ++ p.1) ++ q) ([] ++ q) :=
          Htpy.append_congr (isPath_append_iff.mpr ⟨x₀, hrp, p.2⟩) hq hB (Htpy.refl _)
        have hD : (revPath p.1 ++ p.1) ++ q = revPath p.1 ++ (p.1 ++ q) := by simp
        have hqA : Htpy X v v q (revPath p.1 ++ (p.1 ++ q)) := by
          have := hC.symm
          rw [hD] at this
          simpa using this
        exact (hqA.trans hA).trans hB
  -- and therefore so is `L` upstairs
  have := htpy_uLiftPath hq hnull
  rw [hext] at this
  rw [hLq]
  simpa using this

/-! ### The deck action -/

/-- Concatenating a loop at `x₀` in front of a path from `x₀`. -/
def deckP (g : Loop X x₀) (p : PathFrom X x₀) : PathFrom X x₀ :=
  ⟨g.1 ++ p.1, by
    have hend : endpt X x₀ (g.1 ++ p.1) = endpt X x₀ p.1 := by
      rw [endpt_append, endpt_eq_of_isPath g.2]
    rw [hend]
    exact isPath_append_iff.mpr ⟨x₀, g.2, p.2⟩⟩

theorem endpt_deckP (g : Loop X x₀) (p : PathFrom X x₀) :
    endpt X x₀ (deckP g p).1 = endpt X x₀ p.1 := by grind [endpt_append, endpt_eq_of_isPath, PathFrom, endpt, deckP]

/-- The action of the fundamental group on the vertices of the universal cover. -/
def deckV (γ : Pi1 X x₀) (c : UV X x₀) : UV X x₀ :=
  Quotient.map₂ deckP (by
    intro g g' hg p p' hp
    show Htpy X x₀ (endpt X x₀ (deckP g p).1) (deckP g p).1 (deckP g' p').1
    rw [endpt_deckP]
    exact Htpy.append_congr g.2 p.2 hg hp) γ c

@[simp] theorem deckV_mk (g : Loop X x₀) (p : PathFrom X x₀) :
    deckV (Quotient.mk _ g) (UV.mk p) = UV.mk (deckP g p) := rfl

@[simp] theorem endV_deckV (γ : Pi1 X x₀) (c : UV X x₀) : endV (deckV γ c) = endV c := by
  induction γ using Quotient.ind with
  | _ g =>
      induction c using UV.ind with
      | h p => exact endpt_deckP g p

theorem deckV_one (c : UV X x₀) : deckV (1 : Pi1 X x₀) c = c := by
  induction c using UV.ind with
  | h p =>
      refine Quotient.sound ?_
      show Htpy X x₀ (endpt X x₀ ([] ++ p.1)) ([] ++ p.1) p.1
      simpa using Htpy.refl p.1

theorem deckV_mul (γ δ : Pi1 X x₀) (c : UV X x₀) :
    deckV (γ * δ) c = deckV γ (deckV δ c) := by
  induction γ using Quotient.ind with
  | _ g =>
      induction δ using Quotient.ind with
      | _ g' =>
          induction c using UV.ind with
          | h p =>
              refine Quotient.sound ?_
              show Htpy X x₀ (endpt X x₀ ((g.1 ++ g'.1) ++ p.1)) ((g.1 ++ g'.1) ++ p.1)
                (g.1 ++ (g'.1 ++ p.1))
              simpa using
                Htpy.refl
                  ((g.1 ++ g'.1) ++ p.1)

theorem extend_deckV (γ : Pi1 X x₀) (eb : X.E × Bool) (c : UV X x₀) :
    extend eb (deckV γ c) = deckV γ (extend eb c) := by
  induction γ using Quotient.ind with
  | _ g =>
      induction c using UV.ind with
      | h p =>
          have hl : (extendP eb (deckP g p)).1 = (deckP g (extendP eb p)).1 := by
            by_cases h : endpt X x₀ p.1 = germSrc X.src X.tgt eb
            · have h' : endpt X x₀ (deckP g p).1 = germSrc X.src X.tgt eb := by
                rw [endpt_deckP]; exact h
              rw [extendP_pos h']
              show (g.1 ++ p.1) ++ [eb] = g.1 ++ (extendP eb p).1
              rw [extendP_pos h]
              simp
            · have h' : ¬ endpt X x₀ (deckP g p).1 = germSrc X.src X.tgt eb := by
                rw [endpt_deckP]; exact h
              rw [extendP_neg h']
              show (deckP g p).1 = g.1 ++ (extendP eb p).1
              rw [extendP_neg h]
              rfl
          refine Quotient.sound ?_
          show Htpy X x₀ (endpt X x₀ (extendP eb (deckP g p)).1) (extendP eb (deckP g p)).1
            (deckP g (extendP eb p)).1
          rw [hl]
          exact Htpy.refl _

/-- The action of the fundamental group on the edges of the universal cover. -/
def deckE (γ : Pi1 X x₀) (E : UE X x₀) : UE X x₀ :=
  ⟨(deckV γ E.1.1, E.1.2), by rw [endV_deckV]; exact E.2⟩

/-- The action of the fundamental group on the two-cells of the universal cover. -/
def deckF (γ : Pi1 X x₀) (F : UF X x₀) : UF X x₀ :=
  ⟨(deckV γ F.1.1, F.1.2), by rw [endV_deckV]; exact F.2⟩


theorem uLiftPath_deckV (γ : Pi1 X x₀) : ∀ (q : List (X.E × Bool)) (c : UV X x₀) (w : X.V),
    IsPath X.src X.tgt q (endV c) w →
      uLiftPath q (deckV γ c) = (uLiftPath q c).map (fun Eb => (deckE γ Eb.1, Eb.2)) := by
  intro q
  induction q with
  | nil => intro c w _; rfl
  | cons eb t ih =>
      intro c w hq
      have h  := hq.1
      have h' : endV (deckV γ c) = germSrc X.src X.tgt eb := by rw [endV_deckV]; exact h
      rw [uLiftPath_cons h', uLiftPath_cons h, List.map_cons, (show liftGerm (deckV γ c) eb h' = (deckE γ (liftGerm c eb h).1, (liftGerm c eb h).2) by
        obtain ⟨e, b⟩ := eb
        cases b with
        | true => rfl
        | false =>
            refine Prod.ext ?_ rfl
            refine Subtype.ext (Prod.ext ?_ rfl)
            exact extend_deckV γ (e, false) c),
        extend_deckV γ eb c,
        ih (extend eb c) w (by rw [endV_extend h]; exact hq.2)]

variable (X x₀) in
/-- The deck action of `π₁(X, x₀)` on the universal cover, by concatenation on the left. -/
def univDeck : DeckAction (uCover X x₀) (Pi1 X x₀) where
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
  att_smul := by
    intro γ F
    show uLiftPath (X.att F.1.2) (deckV γ F.1.1) = _
    have hbase : endV F.1.1 = X.base F.1.2 := F.2
    have hatt : IsPath X.src X.tgt (X.att F.1.2) (endV F.1.1) (X.base F.1.2) := by
      rw [hbase]; exact X.att_isLoop F.1.2
    exact uLiftPath_deckV γ (X.att F.1.2) F.1.1 (X.base F.1.2) hatt

/-- **The universal cover is a regular cover with deck group `π₁(X, x₀)`.** -/
theorem isRegular_univProj : IsRegular (univProj X x₀) (univDeck X x₀) := by
  constructor
  · intro γ c
    exact endV_deckV γ c
  · intro c d hcd
    induction c using UV.ind with
    | h p =>
        induction d using UV.ind with
        | h r =>
            have hv : endpt X x₀ p.1 = endpt X x₀ r.1 := hcd
            have hvp : IsPath X.src X.tgt p.1 x₀ (endpt X x₀ r.1) := by rw [← hv]; exact p.2
            have hrev  := isPath_revPath hvp
            have hrp  :=
              isPath_append_iff.mpr ⟨endpt X x₀ r.1, r.2, hrev⟩
            refine ⟨Quotient.mk _ ⟨r.1 ++ revPath p.1, hrp⟩, ?_, ?_⟩
            · -- the translate of `p` by this loop is `r`
              refine Quotient.sound ?_
              show Htpy X x₀ (endpt X x₀ ((r.1 ++ revPath p.1) ++ p.1))
                ((r.1 ++ revPath p.1) ++ p.1) r.1
              have hend : endpt X x₀ ((r.1 ++ revPath p.1) ++ p.1) = endpt X x₀ r.1 := by
                rw [endpt_append, endpt_eq_of_isPath hrp]
                exact hv
              rw [hend]
              have hB  :=
                htpy_revPath_append hvp
              have hA  :=
                Htpy.append_congr r.2 (isPath_append_iff.mpr ⟨x₀, hrev, hvp⟩) (Htpy.refl _) hB
              have hassoc : (r.1 ++ revPath p.1) ++ p.1 = r.1 ++ (revPath p.1 ++ p.1) := by simp
              rw [hassoc]
              simpa using hA
            · -- uniqueness
              rintro γ hγ
              induction γ using Quotient.ind with
              | _ g =>
                  refine Quotient.sound ?_
                  have hg : Htpy X x₀ (endpt X x₀ (g.1 ++ p.1)) (g.1 ++ p.1) r.1 :=
                    Quotient.exact hγ
                  have hgp :=
                    isPath_append_iff.mpr ⟨x₀, g.2, hvp⟩
                  have hend : endpt X x₀ (g.1 ++ p.1) = endpt X x₀ r.1 :=
                    endpt_eq_of_isPath hgp
                  rw [hend] at hg
                  -- append `revPath p` on the right
                  have h1 :=
                    Htpy.append_congr hgp hrev hg (Htpy.refl _)
                  have h2 :=
                    Htpy.append_congr g.2 (isPath_append_iff.mpr ⟨endpt X x₀ r.1, hvp, hrev⟩)
                      (Htpy.refl _) (htpy_append_revPath hvp)
                  have hassoc : (g.1 ++ p.1) ++ revPath p.1 = g.1 ++ (p.1 ++ revPath p.1) := by
                    simp
                  rw [hassoc] at h1
                  have h3 : Htpy X x₀ x₀ g.1 (g.1 ++ (p.1 ++ revPath p.1)) := by
                    simpa using h2.symm
                  exact h3.trans h1

end Comb
end FiniteChains
end

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
def CEq (Cm : V → V → Prop) : List V → List V → Prop := Relation.ReflTransGen (Swap Cm)

variable {Cm : V → V → Prop}

theorem Swap.symm' (hs : ∀ {a b : V}, Cm a b → Cm b a) {l l' : List V} (h : Swap Cm l l') :
    Swap Cm l' l := by
  induction h with
  | head h q => exact Swap.head (hs h) q
  | cons x _ ih => exact Swap.cons x ih

theorem Swap.length_eq {l l' : List V} (h : Swap Cm l l') : l.length = l'.length := by
  induction h with
  | head h q => simp
  | cons x _ ih => simp_all

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

@[simp] theorem canStart_nil (s : V) : ¬ canStart Cm s ([] : List V) := id

@[simp] theorem canStart_cons {s a : V} {t : List V} :
    canStart Cm s (a :: t) ↔ a = s ∨ (Cm s a ∧ canStart Cm s t) := Iff.rfl

/-- Delete the occurrence of `s` that `canStart` refers to. -/
def popStart [DecidableEq V] (s : V) : List V → List V
  | [] => []
  | a :: t => if a = s then t else a :: popStart s t

@[simp] theorem popStart_nil [DecidableEq V] (s : V) : popStart s ([] : List V) = [] := rfl

@[simp] theorem popStart_cons [DecidableEq V] (s a : V) (t : List V) :
    popStart s (a :: t) = if a = s then t else a :: popStart s t := rfl

/-- A word is **reduced** when no letter can be moved to the front to meet an equal letter. -/
def IsRed (Cm : V → V → Prop) : List V → Prop
  | [] => True
  | a :: t => IsRed Cm t ∧ ¬ canStart Cm a t

@[simp] theorem isRed_nil : IsRed Cm ([] : List V) := trivial

@[simp] theorem isRed_cons {a : V} {t : List V} :
    IsRed Cm (a :: t) ↔ IsRed Cm t ∧ ¬ canStart Cm a t := Iff.rfl

section Basic

variable (hirr : ∀ a : V, ¬ Cm a a) (hsymm : ∀ {a b : V}, Cm a b → Cm b a)
include hirr hsymm

omit hirr in
/-- `canStart` only depends on the trace. -/
theorem canStart_swap {s : V} {l l' : List V} (h : Swap Cm l l') :
    canStart Cm s l ↔ canStart Cm s l' := by
  induction h with
  | @head a b hab q =>
      have hba  := hsymm hab
      simp
      constructor
      · grind
      · grind
  | cons x _ ih => simp_all

omit hirr in
theorem canStart_ceq {s : V} {l l' : List V} (h : CEq Cm l l') :
    canStart Cm s l ↔ canStart Cm s l' := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (canStart_swap hsymm hstep)

/-- Reducedness only depends on the trace. -/
theorem isRed_swap {l l' : List V} (h : Swap Cm l l') : IsRed Cm l ↔ IsRed Cm l' := by
  induction h with
  | @head a b hab q =>
      have hba  := hsymm hab
      have hne : a ≠ b := by rintro rfl; exact hirr _ hab
      simp
      constructor
      · simp_all
      · grind
  | @cons x l₀ l₀' hstep ih =>
      simp only [isRed_cons, ih, canStart_swap hsymm hstep]

theorem isRed_ceq {l l' : List V} (h : CEq Cm l l') : IsRed Cm l ↔ IsRed Cm l' := by
  induction h with
  | refl => rfl
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
        simp
        exact CEq.refl _
      · rcases h with h | ⟨hsa, ht⟩
        · simp_all
        · have h1  := CEq.cons a (ih ht)
          have h2 : Swap Cm (a :: s :: popStart s t) (s :: a :: popStart s t) :=
            Swap.head (hsymm hsa) _
          have h3  := h1.trans (CEq.of_swap h2)
          simpa [hat] using h3

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
theorem isRed_popStart {s : V} {l : List V} (hl : IsRed Cm l) (h : canStart Cm s l) :
    IsRed Cm (popStart s l) :=
  ((isRed_ceq hirr hsymm (ceq_popStart hsymm h)).1 hl).1

/-- After deleting the front occurrence of `s` from a reduced word, `s` can no longer be moved
to the front. -/
theorem not_canStart_popStart {s : V} {l : List V} (hl : IsRed Cm l) (h : canStart Cm s l) :
    ¬ canStart Cm s (popStart s l) :=
  ((isRed_ceq hirr hsymm (ceq_popStart hsymm h)).1 hl).2

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
        · by_cases har : a = r
          · subst har
            exact ⟨hsa, by simp [has]⟩
          · rcases hr with h | ⟨hra, hrt⟩
            · exact absurd h har
            · obtain ⟨hcom, hpop⟩ := ih hst hrt
              exact ⟨hcom, by simp [has, har, hra, hpop]⟩

end Basic

end RACG
end FiniteChains

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains
namespace RACG

universe u

/-- A **commutation graph**: a symmetric irreflexive relation on the alphabet `V`.  Two letters
related by `rel` are the generators of a `(s t)² = 1` relation of the right-angled Coxeter
group. -/
structure CommRel (V : Type u) where
  /-- The commutation relation. -/
  rel : V → V → Prop
  /-- It is symmetric. -/
  rel_symm : ∀ {a b : V}, rel a b → rel b a
  /-- No letter commutes with itself (letters are distinct generators). -/
  rel_irrefl : ∀ a : V, ¬ rel a a

variable {V : Type u} [DecidableEq V] (A : CommRel V)

/-- Reduced words, with trace equality. -/
def redSetoid : Setoid {l : List V // IsRed A.rel l} where
  r a b := CEq A.rel a.1 b.1
  iseqv :=
    ⟨fun _ => CEq.refl _, fun h => CEq.symm A.rel_symm h, fun h h' => h.trans h'⟩

/-- The set of **reduced traces**: reduced words modulo commutation.  This is the vertex set of
the Cayley graph of the right-angled Coxeter group. -/
def Tr : Type u := Quotient (redSetoid A)

/-- The trace of a reduced word. -/
def mkTr (l : List V) (h : IsRed A.rel l) : Tr A := Quotient.mk (redSetoid A) ⟨l, h⟩

omit [DecidableEq V] in
theorem mkTr_eq_iff {l m : List V} (hl : IsRed A.rel l) (hm : IsRed A.rel m) :
    mkTr A l hl = mkTr A m hm ↔ CEq A.rel l m :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- The empty trace: the identity element. -/
def oneTr : Tr A := mkTr A [] trivial

/-- The length of a reduced trace. -/
def trLen : Tr A → ℕ :=
  Quotient.lift (fun l : {l : List V // IsRed A.rel l} => l.1.length)
    (fun _ _ h => CEq.length_eq h)

omit [DecidableEq V] in
@[simp] theorem trLen_mkTr (l : List V) (h : IsRed A.rel l) : trLen A (mkTr A l h) = l.length :=
  rfl

omit [DecidableEq V] in
@[simp] theorem trLen_one : trLen A (oneTr A) = 0 := rfl

open Classical in
/-- The elementary move on reduced words: delete the letter `s` from the front if it can be
moved there, otherwise prepend it. -/
def actRep (s : V) (l : {l : List V // IsRed A.rel l}) :
    {l : List V // IsRed A.rel l} :=
  if h : canStart A.rel s l.1 then
    ⟨popStart s l.1, isRed_popStart A.rel_irrefl A.rel_symm l.2 h⟩
  else ⟨s :: l.1, ⟨l.2, h⟩⟩

theorem actRep_of_canStart {s : V} {l : {l : List V // IsRed A.rel l}}
    (h : canStart A.rel s l.1) : (actRep A s l).1 = popStart s l.1 := by
  simp [actRep, h]

theorem actRep_of_not_canStart {s : V} {l : {l : List V // IsRed A.rel l}}
    (h : ¬ canStart A.rel s l.1) : (actRep A s l).1 = s :: l.1 := by
  simp [actRep, h]

theorem actRep_respects {s : V} {a b : {l : List V // IsRed A.rel l}} (h : CEq A.rel a.1 b.1) :
    CEq A.rel (actRep A s a).1 (actRep A s b).1 := by
  by_cases ha : canStart A.rel s a.1
  · have hb  := (canStart_ceq A.rel_symm h).1 ha
    rw [actRep_of_canStart A ha, actRep_of_canStart A hb]
    exact popStart_ceq A.rel_irrefl h
  · have hb  := fun hb => ha ((canStart_ceq A.rel_symm h).2 hb)
    rw [actRep_of_not_canStart A ha, actRep_of_not_canStart A hb]
    exact CEq.cons s h

/-- The elementary move on reduced traces. -/
def act (s : V) : Tr A → Tr A :=
  Quotient.map (actRep A s) (fun _ _ h => actRep_respects A h)

@[simp] theorem act_mk (s : V) (l : List V) (h : IsRed A.rel l) :
    act A s (mkTr A l h) = Quotient.mk (redSetoid A) (actRep A s ⟨l, h⟩) := rfl

theorem act_involutive (s : V) : Function.Involutive (act A s) := by
  intro t
  induction t using Quotient.inductionOn with
  | _ l =>
      by_cases h : canStart A.rel s l.1
      · have h1  := actRep_of_canStart A h
        have h2 : ¬ canStart A.rel s (actRep A s l).1 := by
          rw [h1]; exact not_canStart_popStart A.rel_irrefl A.rel_symm l.2 h
        have h3 : (actRep A s (actRep A s l)).1 = s :: popStart s l.1 := by
          rw [actRep_of_not_canStart A h2, h1]
        refine Quotient.sound ?_
        show CEq A.rel (actRep A s (actRep A s l)).1 l.1
        rw [h3]
        exact CEq.symm A.rel_symm (ceq_popStart A.rel_symm h)
      · have h1  := actRep_of_not_canStart A h
        have h2 : canStart A.rel s (actRep A s l).1 := by rw [h1]; exact Or.inl rfl
        have h3 : (actRep A s (actRep A s l)).1 = l.1 := by
          rw [actRep_of_canStart A h2, h1]; simp
        refine Quotient.sound ?_
        show CEq A.rel (actRep A s (actRep A s l)).1 l.1
        rw [h3]
        exact CEq.refl _

/-- The elementary move as a permutation of the set of reduced traces. -/
def actPerm (s : V) : Equiv.Perm (Tr A) := (act_involutive A s).toPerm _

@[simp] theorem actPerm_apply (s : V) (t : Tr A) : actPerm A s t = act A s t := rfl

theorem actPerm_inv (s : V) : (actPerm A s)⁻¹ = actPerm A s :=
  inv_eq_of_mul_eq_one_left (by ext t; simpa using act_involutive A s t)

theorem act_mkTr_of_canStart {s : V} {l : List V} (hl : IsRed A.rel l)
    (h : canStart A.rel s l) :
    act A s (mkTr A l hl) = mkTr A (popStart s l) (isRed_popStart A.rel_irrefl A.rel_symm hl h) :=
  Quotient.sound (by
    show CEq A.rel (actRep A s ⟨l, hl⟩).1 (popStart s l)
    rw [actRep_of_canStart A h]
    exact CEq.refl _)

theorem act_mkTr_of_not_canStart {s : V} {l : List V} (hl : IsRed A.rel l)
    (h : ¬ canStart A.rel s l) :
    act A s (mkTr A l hl) = mkTr A (s :: l) ⟨hl, h⟩ :=
  Quotient.sound (by
    show CEq A.rel (actRep A s ⟨l, hl⟩).1 (s :: l)
    rw [actRep_of_not_canStart A h]
    exact CEq.refl _)

/-- Commuting letters give commuting moves. -/

theorem actPerm_mul_comm {s r : V} (h : A.rel s r) :
    actPerm A s * actPerm A r = actPerm A r * actPerm A s := by
  ext t
  simpa using (by
    have hrs  := A.rel_symm h
    have hsr : s ≠ r := by rintro rfl; exact A.rel_irrefl s h
    induction t using Quotient.inductionOn with
    | _ lp =>
      obtain ⟨l, hl⟩ := lp
      show act A s (act A r (mkTr A l hl)) = act A r (act A s (mkTr A l hl))
      by_cases hs : canStart A.rel s l
      · by_cases hr : canStart A.rel r l
        · -- both letters can be moved to the front
          obtain ⟨-, hrs'⟩ := canStart_two A.rel_symm hsr hs hr
          obtain ⟨-, hsr'⟩ := canStart_two A.rel_symm (Ne.symm hsr) hr hs
          rw [act_mkTr_of_canStart A hl hr, act_mkTr_of_canStart A _ hsr',
            act_mkTr_of_canStart A hl hs, act_mkTr_of_canStart A _ hrs']
          refine (mkTr_eq_iff A _ _).2 ?_
          -- both sides are obtained from `l` by deleting one `s` and one `r`
          have e1  :=
            (ceq_popStart A.rel_symm hs).trans
              (CEq.cons s (ceq_popStart A.rel_symm hrs'))
          have e2  :=
            (ceq_popStart A.rel_symm hr).trans
              (CEq.cons r (ceq_popStart A.rel_symm hsr'))
          have e3 : CEq A.rel (s :: r :: popStart r (popStart s l))
              (r :: s :: popStart r (popStart s l)) := CEq.of_swap (Swap.head h _)
          have e4 : CEq A.rel (r :: s :: popStart r (popStart s l))
              (r :: s :: popStart s (popStart r l)) :=
            (CEq.symm A.rel_symm (e1.trans e3)).trans e2
          exact CEq.symm A.rel_symm (cancel_head A.rel_irrefl (cancel_head A.rel_irrefl e4))
        · -- only `s` can
          have hr' : ¬ canStart A.rel r (popStart s l) := by
            intro hc
            exact hr ((canStart_ceq A.rel_symm (ceq_popStart A.rel_symm hs)).2
              (Or.inr ⟨hrs, hc⟩))
          have hs' : canStart A.rel s (r :: l) := Or.inr ⟨h, hs⟩
          rw [act_mkTr_of_not_canStart A hl hr, act_mkTr_of_canStart A _ hs',
            act_mkTr_of_canStart A hl hs, act_mkTr_of_not_canStart A _ hr']
          refine (mkTr_eq_iff A _ _).2 ?_
          have : popStart s (r :: l) = r :: popStart s l := by
            simp [popStart, Ne.symm hsr]
          rw [this]
          exact CEq.refl _
      · by_cases hr : canStart A.rel r l
        · -- only `r` can
          have hs' : ¬ canStart A.rel s (popStart r l) := by
            intro hc
            exact hs ((canStart_ceq A.rel_symm (ceq_popStart A.rel_symm hr)).2
              (Or.inr ⟨h, hc⟩))
          have hr' : canStart A.rel r (s :: l) := Or.inr ⟨hrs, hr⟩
          rw [act_mkTr_of_canStart A hl hr, act_mkTr_of_not_canStart A _ hs',
            act_mkTr_of_not_canStart A hl hs, act_mkTr_of_canStart A _ hr']
          refine (mkTr_eq_iff A _ _).2 ?_
          have : popStart r (s :: l) = s :: popStart r l := by
            simp [popStart, hsr]
          rw [this]
          exact CEq.refl _
        · -- neither can
          have hs' : ¬ canStart A.rel s (r :: l) := by
            rintro (rfl | ⟨-, hc⟩)
            · exact hsr rfl
            · exact hs hc
          have hr' : ¬ canStart A.rel r (s :: l) := by
            rintro (rfl | ⟨-, hc⟩)
            · exact hsr rfl
            · exact hr hc
          rw [act_mkTr_of_not_canStart A hl hr, act_mkTr_of_not_canStart A _ hs',
            act_mkTr_of_not_canStart A hl hs, act_mkTr_of_not_canStart A _ hr']
          exact (mkTr_eq_iff A _ _).2 (CEq.of_swap (Swap.head h l)))

theorem actPerm_mul_self (s : V) : actPerm A s * actPerm A s = 1 := by
  ext t
  simpa using act_involutive A s t

/-- The permutation of reduced traces determined by a word. -/
def wordPerm (l : List V) : Equiv.Perm (Tr A) := (l.map (actPerm A)).prod

@[simp] theorem wordPerm_nil : wordPerm A [] = 1 := rfl


@[simp] theorem wordPerm_cons (s : V) (l : List V) :
    wordPerm A (s :: l) = actPerm A s * wordPerm A l := rfl

theorem wordPerm_append (l m : List V) :
    wordPerm A (l ++ m) = wordPerm A l * wordPerm A m := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih, mul_assoc]

theorem wordPerm_reverse (l : List V) : wordPerm A l.reverse = (wordPerm A l)⁻¹ := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have hc  := wordPerm_cons A a t
      rw [List.reverse_cons, wordPerm_append, ih, hc, mul_inv_rev, actPerm_inv]
      simp

theorem wordPerm_swap {l m : List V} (h : Swap A.rel l m) : wordPerm A l = wordPerm A m := by
  induction h with
  | @head a b hab q =>
      simp only [wordPerm_cons, ← mul_assoc]
      rw [actPerm_mul_comm A hab]
  | cons x _ ih => simp_all

/-- Words with the same trace act in the same way. -/
theorem wordPerm_ceq {l m : List V} (h : CEq A.rel l m) : wordPerm A l = wordPerm A m := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (wordPerm_swap A hstep)

/-- Deleting a cancelling pair does not change the action. -/
theorem wordPerm_cancel (s : V) (l : List V) :
    wordPerm A (s :: s :: l) = wordPerm A l := by
  simp only [wordPerm_cons, ← mul_assoc, actPerm_mul_self, one_mul]

/-- A reduced word acts on the empty trace by producing its own trace. -/
theorem wordPerm_apply_one : ∀ {l : List V} (h : IsRed A.rel l),
    wordPerm A l (oneTr A) = mkTr A l h
  | [], _ => rfl
  | a :: t, h => by
      have ht : IsRed A.rel t := h.1
      have hna : ¬ canStart A.rel a t := h.2
      have : wordPerm A (a :: t) (oneTr A) = act A a (wordPerm A t (oneTr A)) := by
        simp [wordPerm_cons]
      rw [this, wordPerm_apply_one ht, act_mkTr_of_not_canStart A ht hna]

/-- A word that is not reduced can be shortened without changing its action. -/
theorem exists_shorter_of_not_isRed :
    ∀ {l : List V}, ¬ IsRed A.rel l →
      ∃ m : List V, m.length < l.length ∧ wordPerm A m = wordPerm A l
  | [], h => absurd isRed_nil h
  | a :: t, h => by
      by_cases hc : canStart A.rel a t
      · refine ⟨popStart a t, ?_, ?_⟩
        · have := length_popStart A.rel_symm (Cm := A.rel) (s := a) hc
          simp only [List.length_cons]
          omega
        · have h1 : wordPerm A t = wordPerm A (a :: popStart a t) :=
            wordPerm_ceq A (ceq_popStart A.rel_symm hc)
          calc wordPerm A (popStart a t)
              = wordPerm A (a :: a :: popStart a t) := (wordPerm_cancel A a _).symm
            _ = actPerm A a * wordPerm A (a :: popStart a t) := by rw [wordPerm_cons]
            _ = actPerm A a * wordPerm A t := by rw [h1]
            _ = wordPerm A (a :: t) := (wordPerm_cons A a t).symm
      · have ht : ¬ IsRed A.rel t := fun ht => h ⟨ht, hc⟩
        obtain ⟨m, hm, hm'⟩ := exists_shorter_of_not_isRed ht
        exact ⟨a :: m, by simpa using hm, by simp [wordPerm_cons, hm']⟩

/-- Every word can be shortened to a reduced word acting in the same way. -/
theorem exists_isRed_word (l : List V) :
    ∃ m : List V, IsRed A.rel m ∧ m.length ≤ l.length ∧ wordPerm A m = wordPerm A l := by
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
      subst hn
      by_cases hred : IsRed A.rel l
      · grind
      · obtain ⟨m, hlt, hperm⟩ := exists_shorter_of_not_isRed A hred
        obtain ⟨m', hm', hlen, hperm'⟩ := ih m.length hlt m rfl
        exact ⟨m', hm', by omega, by rw [hperm', hperm]⟩

/-- The length of an element of the right-angled Coxeter group: the length of its reduced
trace. -/
def len (w : Equiv.Perm (Tr A)) : ℕ := trLen A (w (oneTr A))

omit [DecidableEq V] in
@[simp] theorem len_one : len A 1 = 0 := rfl

/-- The trace length changes by one under an elementary move. -/
theorem trLen_act (s : V) (t : Tr A) :
    trLen A (act A s t) + 1 = trLen A t ∨ trLen A (act A s t) = trLen A t + 1 := by
  induction t using Quotient.inductionOn with
  | _ lp =>
      obtain ⟨l, hl⟩ := lp
      by_cases hc : canStart A.rel s l
      · left
        rw [show (Quotient.mk (redSetoid A) ⟨l, hl⟩ : Tr A) = mkTr A l hl from rfl,
          act_mkTr_of_canStart A hl hc]
        simpa using length_popStart A.rel_symm hc
      · right
        rw [show (Quotient.mk (redSetoid A) ⟨l, hl⟩ : Tr A) = mkTr A l hl from rfl,
          act_mkTr_of_not_canStart A hl hc]
        simp

theorem len_le_length (l : List V) : len A (wordPerm A l) ≤ l.length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      have h1 : wordPerm A (a :: t) (oneTr A) = act A a (wordPerm A t (oneTr A)) := by
        simp [wordPerm_cons]
      have h2 := trLen_act A a (wordPerm A t (oneTr A))
      simp only [len, h1, List.length_cons] at *
      omega

end RACG
end FiniteChains
end

namespace FiniteChains
namespace RACG

universe u

variable {V : Type u} [DecidableEq V] (A : CommRel V)

/-- The group of the right-angled Coxeter system, realised as permutations of the reduced
traces. -/
def CayGroup : Subgroup (Equiv.Perm (Tr A)) := Subgroup.closure (Set.range (actPerm A))

/-- A generator, as an element of the group. -/
def gen (s : V) : CayGroup A :=
  ⟨actPerm A s, Subgroup.subset_closure ⟨s, rfl⟩⟩

/-- The word length of an element of the group. -/
def clen (x : CayGroup A) : ℕ := len A (x : Equiv.Perm (Tr A))

/-- The element of the group determined by a word. -/
def cword (l : List V) : CayGroup A :=
  ⟨wordPerm A l, by
    induction l with
    | nil => simp
    | cons a t ih =>
        rw [wordPerm_cons]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨a, rfl⟩) ih⟩

@[simp] theorem cword_val (l : List V) : ((cword A l : CayGroup A) : Equiv.Perm (Tr A))
    = wordPerm A l := rfl

@[simp] theorem cword_cons (s : V) (l : List V) : cword A (s :: l) = gen A s * cword A l :=
  Subtype.ext (by simp [gen])

@[simp] theorem cword_nil : cword A [] = 1 := Subtype.ext (by simp)

theorem cword_ceq {l m : List V} (h : CEq A.rel l m) : cword A l = cword A m :=
  Subtype.ext (by simpa using wordPerm_ceq A h)

theorem gen_mul_gen (s : V) : gen A s * gen A s = 1 :=
  Subtype.ext (by simpa [gen] using actPerm_mul_self A s)

theorem cword_apply_one {l : List V} (hl : IsRed A.rel l) :
    ((cword A l : CayGroup A) : Equiv.Perm (Tr A)) (oneTr A) = mkTr A l hl :=
  wordPerm_apply_one A hl

theorem exists_cword (x : CayGroup A) : ∃ l : List V, IsRed A.rel l ∧ cword A l = x := by
  obtain ⟨p, hp⟩ : ∃ l : List V, wordPerm A l = x := by
    refine Subgroup.closure_induction
      ?_ ?_ ?_ ?_ x.2
    · rintro g ⟨s, rfl⟩
      exact ⟨[s], by simp⟩
    · exact ⟨[], by simp⟩
    · rintro g h - - ⟨l, rfl⟩ ⟨m, rfl⟩
      exact ⟨l ++ m, by rw [wordPerm_append]⟩
    · rintro g - ⟨l, rfl⟩
      exact ⟨l.reverse, by rw [wordPerm_reverse]⟩
  obtain ⟨m, hm, -, hmp⟩ := exists_isRed_word A p
  exact ⟨m, hm, Subtype.ext (by rw [cword_val, hmp, hp])⟩

theorem clen_cword {l : List V} (hl : IsRed A.rel l) : clen A (cword A l) = l.length := by
  show trLen A (((cword A l : CayGroup A) : Equiv.Perm (Tr A)) (oneTr A)) = l.length
  rw [cword_apply_one A hl, trLen_mkTr]

theorem clen_eq_zero_iff {x : CayGroup A} : clen A x = 0 ↔ x = 1 := by
  constructor
  · intro h
    obtain ⟨l, hl, rfl⟩ := exists_cword A x
    rw [clen_cword A hl] at h
    have : l = [] := List.eq_nil_of_length_eq_zero h
    simp [this]
  · rintro rfl
    simp [clen, len]

@[simp] theorem clen_one : clen A (1 : CayGroup A) = 0 := (clen_eq_zero_iff A).2 rfl

theorem clen_le_of_cword {l : List V} {x : CayGroup A} (h : cword A l = x) :
    clen A x ≤ l.length := by
  rw [← h]
  exact len_le_length A l

theorem clen_inv (x : CayGroup A) : clen A x⁻¹ = clen A x := by
  have key : ∀ y : CayGroup A, clen A y⁻¹ ≤ clen A y := by
    intro y
    obtain ⟨l, hl, rfl⟩ := exists_cword A y
    have h1 : cword A l.reverse = (cword A l)⁻¹ :=
      Subtype.ext (by simpa using wordPerm_reverse A l)
    have := clen_le_of_cword A h1
    simpa [clen_cword A hl] using this
  have h1 := key x
  have h2 := key x⁻¹
  simp at h2
  omega

/-- `s` is a left descent of `x`: multiplying by `s` on the left shortens `x`. -/
def IsDesc (x : CayGroup A) (s : V) : Prop := clen A (gen A s * x) < clen A x

/-- Descents are visible on any reduced word: `s` shortens `x` exactly when it can be moved to
the front of a reduced word for `x`. -/
theorem isDesc_iff_canStart {x : CayGroup A} {l : List V} (hl : IsRed A.rel l)
    (hx : cword A l = x) (s : V) : IsDesc A x s ↔ canStart A.rel s l := by
  subst hx
  by_cases hc : canStart A.rel s l
  · have hpop : gen A s * cword A l = cword A (popStart s l) := by
      have h1  :=
        cword_ceq A (ceq_popStart A.rel_symm hc)
      rw [h1, cword_cons, ← mul_assoc, gen_mul_gen, one_mul]
    have hred  := isRed_popStart A.rel_irrefl A.rel_symm hl hc
    have hlen  := length_popStart A.rel_symm hc
    simp only [IsDesc, hpop, clen_cword A hred, clen_cword A hl, hc, iff_true]
    omega
  · have hred : IsRed A.rel (s :: l) := ⟨hl, hc⟩
    have hcons  := (cword_cons A s l).symm
    simp only [IsDesc, hcons, clen_cword A hred, clen_cword A hl, hc, iff_false,
      List.length_cons, not_lt]
    omega


theorem clen_gen_mul_of_not_desc {x : CayGroup A} {s : V} (h : ¬ IsDesc A x s) :
    clen A (gen A s * x) = clen A x + 1 := by
  have hlt : ¬ clen A (gen A s * x) < clen A x := h
  rcases (show clen A (gen A s * x) + 1 = clen A x ∨ clen A (gen A s * x) = clen A x + 1 by
    obtain ⟨l, hl, rfl⟩ := exists_cword A x
    by_cases hc : canStart A.rel s l
    · left
      have hpop : gen A s * cword A l = cword A (popStart s l) := by
        have h1  :=
          cword_ceq A (ceq_popStart A.rel_symm hc)
        rw [h1, cword_cons, ← mul_assoc, gen_mul_gen, one_mul]
      have hred  := isRed_popStart A.rel_irrefl A.rel_symm hl hc
      rw [hpop, clen_cword A hred, clen_cword A hl]
      exact length_popStart A.rel_symm hc
    · right
      have hred : IsRed A.rel (s :: l) := ⟨hl, hc⟩
      rw [← cword_cons, clen_cword A hred, clen_cword A hl]
      simp) with h' | h'
  · omega
  · exact h'

theorem gen_mul_gen_mul (x : CayGroup A) (s : V) : gen A s * (gen A s * x) = x := by
  rw [← mul_assoc, gen_mul_gen, one_mul]

theorem exists_desc {x : CayGroup A} (hx : x ≠ 1) : ∃ s : V, IsDesc A x s := by
  obtain ⟨l, hl, rfl⟩ := exists_cword A x
  match l, hl with
  | [], _ => exact absurd (cword_nil A) hx
  | a :: t, hl =>
      exact ⟨a, (isDesc_iff_canStart A hl rfl a).2 (Or.inl rfl)⟩

/-- **The right-angled descent lemma.**  Two distinct left descents of an element commute, and
the second one is still a descent after the first has been removed. -/
theorem desc_two {x : CayGroup A} {s r : V} (hsr : s ≠ r) (hs : IsDesc A x s)
    (hr : IsDesc A x r) : A.rel s r ∧ IsDesc A (gen A s * x) r := by
  obtain ⟨l, hl, rfl⟩ := exists_cword A x
  have hcs  := (isDesc_iff_canStart A hl rfl s).1 hs
  have hcr  := (isDesc_iff_canStart A hl rfl r).1 hr
  obtain ⟨hrel, hpopr⟩ := canStart_two A.rel_symm hsr hcs hcr
  refine ⟨hrel, ?_⟩
  have hpop : gen A s * cword A l = cword A (popStart s l) := by
    have h1  :=
      cword_ceq A (ceq_popStart A.rel_symm hcs)
    rw [h1, cword_cons, ← mul_assoc, gen_mul_gen, one_mul]
  have hred  := isRed_popStart A.rel_irrefl A.rel_symm hl hcs
  rw [hpop]
  exact (isDesc_iff_canStart A hred rfl r).2 hpopr

/-- The left descents of an element pairwise commute. -/
theorem desc_rel {x : CayGroup A} {s r : V} (hsr : s ≠ r) (hs : IsDesc A x s)
    (hr : IsDesc A x r) : A.rel s r := (desc_two A hsr hs hr).1

/-- A descent of a commuting letter survives prefixing. -/
theorem desc_gen_mul_of_rel {x : CayGroup A} {s r : V} (hrel : A.rel s r) (hs : IsDesc A x s) :
    IsDesc A (gen A r * x) s := by
  have hrs : s ≠ r := by rintro rfl; exact A.rel_irrefl s hrel
  obtain ⟨l, hl, rfl⟩ := exists_cword A x
  have hcs  := (isDesc_iff_canStart A hl rfl s).1 hs
  by_cases hcr : canStart A.rel r l
  · obtain ⟨-, hpops⟩ := canStart_two A.rel_symm (Ne.symm hrs) hcr hcs
    have hpop : gen A r * cword A l = cword A (popStart r l) := by
      have h1  :=
        cword_ceq A (ceq_popStart A.rel_symm hcr)
      rw [h1, cword_cons, ← mul_assoc, gen_mul_gen, one_mul]
    have hred  := isRed_popStart A.rel_irrefl A.rel_symm hl hcr
    rw [hpop]
    exact (isDesc_iff_canStart A hred rfl s).2 hpops
  · have hred : IsRed A.rel (r :: l) := ⟨hl, hcr⟩
    rw [← cword_cons]
    exact (isDesc_iff_canStart A hred rfl s).2 (Or.inr ⟨hrel, hcs⟩)

end RACG
end FiniteChains

namespace FiniteChains
namespace RACG

universe u

variable {V : Type u} [DecidableEq V] (A : CommRel V)

theorem gen_inv (s : V) : (gen A s)⁻¹ = gen A s :=
  inv_eq_of_mul_eq_one_left (gen_mul_gen A s)

end RACG
end FiniteChains

namespace FiniteChains
namespace RACG

universe u

variable {V : Type u} [DecidableEq V] (A : CommRel V)

/-! ### Right descents -/

/-- `s` is a **right descent** of `x`: multiplying by `s` on the right shortens `x`.  This is
the set `D(w) = {s : ℓ(ws) < ℓ(w)}` of the chamber argument. -/
def IsRDesc (x : CayGroup A) (s : V) : Prop := clen A (x * gen A s) < clen A x


/-- Right descents of `x` are the left descents of `x⁻¹`. -/
theorem isRDesc_iff_isDesc (x : CayGroup A) (s : V) : IsRDesc A x s ↔ IsDesc A x⁻¹ s := by
  unfold IsRDesc IsDesc
  rw [(show clen A (x * gen A s) = clen A (gen A s * x⁻¹) by
    have h : (x * gen A s)⁻¹ = gen A s * x⁻¹ := by
      rw [mul_inv_rev, gen_inv]
    rw [← clen_inv A (x * gen A s), h]), clen_inv A x]

/-- **The descent set is a simplex of `L`**: two distinct right descents commute. -/
theorem rdesc_rel {x : CayGroup A} {s r : V} (hsr : s ≠ r) (hs : IsRDesc A x s)
    (hr : IsRDesc A x r) : A.rel s r :=
  desc_rel A hsr ((isRDesc_iff_isDesc A x s).1 hs) ((isRDesc_iff_isDesc A x r).1 hr)

/-- **The descent set is nonempty** for `x ≠ 1`. -/
theorem exists_rdesc {x : CayGroup A} (hx : x ≠ 1) : ∃ s : V, IsRDesc A x s := by
  obtain ⟨s, hs⟩ := exists_desc A (x := x⁻¹) (by simpa using hx)
  exact ⟨s, (isRDesc_iff_isDesc A x s).2 hs⟩

/-! ### Simplices of `L` and their special subgroups -/

/-- A set of generators spanning a simplex of the flag complex `L`: its elements pairwise
commute. -/
def Commuting (T : Set V) : Prop := ∀ ⦃s⦄, s ∈ T → ∀ ⦃r⦄, r ∈ T → s ≠ r → A.rel s r

/-- The special subgroup `W_T`, generated by the generators indexed by `T`. -/
def specialSub (T : Set V) : Subgroup (CayGroup A) :=
  Subgroup.closure (gen A '' T)

theorem gen_mem_specialSub {T : Set V} {s : V} (hs : s ∈ T) : gen A s ∈ specialSub A T :=
  Subgroup.subset_closure ⟨s, hs, rfl⟩

/-- Two commuting generators commute in the group. -/
theorem gen_comm {s r : V} (h : A.rel s r) : gen A s * gen A r = gen A r * gen A s := by
  have h1 : gen A s * gen A r = cword A [s, r] := by simp
  have h2 : gen A r * gen A s = cword A [r, s] := by simp
  rw [h1, h2]
  exact cword_ceq A (CEq.of_swap (Swap.head h []))

theorem cword_mem_specialSub {T : Set V} {l : List V} (hl : ∀ a ∈ l, a ∈ T) :
    cword A l ∈ specialSub A T := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [cword_cons]
      exact Subgroup.mul_mem _ (gen_mem_specialSub A (hl a (by simp)))
        (ih fun b hb => hl b (by simp [hb]))

/-- Every element of `W_T` is the product of a list of generators from `T`. -/
theorem exists_cword_of_mem_specialSub {T : Set V} {u : CayGroup A} (hu : u ∈ specialSub A T) :
    ∃ l : List V, (∀ a ∈ l, a ∈ T) ∧ cword A l = u := by
  classical
  refine Subgroup.closure_induction (p := fun v _ => ∃ l : List V, (∀ a ∈ l, a ∈ T) ∧
    cword A l = v) ?_ ?_ ?_ ?_ hu
  · rintro v ⟨s, hs, rfl⟩
    exact ⟨[s], by simpa using hs, by simp⟩
  · exact ⟨[], by simp, by simp⟩
  · rintro v w _ _ ⟨l, hl, rfl⟩ ⟨m, hm, rfl⟩
    refine ⟨l ++ m, ?_, ?_⟩
    · intro a ha
      rcases List.mem_append.1 ha with h | h
      exacts [hl a h, hm a h]
    · exact Subtype.ext (by simpa using wordPerm_append A l m)
  · rintro v _ ⟨l, hl, rfl⟩
    refine ⟨l.reverse, ?_, ?_⟩
    · intro a ha; exact hl a (List.mem_reverse.1 ha)
    · exact Subtype.ext (by simpa using wordPerm_reverse A l)

/-- Cancelling a generator inside a duplicate-free word of pairwise commuting letters. -/
theorem gen_mul_cword_erase {T : Set V} (hT : Commuting A T) {s : V} (hs : s ∈ T) :
    ∀ l : List V, (∀ a ∈ l, a ∈ T) → l.Nodup → s ∈ l →
      gen A s * cword A l = cword A (l.erase s) := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
      intro hl hnd hmem
      by_cases hat : a = s
      · subst hat
        simp [cword_cons, ← mul_assoc, gen_mul_gen]
      · have hst : s ∈ t := by
          rcases List.mem_cons.1 hmem with h | h
          · simp_all
          · exact h
        have hrel := hT hs (hl a (by simp)) (fun h => hat h.symm)
        have iht := ih (fun b hb => hl b (by simp [hb])) hnd.of_cons hst
        calc gen A s * cword A (a :: t)
            = (gen A s * gen A a) * cword A t := by rw [cword_cons, mul_assoc]
          _ = gen A a * (gen A s * cword A t) := by rw [gen_comm A hrel, mul_assoc]
          _ = gen A a * cword A (t.erase s) := by rw [iht]
          _ = cword A (a :: t.erase s) := (cword_cons A _ _).symm
          _ = cword A ((a :: t).erase s) := by rw [List.erase_cons_tail (by simpa using hat)]

/-- **Normal form in `W_T ≅ (ℤ/2)^T`**: every element of the special subgroup of a simplex is
the product of a duplicate-free list of its generators. -/
theorem exists_nodup_cword {T : Set V} (hT : Commuting A T) {u : CayGroup A}
    (hu : u ∈ specialSub A T) :
    ∃ l : List V, (∀ a ∈ l, a ∈ T) ∧ l.Nodup ∧ cword A l = u := by
  classical
  obtain ⟨l, hl, rfl⟩ := exists_cword_of_mem_specialSub A hu
  clear hu
  induction l with
  | nil => exact ⟨[], by simp, by simp, rfl⟩
  | cons a t ih =>
      obtain ⟨m, hm, hnd, hmt⟩ := ih fun b hb => hl b (by simp [hb])
      have ha : a ∈ T := hl a (by simp)
      by_cases hmem : a ∈ m
      · refine ⟨m.erase a, fun b hb => hm b (List.mem_of_mem_erase hb), hnd.erase a, ?_⟩
        rw [← gen_mul_cword_erase A hT ha m hm hnd hmem, hmt, cword_cons]
      · refine ⟨a :: m, ?_, by simpa using ⟨hmem, hnd⟩, by rw [cword_cons, hmt, cword_cons]⟩
        intro b hb
        rcases List.mem_cons.1 hb with h | h
        · exact h ▸ ha
        · exact hm b h

/-! ### Elements without descents in a simplex -/

/-- If no generator of the simplex `T` shortens `x` from the left, then no generator of `T`
missing from a word over `T` shortens the product from the left either. -/
theorem not_isDesc_cword_mul {T : Set V} (hT : Commuting A T) {x : CayGroup A}
    (hx : ∀ s ∈ T, ¬ IsDesc A x s) {s : V} (hs : s ∈ T) :
    ∀ l : List V, (∀ a ∈ l, a ∈ T) → s ∉ l → ¬ IsDesc A (cword A l * x) s := by
  intro l
  induction l with
  | nil => simp_all
  | cons a t ih =>
      intro hl hsl
      have hat : a ≠ s := fun h => hsl (by simp [h])
      have hrel := hT hs (hl a (by simp)) (fun h => hat h.symm)
      have iht := ih (fun b hb => hl b (by simp [hb])) (fun h => hsl (by simp [h]))
      intro hcon
      rw [cword_cons, mul_assoc] at hcon
      exact iht (by simpa [gen_mul_gen_mul] using desc_gen_mul_of_rel A hrel hcon)

/-- **Lengths add**: if no generator of `T` shortens `x` from the left, then the length of
`u * x` is the sum of the lengths, for `u ∈ W_T` written as a duplicate-free word. -/
theorem clen_cword_mul {T : Set V} (hT : Commuting A T) {x : CayGroup A}
    (hx : ∀ s ∈ T, ¬ IsDesc A x s) :
    ∀ l : List V, (∀ a ∈ l, a ∈ T) → l.Nodup →
      clen A (cword A l * x) = l.length + clen A x := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
      intro hl hnd
      have iht := ih (fun b hb => hl b (by simp [hb])) hnd.of_cons
      have hnot : ¬ IsDesc A (cword A t * x) a :=
        not_isDesc_cword_mul A hT hx (hl a (by simp)) t
          (fun b hb => hl b (by simp [hb])) (by simpa using (List.nodup_cons.1 hnd).1)
      have hstep := clen_gen_mul_of_not_desc A hnot
      rw [cword_cons, mul_assoc, hstep, iht]
      simp [Nat.add_right_comm]

theorem clen_lt_of_mem_specialSub_left {T : Set V} (hT : Commuting A T) {x : CayGroup A}
    (hx : ∀ s ∈ T, ¬ IsDesc A x s) {u : CayGroup A} (hu : u ∈ specialSub A T) (hu1 : u ≠ 1) :
    clen A x < clen A (u * x) := by
  obtain ⟨l, hl, hnd, rfl⟩ := exists_nodup_cword A hT hu
  have hlen : l ≠ [] := by
    rintro rfl
    exact hu1 (cword_nil A)
  have hsum := clen_cword_mul A hT hx l hl hnd
  have hpos : 0 < l.length := List.length_pos_iff.2 hlen
  omega

/-- The right-handed form: if no generator of the simplex `T` shortens `x` from the right, then
every nontrivial `u ∈ W_T` lengthens `x` on the right. -/
theorem clen_lt_of_mem_specialSub {T : Set V} (hT : Commuting A T) {x : CayGroup A}
    (hx : ∀ s ∈ T, ¬ IsRDesc A x s) {u : CayGroup A} (hu : u ∈ specialSub A T) (hu1 : u ≠ 1) :
    clen A x < clen A (x * u) := by
  have hx' := fun s hs hcon =>
    hx s hs ((isRDesc_iff_isDesc A x s).2 hcon)
  have hu' := Subgroup.inv_mem _ hu
  have hu1' := inv_ne_one.2 hu1
  have h := clen_lt_of_mem_specialSub_left A hT hx' hu' hu1'
  have heq : clen A (u⁻¹ * x⁻¹) = clen A (x * u) := by
    rw [← clen_inv A (x * u), mul_inv_rev]
  rwa [heq, clen_inv A x] at h

/-! ### The chamber intersection formula -/

/-- If some element `y ≠ x` of the coset `x W_T` is not longer than `x`, then `T` meets the
descent set `D(x)`. -/
theorem exists_rdesc_of_earlier {T : Set V} (hT : Commuting A T) {x y : CayGroup A}
    (hy : x⁻¹ * y ∈ specialSub A T) (hne : y ≠ x) (hle : clen A y ≤ clen A x) :
    ∃ s ∈ T, IsRDesc A x s := by
  by_contra hcon
  push_neg at hcon
  have hu1 : x⁻¹ * y ≠ 1 := fun h => hne (inv_mul_eq_one.1 h).symm
  have hlt := clen_lt_of_mem_specialSub A hT hcon hy hu1
  rw [mul_inv_cancel_left] at hlt
  omega

/-- Conversely, a descent `s ∈ T ∩ D(x)` produces the strictly shorter element `x s` of the
coset `x W_T`. -/
theorem earlier_of_rdesc {T : Set V} {x : CayGroup A} {s : V} (hs : s ∈ T)
    (h : IsRDesc A x s) :
    x⁻¹ * (x * gen A s) ∈ specialSub A T ∧ x * gen A s ≠ x ∧
      clen A (x * gen A s) < clen A x := by
  have hlt : clen A (x * gen A s) < clen A x := h
  refine ⟨by simpa using gen_mem_specialSub A hs, ?_, hlt⟩
  grind

/-- **The chamber intersection formula.**  For a simplex `T` of `L`, the chamber `F_x` meets an
earlier chamber (one of length at most `ℓ(x)`, and different from `F_x`) in a point of mirror
type `T` exactly when `T` meets the descent set `D(x) = {s : ℓ(xs) < ℓ(x)}`. -/
theorem exists_rdesc_iff_exists_earlier {T : Set V} (hT : Commuting A T) (x : CayGroup A) :
    (∃ y : CayGroup A, x⁻¹ * y ∈ specialSub A T ∧ y ≠ x ∧ clen A y ≤ clen A x) ↔
      ∃ s ∈ T, IsRDesc A x s := by
  constructor
  · rintro ⟨y, hy, hne, hle⟩
    exact exists_rdesc_of_earlier A hT hy hne hle
  · rintro ⟨s, hs, hsd⟩
    obtain ⟨h1, h2, h3⟩ := earlier_of_rdesc A hs hsd
    exact ⟨x * gen A s, h1, h2, le_of_lt h3⟩

/-! ### The shortest element of a coset -/

/-- **`x` is the shortest element of `x W_T` exactly when `T ∩ D(x) = ∅`.** -/
theorem shortest_iff_no_rdesc {T : Set V} (hT : Commuting A T) (x : CayGroup A) :
    (∀ y : CayGroup A, x⁻¹ * y ∈ specialSub A T → clen A x ≤ clen A y) ↔
      ∀ s ∈ T, ¬ IsRDesc A x s := by
  constructor
  · intro h s hs hsd
    obtain ⟨h1, -, h3⟩ := earlier_of_rdesc A hs hsd
    exact absurd (h _ h1) (by omega)
  · intro h y hy
    by_cases hxy : y = x
    · simp [hxy]
    · have hu1 : x⁻¹ * y ≠ 1 := fun hc => hxy (inv_mul_eq_one.1 hc).symm
      have hlt := clen_lt_of_mem_specialSub A hT h hy hu1
      rw [mul_inv_cancel_left] at hlt
      omega

/-- Membership in the coset `x W_T` only depends on the coset. -/
theorem mem_coset_congr {T : Set V} {x y : CayGroup A} (hxy : x⁻¹ * y ∈ specialSub A T)
    (z : CayGroup A) : y⁻¹ * z ∈ specialSub A T ↔ x⁻¹ * z ∈ specialSub A T := by
  constructor
  · intro h
    have hz : x⁻¹ * z = (x⁻¹ * y) * (y⁻¹ * z) := by group
    rw [hz]
    exact Subgroup.mul_mem _ hxy h
  · intro h
    have hz : y⁻¹ * z = (x⁻¹ * y)⁻¹ * (x⁻¹ * z) := by group
    rw [hz]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hxy) h

/-- **Uniqueness of the shortest element of a coset.**  Every coset `x W_T` of the special
subgroup of a simplex contains exactly one element with no right descent in `T`. -/
theorem existsUnique_shortest_coset {T : Set V} (hT : Commuting A T) (x : CayGroup A) :
    ∃! y : CayGroup A, x⁻¹ * y ∈ specialSub A T ∧ ∀ s ∈ T, ¬ IsRDesc A y s := by
  classical
  have hne : ∃ n : ℕ, ∃ y : CayGroup A, x⁻¹ * y ∈ specialSub A T ∧ clen A y = n :=
    ⟨clen A x, x, by rw [inv_mul_cancel]; exact Subgroup.one_mem _, rfl⟩
  obtain ⟨y, hyc, hymin⟩ :
      ∃ y : CayGroup A, x⁻¹ * y ∈ specialSub A T ∧
        ∀ z : CayGroup A, x⁻¹ * z ∈ specialSub A T → clen A y ≤ clen A z := by
    obtain ⟨y, hy, hylen⟩ := Nat.find_spec hne
    refine ⟨y, hy, fun z hz => ?_⟩
    have hfind : Nat.find hne ≤ clen A z := Nat.find_le ⟨z, hz, rfl⟩
    omega
  have hyd  :=
    (shortest_iff_no_rdesc A hT y).1
      (fun z hz => hymin z ((mem_coset_congr A hyc z).1 hz))
  refine ⟨y, ⟨hyc, hyd⟩, ?_⟩
  rintro z ⟨hzc, hzd⟩
  have hyz  := (mem_coset_congr A hyc z).2 hzc
  have hzy : z⁻¹ * y ∈ specialSub A T := by
    have := Subgroup.inv_mem _ hyz
    rwa [mul_inv_rev, inv_inv] at this
  by_contra hne'
  have h1  := fun hc => hne' (inv_mul_eq_one.1 hc).symm
  have h2  := fun hc => hne' (inv_mul_eq_one.1 hc)
  have hlt1 := clen_lt_of_mem_specialSub A hT hyd hyz h1
  have hlt2 := clen_lt_of_mem_specialSub A hT hzd hzy h2
  rw [mul_inv_cancel_left] at hlt1 hlt2
  omega

end RACG
end FiniteChains

namespace FiniteChains
namespace Mirror

universe u

variable {V : Type u} [DecidableEq V]

/-! ### The descent set of an element of a right-angled Coxeter group -/

section RACG

open RACG

variable [Fintype V] (A : CommRel V)

/-- The descent set `D(x) = {s : ℓ(xs) < ℓ(x)}` as a finite set of generators. -/
def rdescFinset (x : CayGroup A) : Finset V := by
  classical
  exact Finset.univ.filter fun s => IsRDesc A x s

theorem mem_rdescFinset {x : CayGroup A} {s : V} :
    s ∈ rdescFinset A x ↔ IsRDesc A x s := by
  simp [rdescFinset]

/-- The simplices of `L`: the cliques of the commutation graph. -/
def IsSimplex (σ : Finset V) : Prop := ∀ s ∈ σ, ∀ r ∈ σ, s ≠ r → A.rel s r

omit [DecidableEq V] [Fintype V] in
theorem isSimplex_subset {σ τ : Finset V} (hστ : σ ⊆ τ) (hτ : IsSimplex A τ) :
    IsSimplex A σ := fun s hs r hr hsr => hτ s (hστ hs) r (hστ hr) hsr

/-- **The descent set is a simplex of `L`**, in the form needed by the chamber argument. -/
theorem isSimplex_rdescFinset (x : CayGroup A) : IsSimplex A (rdescFinset A x) := by grind [rdesc_rel, IsSimplex, rdescFinset]

/-- **The descent set is nonempty** for `x ≠ 1`. -/
theorem rdescFinset_nonempty {x : CayGroup A} (hx : x ≠ 1) : (rdescFinset A x).Nonempty := by
  obtain ⟨s, hs⟩ := exists_rdesc A hx
  exact ⟨s, (mem_rdescFinset A).2 hs⟩

end RACG

end Mirror
end FiniteChains

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains
namespace Comb

universe u

/-! ### The order complex of a preorder -/

section OrderComplex

variable (P : Type u) [Preorder P]

/-- Oriented edges of the order complex: comparable ordered pairs. -/
def OrdEdge : Type u := {p : P × P // p.1 ≤ p.2}

/-- Two-cells of the order complex: chains `a ≤ b ≤ c`. -/
def OrdTri : Type u := {t : P × P × P // t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2}

/-- The two-skeleton of the order complex of a preorder: vertices are elements, edges are
comparable pairs, and every chain `a ≤ b ≤ c` carries a triangle attached along
`[a,b][b,c][a,c]⁻¹`. -/
def orderCx : Complex2.{u} where
  V := P
  E := OrdEdge P
  F := OrdTri P
  src e := e.1.1
  tgt e := e.1.2
  base t := t.1.1
  att t :=
    [((⟨(t.1.1, t.1.2.1), t.2.1⟩ : OrdEdge P), true),
     ((⟨(t.1.2.1, t.1.2.2), t.2.2⟩ : OrdEdge P), true),
     ((⟨(t.1.1, t.1.2.2), le_trans t.2.1 t.2.2⟩ : OrdEdge P), false)]
  att_isLoop := fun _ => ⟨rfl, rfl, rfl, rfl⟩

variable {P}

/-- The edge `a → b` attached to `a ≤ b`. -/
def ordPos {a b : P} (h : a ≤ b) : (orderCx P).E × Bool := ((⟨(a, b), h⟩ : OrdEdge P), true)

/-- The edge `a ≤ b` traversed backwards, from `b` to `a`. -/
def ordNeg {a b : P} (h : a ≤ b) : (orderCx P).E × Bool := ((⟨(a, b), h⟩ : OrdEdge P), false)

@[simp] theorem revGerm_ordPos {a b : P} (h : a ≤ b) : revGerm (ordPos h) = ordNeg h := rfl

@[simp] theorem revGerm_ordNeg {a b : P} (h : a ≤ b) : revGerm (ordNeg h) = ordPos h := rfl

theorem isPath_ordPos {a b : P} (h : a ≤ b) :
    IsPath (orderCx P).src (orderCx P).tgt [ordPos h] a b := ⟨rfl, rfl⟩

theorem isPath_ordNeg {a b : P} (h : a ≤ b) :
    IsPath (orderCx P).src (orderCx P).tgt [ordNeg h] b a := ⟨rfl, rfl⟩

theorem isPath_nil' (a : P) :
    IsPath (orderCx P).src (orderCx P).tgt ([] : List ((orderCx P).E × Bool)) a a := rfl

/-- Backtrack cancellation for an edge traversed forwards and then backwards. -/
theorem htpy_ordPos_ordNeg {a b : P} (h : a ≤ b) :
    Htpy (orderCx P) a a [ordPos h, ordNeg h] [] := by
  have := htpy_append_revPath (isPath_single (ordPos h))
  simpa [revPath, revGerm, Bool.not, Bool.not_true, Bool.not_false, ordPos, ordNeg, germSrc, germTgt, orderCx] using this

/-- Backtrack cancellation for an edge traversed backwards and then forwards. -/
theorem htpy_ordNeg_ordPos {a b : P} (h : a ≤ b) :
    Htpy (orderCx P) b b [ordNeg h, ordPos h] [] := by
  have := htpy_append_revPath (isPath_single (ordNeg h))
  simpa [revPath, revGerm, Bool.not, Bool.not_true, Bool.not_false, ordPos, ordNeg, germSrc, germTgt, orderCx] using this

/-- **The triangular relation**: `[a,b][b,c] ≃ [a,c]` for a chain `a ≤ b ≤ c`. -/
theorem htpy_orderCx_tri {a b c : P} (hab : a ≤ b) (hbc : b ≤ c) :
    Htpy (orderCx P) a c [ordPos hab, ordPos hbc] [ordPos (hab.trans hbc)] := by
  have hac  := hab.trans hbc
  have hp : IsPath (orderCx P).src (orderCx P).tgt [ordPos hab, ordPos hbc] a c :=
    ⟨rfl, rfl, rfl⟩
  have hq : IsPath (orderCx P).src (orderCx P).tgt [] c c := rfl
  have h1  :=
    Htpy.append_congr hp hq (Htpy.refl _) (htpy_ordNeg_ordPos hac).symm
  have hfull : IsPath (orderCx P).src (orderCx P).tgt
      [ordPos hab, ordPos hbc, ordNeg hac, ordPos hac] a c := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have h2 : Htpy (orderCx P) a c [ordPos hab, ordPos hbc, ordNeg hac, ordPos hac]
      [ordPos hac] := by
    refine Htpy.of_step ⟨hfull, isPath_ordPos hac, Or.inr ?_⟩
    exact ⟨[], [ordPos hac], ⟨(a, b, c), hab, hbc⟩, rfl, rfl⟩
  simpa using h1.trans h2

end OrderComplex

/-! ### The explicit contraction of edge paths -/

section Contraction

variable {P : Type u} [Preorder P]

/-- The path `p_σ = [σ,ρσ]⁻¹[ρσ,d]` of the text: from `σ` down to `ρσ` and up to `d`. -/
def ordPth (d : P) (rho : P → P) (hle : ∀ x, rho x ≤ x) (htop : ∀ x, rho x ≤ d) (x : P) :
    List ((orderCx P).E × Bool) := [ordNeg (hle x), ordPos (htop x)]

theorem isPath_ordPth (d : P) (rho : P → P) (hle : ∀ x, rho x ≤ x) (htop : ∀ x, rho x ≤ d)
    (x : P) :
    IsPath (orderCx P).src (orderCx P).tgt (ordPth d rho hle htop x) x d := ⟨rfl, rfl, rfl⟩

/-- **The key identity** `[σ,τ] p_τ ≃ p_σ` for `σ ≤ τ`, obtained from the three triangular
relations for the chains `ρσ ≤ σ ≤ τ`, `ρσ ≤ ρτ ≤ τ` and `ρσ ≤ ρτ ≤ d`. -/
theorem htpy_ordPos_ordPth (d : P) (rho : P → P) (hle : ∀ x, rho x ≤ x)
    (htop : ∀ x, rho x ≤ d) (hmono : ∀ {x y : P}, x ≤ y → rho x ≤ rho y) {a b : P}
    (hab : a ≤ b) :
    Htpy (orderCx P) a d (ordPos hab :: ordPth d rho hle htop b) (ordPth d rho hle htop a) := by
  have hrs  := hmono hab
  have hrb  := hrs.trans (hle b)
  have pa2 : IsPath (orderCx P).src (orderCx P).tgt [ordNeg (hle a), ordPos hrs] a (rho b) :=
    ⟨rfl, rfl, rfl⟩
  have pb2 : IsPath (orderCx P).src (orderCx P).tgt
      [ordNeg (hle b), ordPos (htop b)] b d := ⟨rfl, rfl, rfl⟩
  have p3 : IsPath (orderCx P).src (orderCx P).tgt
      [ordPos hab, ordNeg (hle b), ordPos (htop b)] a d := ⟨rfl, rfl, rfl, rfl⟩
  -- Step 1: expand `[ρa,d]` as `[ρa,ρb][ρb,d]`.
  have s1  :=
    Htpy.append_congr (isPath_ordNeg (hle a)) (isPath_ordPos (htop a)) (Htpy.refl _)
      (htpy_orderCx_tri hrs (htop b)).symm
  -- Step 2: insert the backtrack `[ρb,b][ρb,b]⁻¹`.
  have s2  :=
    (htpy_ordPos_ordNeg (hle b)).symm.congr_append pa2
      (isPath_ordPos (htop b))
  -- Step 3: contract `[ρa,ρb][ρb,b]` to `[ρa,b]`.
  have s3  :=
    (htpy_orderCx_tri hrs (hle b)).congr_append (isPath_ordNeg (hle a)) pb2
  -- Step 4: expand `[ρa,b]` as `[ρa,a][a,b]`.
  have s4  :=
    (htpy_orderCx_tri (hle a) hab).symm.congr_append
      (isPath_ordNeg (hle a)) pb2
  -- Step 5: cancel the backtrack `[ρa,a]⁻¹[ρa,a]`.
  have s5  :=
    (htpy_ordNeg_ordPos (hle a)).congr_append (isPath_nil' a) p3
  have chain : Htpy (orderCx P) a d (ordPth d rho hle htop a)
      (ordPos hab :: ordPth d rho hle htop b) := by
    simp only [ordPth]
    simp only [List.nil_append, List.cons_append] at s1 s2 s3 s4 s5 ⊢
    exact ((((s1.trans s2).trans s3).trans s4).trans s5)
  exact chain.symm

/-- The reversed form of the key identity: `[σ,τ]⁻¹ p_σ ≃ p_τ`. -/
theorem htpy_ordNeg_ordPth (d : P) (rho : P → P) (hle : ∀ x, rho x ≤ x)
    (htop : ∀ x, rho x ≤ d) (hmono : ∀ {x y : P}, x ≤ y → rho x ≤ rho y) {a b : P}
    (hab : a ≤ b) :
    Htpy (orderCx P) b d (ordNeg hab :: ordPth d rho hle htop a) (ordPth d rho hle htop b) := by
  have h1  :=
    Htpy.append_congr (isPath_ordNeg hab) (isPath_ordPth d rho hle htop a) (Htpy.refl _)
      (htpy_ordPos_ordPth d rho hle htop hmono hab).symm
  have h2  :=
    (htpy_ordNeg_ordPos hab).congr_append (isPath_nil' b)
      (isPath_ordPth d rho hle htop b)
  simp at h1 h2 ⊢
  exact h1.trans h2

/-- **Every edge path is the standard one**: for a path `p` from `σ` to `τ` one has
`p · p_τ ≃ p_σ`; in particular every path `σ → τ` is homotopic to `p_σ p_τ⁻¹`. -/
theorem htpy_path_ordPth (d : P) (rho : P → P) (hle : ∀ x, rho x ≤ x)
    (htop : ∀ x, rho x ≤ d) (hmono : ∀ {x y : P}, x ≤ y → rho x ≤ rho y) :
    ∀ (p : List ((orderCx P).E × Bool)) {x y : P},
      IsPath (orderCx P).src (orderCx P).tgt p x y →
      Htpy (orderCx P) x d (p ++ ordPth d rho hle htop y) (ordPth d rho hle htop x) := by
  intro p
  induction p with
  | nil =>
      intro x y hp
      cases hp
      exact Htpy.refl _
  | cons eb p ih =>
      rintro x y ⟨hx, hrest⟩
      obtain ⟨⟨⟨a, b⟩, hab⟩, tag⟩ := eb
      cases tag with
      | false =>
          have hxb  := hx
          have hrest'  := hrest
          have hih := ih hrest'
          have h1  :=
            Htpy.append_congr (isPath_ordNeg hab)
              (isPath_append_iff.mpr ⟨y, hrest', isPath_ordPth d rho hle htop y⟩)
              (Htpy.refl _) hih
          have h2 := htpy_ordNeg_ordPth d rho hle htop hmono hab
          have hgoal : Htpy (orderCx P) b d ((ordNeg hab :: p) ++ ordPth d rho hle htop y)
              (ordPth d rho hle htop b) := by
            simp at h1 ⊢
            exact h1.trans h2
          rw [hxb]
          exact hgoal
      | true =>
          have hxa  := hx
          have hrest'  := hrest
          have hih := ih hrest'
          have h1  :=
            Htpy.append_congr (isPath_ordPos hab)
              (isPath_append_iff.mpr ⟨y, hrest', isPath_ordPth d rho hle htop y⟩)
              (Htpy.refl _) hih
          have h2 := htpy_ordPos_ordPth d rho hle htop hmono hab
          have hgoal : Htpy (orderCx P) a d ((ordPos hab :: p) ++ ordPth d rho hle htop y)
              (ordPth d rho hle htop a) := by
            simp at h1 ⊢
            exact h1.trans h2
          rw [hxa]
          exact hgoal

/-- **Simple connectivity of the order complex** of a preorder carrying an order map
`ρ ≤ id` with `ρ ≤ c_d`.  This is proved with edges and triangular relations alone; it is not
inferred from acyclicity of the chain complex. -/
theorem simplyConnected_orderCx (d : P) (rho : P → P) (hle : ∀ x, rho x ≤ x)
    (htop : ∀ x, rho x ≤ d) (hmono : ∀ {x y : P}, x ≤ y → rho x ≤ rho y) :
    SimplyConnected (orderCx P) := by
  intro a p hp
  have hq  :=
    isPath_ordPth d rho hle htop a
  set q := ordPth d rho hle htop a with hqdef
  have h := htpy_path_ordPth d rho hle htop hmono p hp
  have h3  := htpy_append_revPath hq
  have h1  :=
    Htpy.append_congr hp (isPath_append_iff.mpr ⟨d, hq, isPath_revPath hq⟩) (Htpy.refl _) h3
  have h2  :=
    Htpy.append_congr (isPath_append_iff.mpr ⟨a, hp, hq⟩) (isPath_revPath hq) h (Htpy.refl _)
  have h1' : Htpy (orderCx P) a a p ((p ++ q) ++ revPath q) := by
    simpa [List.append_assoc] using h1.symm
  exact (h1'.trans h2).trans h3

/-- The order complex of a preorder with such a contraction is connected. -/
theorem isConnected_orderCx (d : P) (rho : P → P) (hle : ∀ x, rho x ≤ x)
    (htop : ∀ x, rho x ≤ d) : IsConnected (orderCx P) := by
  intro a b
  exact ⟨ordPth d rho hle htop a ++ revPath (ordPth d rho hle htop b),
    isPath_append_iff.mpr ⟨d, isPath_ordPth d rho hle htop a,
      isPath_revPath (isPath_ordPth d rho hle htop b)⟩⟩

end Contraction

end Comb

/-! ### The attaching subcomplex of a chamber is simply connected -/


end FiniteChains
end

namespace FiniteChains
namespace Comb

universe u

/-! ### Functoriality of the order complex -/

section Map

variable {P Q : Type u} [Preorder P] [Preorder Q]

/-- A monotone map induces a cellular map of order complexes. -/
def orderCxMap (f : P → Q) (hf : Monotone f) : Hom (orderCx P) (orderCx Q) where
  onV := f
  onE e := (⟨(f e.1.1, f e.1.2), hf e.2⟩ : OrdEdge Q)
  onF t := (⟨(f t.1.1, f t.1.2.1, f t.1.2.2), hf t.2.1, hf t.2.2⟩ : OrdTri Q)
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF _ := rfl

@[simp] theorem orderCxMap_onV (f : P → Q) (hf : Monotone f) (p : P) :
    (orderCxMap f hf).onV p = f p := rfl

end Map

/-! ### Paths inside a subposet -/

section PathIn

variable {P : Type u} [Preorder P]

/-- Every edge of the path `l` has both endpoints in `A`. -/
def PathIn (A : P → Prop) (l : List ((orderCx P).E × Bool)) : Prop :=
  ∀ e ∈ l, A e.1.1.1 ∧ A e.1.1.2

theorem pathIn_nil (A : P → Prop) : PathIn A ([] : List ((orderCx P).E × Bool)) := by
  intro e he
  exact absurd he (by simp)

theorem pathIn_cons {A : P → Prop} {e : (orderCx P).E × Bool}
    {l : List ((orderCx P).E × Bool)} (he : A e.1.1.1 ∧ A e.1.1.2) (hl : PathIn A l) :
    PathIn A (e :: l) := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | h
  · exact he
  · exact hl x h

theorem pathIn_of_cons {A : P → Prop} {e : (orderCx P).E × Bool}
    {l : List ((orderCx P).E × Bool)} (h : PathIn A (e :: l)) :
    (A e.1.1.1 ∧ A e.1.1.2) ∧ PathIn A l :=
  ⟨h e (by simp), fun x hx => h x (by simp [hx])⟩

theorem pathIn_append {A : P → Prop} {l l' : List ((orderCx P).E × Bool)}
    (h : PathIn A l) (h' : PathIn A l') : PathIn A (l ++ l') := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact h x hx
  · exact h' x hx

theorem pathIn_of_append_left {A : P → Prop} {l l' : List ((orderCx P).E × Bool)}
    (h : PathIn A (l ++ l')) : PathIn A l := fun x hx => h x (by simp [hx])

theorem pathIn_of_append_right {A : P → Prop} {l l' : List ((orderCx P).E × Bool)}
    (h : PathIn A (l ++ l')) : PathIn A l' := fun x hx => h x (by simp [hx])

theorem pathIn_revPath {A : P → Prop} {l : List ((orderCx P).E × Bool)} (h : PathIn A l) :
    PathIn A (revPath l) := by
  intro x hx
  simp only [revPath, List.mem_reverse, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact h y hy

theorem pathIn_mono {A B : P → Prop} (hAB : ∀ p, A p → B p)
    {l : List ((orderCx P).E × Bool)} (h : PathIn A l) : PathIn B l :=
  fun x hx => ⟨hAB _ (h x hx).1, hAB _ (h x hx).2⟩

end PathIn

/-! ### Lifting a path to a subposet -/

section Lift

variable {P : Type u} [Preorder P] {A : P → Prop}

/-- The inclusion of a subposet. -/
theorem monotone_subtypeVal : Monotone (fun p : {p : P // A p} => (p : P)) :=
  fun _ _ h => h

/-- The cellular map induced by the inclusion of a subposet. -/
def subposetHom (A : P → Prop) : Hom (orderCx {p : P // A p}) (orderCx P) :=
  orderCxMap (fun p : {p : P // A p} => (p : P)) monotone_subtypeVal

/-- The lift of one oriented edge with endpoints in `A`. -/
def liftGermIn (e : (orderCx P).E × Bool) (h : A e.1.1.1 ∧ A e.1.1.2) :
    (orderCx {p : P // A p}).E × Bool :=
  ((⟨(⟨e.1.1.1, h.1⟩, ⟨e.1.1.2, h.2⟩), e.1.2⟩ : OrdEdge {p : P // A p}), e.2)

/-- The lift of a path all of whose edges have endpoints in `A`. -/
def liftPathIn : (l : List ((orderCx P).E × Bool)) → PathIn A l →
    List ((orderCx {p : P // A p}).E × Bool)
  | [], _ => []
  | e :: t, h => liftGermIn e (pathIn_of_cons h).1 :: liftPathIn t (pathIn_of_cons h).2

theorem mapPath_liftPathIn : ∀ (l : List ((orderCx P).E × Bool)) (h : PathIn A l),
    mapPath (subposetHom A) (liftPathIn l h) = l
  | [], _ => rfl
  | e :: t, h => by
      simp only [liftPathIn, mapPath, List.map_cons]
      rw [show (List.map (fun eb => ((subposetHom A).onE eb.1, eb.2)) (liftPathIn t
        (pathIn_of_cons h).2)) = t from mapPath_liftPathIn t (pathIn_of_cons h).2]
      rfl

theorem isPath_liftPathIn : ∀ (l : List ((orderCx P).E × Bool)) (h : PathIn A l) {u v : P}
    (hu : A u) (hv : A v), IsPath (orderCx P).src (orderCx P).tgt l u v →
    IsPath (orderCx {p : P // A p}).src (orderCx {p : P // A p}).tgt (liftPathIn l h)
      ⟨u, hu⟩ ⟨v, hv⟩
  | [], _, u, v, hu, hv, hp => by
      have : u = v := hp
      subst this
      rfl
  | e :: t, h, u, v, hu, hv, hp => by
      obtain ⟨hstart, hrest⟩ := hp
      obtain ⟨e, tag⟩ := e
      cases tag with
      | false =>
          refine ⟨Subtype.ext hstart, ?_⟩
          exact isPath_liftPathIn t (pathIn_of_cons h).2 ((pathIn_of_cons h).1).1 hv hrest
      | true =>
          refine ⟨Subtype.ext hstart, ?_⟩
          exact isPath_liftPathIn t (pathIn_of_cons h).2 ((pathIn_of_cons h).1).2 hv hrest

/-- **A loop inside a simply connected subposet is null-homotopic in the ambient complex.** -/
theorem htpy_nil_of_pathIn (hA : SimplyConnected (orderCx {p : P // A p}))
    {v : P} (hv : A v) {l : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt l v v) (hl : PathIn A l) :
    Htpy (orderCx P) v v l [] := by
  have hlift := isPath_liftPathIn l hl hv hv hp
  have hnull := hA ⟨v, hv⟩ (liftPathIn l hl) hlift
  have := mapPath_htpy (subposetHom A) hnull
  rw [mapPath_liftPathIn l hl] at this
  simpa [mapPath, subposetHom] using this

end Lift

/-! ### The gluing lemma -/

section VanKampen

variable {P : Type u} [Preorder P]

/-- Every loop of the ambient order complex all of whose edges lie in `A` is null-homotopic in
the ambient complex. -/
def NullIn (A : P → Prop) : Prop :=
  ∀ (v : P) (l : List ((orderCx P).E × Bool)), A v →
    IsPath (orderCx P).src (orderCx P).tgt l v v → PathIn A l → Htpy (orderCx P) v v l []

/-- Any two elements of `A` are joined by a path all of whose edges lie in `A`. -/
def ConnectedIn (A : P → Prop) : Prop :=
  ∀ u v : P, A u → A v → ∃ l, IsPath (orderCx P).src (orderCx P).tgt l u v ∧ PathIn A l

/-- A simply connected subposet gives `NullIn`. -/
theorem nullIn_of_simplyConnected {A : P → Prop}
    (hA : SimplyConnected (orderCx {p : P // A p})) : NullIn A :=
  fun _ _ hv hp hl => htpy_nil_of_pathIn hA hv hp hl

/-- The image of a path of the subposet complex lies in the subposet. -/
theorem pathIn_mapPath (A : P → Prop) (l : List ((orderCx {p : P // A p}).E × Bool)) :
    PathIn A (mapPath (subposetHom A) l) := by
  intro e he
  simp only [mapPath, List.mem_map] at he
  obtain ⟨x, _, rfl⟩ := he
  exact ⟨x.1.1.1.2, x.1.1.2.2⟩

/-- A connected subposet gives `ConnectedIn`. -/
theorem connectedIn_of_isConnected {A : P → Prop} (h : IsConnected (orderCx {p : P // A p})) :
    ConnectedIn A := by
  intro u v hu hv
  obtain ⟨l, hl⟩ := h ⟨u, hu⟩ ⟨v, hv⟩
  exact ⟨mapPath (subposetHom A) l, isPath_mapPath (subposetHom A) hl, pathIn_mapPath A l⟩

theorem pathIn_congr {A A' : P → Prop} (h : ∀ p, A p ↔ A' p)
    {l : List ((orderCx P).E × Bool)} (hl : PathIn A l) : PathIn A' l :=
  pathIn_mono (fun p hp => (h p).1 hp) hl

theorem nullIn_congr {A A' : P → Prop} (h : ∀ p, A p ↔ A' p) (hA : NullIn A) : NullIn A' :=
  fun v l hv hp hl => hA v l ((h v).2 hv) hp (pathIn_congr (fun p => (h p).symm) hl)

theorem connectedIn_congr {A A' : P → Prop} (h : ∀ p, A p ↔ A' p) (hA : ConnectedIn A) :
    ConnectedIn A' := by
  intro u v hu hv
  obtain ⟨l, hl, hlin⟩ := hA u v ((h u).2 hu) ((h v).2 hv)
  exact ⟨l, hl, pathIn_congr h hlin⟩

/-- **Cutting a path at its first return to the intersection.**  A path that starts on the `S`
side runs inside `S` until it first meets `S ∩ S'`. -/
theorem split_side {S S' U : P → Prop}
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (S a ∧ S b) ∨ (S' a ∧ S' b)) :
    ∀ (t : List ((orderCx P).E × Bool)) (w v : P),
      IsPath (orderCx P).src (orderCx P).tgt t w v → PathIn U t → (S v ∧ S' v) → S w →
      ∃ (t₁ t₂ : List ((orderCx P).E × Bool)) (z : P), t = t₁ ++ t₂ ∧
        IsPath (orderCx P).src (orderCx P).tgt t₁ w z ∧
        IsPath (orderCx P).src (orderCx P).tgt t₂ z v ∧ (S z ∧ S' z) ∧ PathIn S t₁ := by
  intro t
  induction t with
  | nil =>
      intro w v hp _ hv _
      have hwv  := hp
      subst hwv
      exact ⟨[], [], w, rfl, rfl, rfl, hv, pathIn_nil S⟩
  | cons e t ih =>
      intro w v hp hUl hv hw
      by_cases hJ : S w ∧ S' w
      · exact ⟨[], e :: t, w, rfl, rfl, hp, hJ, pathIn_nil S⟩
      · obtain ⟨hstart, hrest⟩ := hp
        obtain ⟨hUe, hUt⟩ := pathIn_of_cons hUl
        have hS'  := fun h => hJ ⟨hw, h⟩
        have hSe : S e.1.1.1 ∧ S e.1.1.2 := by
          rcases hmix e.1.1.1 e.1.1.2 e.1.2 hUe.1 hUe.2 with h | h
          · exact h
          · exfalso
            obtain ⟨ee, tag⟩ := e
            cases tag with
            | false =>
                exact hS' (by rw [hstart]; exact h.2)
            | true =>
                exact hS' (by rw [hstart]; exact h.1)
        have hSw : S (germTgt (orderCx P).src (orderCx P).tgt e) := by
          obtain ⟨ee, tag⟩ := e
          cases tag with
          | false => exact hSe.1
          | true => exact hSe.2
        obtain ⟨t₁, t₂, z, hteq, hp1, hp2, hz, hin1⟩ :=
          ih (germTgt (orderCx P).src (orderCx P).tgt e) v hrest hUt hv hSw
        exact ⟨e :: t₁, t₂, z, by simp [hteq], ⟨hstart, hp1⟩, hp2, hz, pathIn_cons hSe hin1⟩

/-- **The gluing lemma at the level of `π₁`.**  Let `U` be covered by two subposets `A` and `B`
such that no comparability inside `U` is mixed, let loops inside `A` and inside `B` be
null-homotopic in the ambient order complex, let `A`, `B` and their intersection `J = A ∩ B` be
connected and let `J` be nonempty.  Then every loop inside `U` is null-homotopic in the ambient
order complex.  This is the van Kampen step of the chamber induction, written so that its
conclusion is again a hypothesis of the same shape. -/
theorem htpy_nil_of_pathIn_union {A B U : P → Prop}
    (hU : ∀ p, U p ↔ (A p ∨ B p))
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    (hA : NullIn A) (hB : NullIn B)
    (hAconn : ConnectedIn A) (hBconn : ConnectedIn B)
    (hJconn : ConnectedIn (fun p => A p ∧ B p))
    {j : P} (hj : A j ∧ B j) :
    NullIn U := by
  have hex : ∀ u : P, ∃ g : List ((orderCx P).E × Bool),
      ((A u ∧ B u) → IsPath (orderCx P).src (orderCx P).tgt g j u ∧
        PathIn (fun p => A p ∧ B p) g) ∧ (u = j → g = []) := by
    intro u
    by_cases hu : u = j
    · subst hu
      exact ⟨[], fun _ => ⟨rfl, pathIn_nil _⟩, fun _ => rfl⟩
    · by_cases h : A u ∧ B u
      · obtain ⟨g, hg⟩ := hJconn j u hj h
        exact ⟨g, fun _ => hg, fun hc => absurd hc hu⟩
      · exact ⟨[], fun hc => absurd hc h, fun _ => rfl⟩
  choose γ hγ hγj using hex
  have key : ∀ n l (u v), l.length ≤ n →
      IsPath (orderCx P).src (orderCx P).tgt l u v → PathIn U l →
      (A u ∧ B u) → (A v ∧ B v) →
      Htpy (orderCx P) j j (γ u ++ l ++ revPath (γ v)) [] := by
    intro n
    induction n with
    | zero =>
        intro l u v hlen hp _ hu _
        have hl  := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hlen)
        subst hl
        have huv  := hp
        subst huv
        simpa using htpy_append_revPath (hγ u hu).1
    | succ n ih =>
        intro l u v hlen hp hUl hu hv
        cases l with
        | nil => grind
        | cons e t =>
            obtain ⟨hstart, hrest⟩ := hp
            obtain ⟨hUe, hUt⟩ := pathIn_of_cons hUl
            have side : ∀ S S' : P → Prop,
                (∀ a b : P, a ≤ b → U a → U b → (S a ∧ S b) ∨ (S' a ∧ S' b)) →
                NullIn S →
                (∀ p : P, S p ∧ S' p → A p ∧ B p) →
                (∀ p : P, A p ∧ B p → S p ∧ S' p) →
                (S e.1.1.1 ∧ S e.1.1.2) →
                Htpy (orderCx P) j j (γ u ++ (e :: t) ++ revPath (γ v)) [] := by
              intro S S' hmixS hNullS hJS hJS' hSe
              have hSw : S (germTgt (orderCx P).src (orderCx P).tgt e) := by
                obtain ⟨ee, tag⟩ := e
                cases tag with
                | false => exact hSe.1
                | true => exact hSe.2
              obtain ⟨t₁, t₂, z, hteq, hp1, hp2, hz, hin1⟩ :=
                split_side hmixS t _ v hrest hUt (hJS' v hv) hSw
              have hJz  := hJS z hz
              have hgu := (hγ u hu).1
              have hgv := (hγ v hv).1
              have hgz := (hγ z hJz).1
              have hSj  := hJS' j hj
              have hpath1 : IsPath (orderCx P).src (orderCx P).tgt (γ u ++ (e :: t₁)) j z :=
                isPath_append_iff.mpr ⟨u, hgu, ⟨hstart, hp1⟩⟩
              have hpathY :=
                isPath_append_iff.mpr ⟨v, hp2, isPath_revPath hgv⟩
              have hX : IsPath (orderCx P).src (orderCx P).tgt
                  ((γ u ++ (e :: t₁)) ++ revPath (γ z)) j j :=
                isPath_append_iff.mpr ⟨z, hpath1, isPath_revPath hgz⟩
              have hY : IsPath (orderCx P).src (orderCx P).tgt
                  (γ z ++ (t₂ ++ revPath (γ v))) j j :=
                isPath_append_iff.mpr ⟨z, hgz, hpathY⟩
              have hloop1 : Htpy (orderCx P) j j ((γ u ++ (e :: t₁)) ++ revPath (γ z)) [] := by
                refine hNullS j _ hSj.1 hX ?_
                refine pathIn_append (pathIn_append ?_ (pathIn_cons hSe hin1)) ?_
                · exact pathIn_mono (fun p h => (hJS' p h).1) (hγ u hu).2
                · exact pathIn_revPath (pathIn_mono (fun p h => (hJS' p h).1) (hγ z hJz).2)
              have hlen2 : t₂.length ≤ n := by
                have h1 : t₂.length ≤ t.length := by
                  rw [hteq]; simp
                simp only [List.length_cons] at hlen
                omega
              have hUt₂ : PathIn U t₂ := by
                have hUt' : PathIn U (t₁ ++ t₂) := by rw [← hteq]; exact hUt
                exact pathIn_of_append_right hUt'
              have hloop2 : Htpy (orderCx P) j j (γ z ++ (t₂ ++ revPath (γ v))) [] := by
                have h := ih t₂ z v hlen2 hp2 hUt₂ hJz hv
                simpa [List.append_assoc] using h
              have hcancel : Htpy (orderCx P) j j
                  ((γ u ++ (e :: t₁)) ++ [] ++ (t₂ ++ revPath (γ v)))
                  ((γ u ++ (e :: t₁)) ++ (revPath (γ z) ++ γ z) ++ (t₂ ++ revPath (γ v))) :=
                (htpy_revPath_append hgz).symm.congr_append hpath1 hpathY
              have hfinal : Htpy (orderCx P) j j
                  (((γ u ++ (e :: t₁)) ++ revPath (γ z)) ++ (γ z ++ (t₂ ++ revPath (γ v))))
                  ([] ++ []) := Htpy.append_congr hX hY hloop1 hloop2
              have hcomb : Htpy (orderCx P) j j
                  ((γ u ++ (e :: t₁)) ++ [] ++ (t₂ ++ revPath (γ v))) [] := by
                refine hcancel.trans ?_
                simpa [List.append_assoc] using hfinal
              simpa [hteq, List.append_assoc] using hcomb
            rcases hmix e.1.1.1 e.1.1.2 e.1.2 hUe.1 hUe.2 with hside | hside
            · exact side A B hmix hA (fun _ h => h) (fun _ h => h) hside
            · exact side B A (fun a b hab ha hb => (hmix a b hab ha hb).symm) hB
                (fun _ h => ⟨h.2, h.1⟩) (fun _ h => ⟨h.2, h.1⟩) hside
  intro v l hUv hp hUl
  cases l with
  | nil => exact Htpy.refl _
  | cons e t =>
      have hcase : ∀ S : P → Prop, NullIn S → ConnectedIn S → (∀ p, S p → U p) → S v → S j →
          Htpy (orderCx P) v v (e :: t) [] := by
        intro S hNullS hconnS hSU hSv hSj
        obtain ⟨d, hd, hdin⟩ := hconnS v j hSv hSj
        have hdU : PathIn U d := pathIn_mono hSU hdin
        have hq : IsPath (orderCx P).src (orderCx P).tgt
            (revPath d ++ ((e :: t) ++ d)) j j :=
          isPath_append_iff.mpr ⟨v, isPath_revPath hd,
            isPath_append_iff.mpr ⟨v, hp, hd⟩⟩
        have hqU : PathIn U (revPath d ++ ((e :: t) ++ d)) :=
          pathIn_append (pathIn_revPath hdU) (pathIn_append hUl hdU)
        have hkey := key (revPath d ++ ((e :: t) ++ d)).length _ j j le_rfl hq hqU hj hj
        rw [hγj j rfl] at hkey
        have hq0 : Htpy (orderCx P) j j (revPath d ++ ((e :: t) ++ d)) [] := by
          simpa [revPath] using hkey
        have e1 : Htpy (orderCx P) v v
            (d ++ (revPath d ++ ((e :: t) ++ d)) ++ revPath d) (d ++ [] ++ revPath d) :=
          hq0.congr_append hd (isPath_revPath hd)
        have e2 : Htpy (orderCx P) v v (d ++ [] ++ revPath d) [] := by
          simpa using htpy_append_revPath hd
        have hdd : IsPath (orderCx P).src (orderCx P).tgt (d ++ revPath d) v v :=
          isPath_append_iff.mpr ⟨j, hd, isPath_revPath hd⟩
        have f1 : Htpy (orderCx P) v v ((e :: t) ++ []) ((e :: t) ++ (d ++ revPath d)) :=
          Htpy.append_congr hp (isPath_nil' v) (Htpy.refl _) (htpy_append_revPath hd).symm
        have f2 : Htpy (orderCx P) v v ([] ++ ((e :: t) ++ (d ++ revPath d)))
            ((d ++ revPath d) ++ ((e :: t) ++ (d ++ revPath d))) :=
          Htpy.append_congr (isPath_nil' v)
            (isPath_append_iff.mpr ⟨v, hp, hdd⟩) (htpy_append_revPath hd).symm (Htpy.refl _)
        have e3 : Htpy (orderCx P) v v (e :: t)
            (d ++ (revPath d ++ ((e :: t) ++ d)) ++ revPath d) := by
          simpa [List.append_assoc] using f1.trans f2
        exact (e3.trans e1).trans e2
      rcases (hU v).1 hUv with hv | hv
      · grind
      · grind

/-- Under the hypotheses of the gluing lemma the union is connected. -/
theorem connectedIn_union {A B U : P → Prop} (hU : ∀ p, U p ↔ (A p ∨ B p))
    (hAconn : ConnectedIn A) (hBconn : ConnectedIn B) {j : P} (hj : A j ∧ B j) :
    ConnectedIn U := by
  have hAU  := fun p h => (hU p).2 (Or.inl h)
  have hBU  := fun p h => (hU p).2 (Or.inr h)
  have hside : ∀ u, U u → ∃ l, IsPath (orderCx P).src (orderCx P).tgt l u j ∧ PathIn U l := by
    intro u hu
    rcases (hU u).1 hu with h | h
    · obtain ⟨l, hl, hlin⟩ := hAconn u j h hj.1
      exact ⟨l, hl, pathIn_mono hAU hlin⟩
    · obtain ⟨l, hl, hlin⟩ := hBconn u j h hj.2
      exact ⟨l, hl, pathIn_mono hBU hlin⟩
  intro u v hu hv
  obtain ⟨l, hl, hlin⟩ := hside u hu
  obtain ⟨m, hm, hmin⟩ := hside v hv
  exact ⟨l ++ revPath m, isPath_append_iff.mpr ⟨j, hl, isPath_revPath hm⟩,
    pathIn_append hlin (pathIn_revPath hmin)⟩

end VanKampen

end Comb
end FiniteChains

namespace FiniteChains
namespace Davis

open RACG Mirror

universe u

variable {V : Type u} [DecidableEq V]

/-! ### The poset of spherical cosets -/

/-- **A spherical coset** of the right-angled Coxeter group: a simplex `T` of `L` together with
a coset of `W_T`, represented by its unique shortest element. -/
def Sph (A : CommRel V) : Type u :=
  {p : CayGroup A × Finset V // IsSimplex A p.2 ∧ ∀ s ∈ p.2, ¬ IsRDesc A p.1 s}

variable {A : CommRel V}

/-- The shortest element of the coset. -/
def Sph.rep (p : Sph A) : CayGroup A := p.1.1

/-- The simplex of `L` carried by the coset: its mirror type. -/
def Sph.spx (p : Sph A) : Finset V := p.1.2

theorem Sph.isSimplex (p : Sph A) : IsSimplex A p.spx := p.2.1

theorem Sph.no_rdesc (p : Sph A) : ∀ s ∈ p.spx, ¬ IsRDesc A p.rep s := p.2.2

theorem Sph.ext' {p q : Sph A} (hr : p.rep = q.rep) (hs : p.spx = q.spx) : p = q := by
  obtain ⟨⟨a, s⟩, hp⟩ := p
  obtain ⟨⟨b, t⟩, hq⟩ := q
  simp only [Sph.rep, Sph.spx] at hr hs
  subst hr
  subst hs
  rfl

omit [DecidableEq V] in
/-- A simplex of `L` is a commuting set of generators. -/
theorem commuting_of_isSimplex {σ : Finset V} (h : IsSimplex A σ) : Commuting A (σ : Set V) :=
  fun _ hs _ hr hne => h _ (Finset.mem_coe.1 hs) _ (Finset.mem_coe.1 hr) hne

theorem specialSub_mono {S T : Set V} (h : S ⊆ T) : specialSub A S ≤ specialSub A T :=
  Subgroup.closure_mono (Set.image_mono h)

/-- **The order of the Davis poset**: inclusion of cosets. -/
instance : PartialOrder (Sph A) where
  le p q := p.spx ⊆ q.spx ∧ p.rep⁻¹ * q.rep ∈ specialSub A (q.spx : Set V)
  le_refl p := ⟨Finset.Subset.refl _, by rw [inv_mul_cancel]; exact Subgroup.one_mem _⟩
  le_trans p q r hpq hqr := by
    refine ⟨hpq.1.trans hqr.1, ?_⟩
    have h1 : p.rep⁻¹ * q.rep ∈ specialSub A (r.spx : Set V) :=
      specialSub_mono (by exact_mod_cast hqr.1) hpq.2
    have h2 : p.rep⁻¹ * r.rep = (p.rep⁻¹ * q.rep) * (q.rep⁻¹ * r.rep) := by group
    rw [h2]
    exact Subgroup.mul_mem _ h1 hqr.2
  le_antisymm p q hpq hqp := by
    have hspx : p.spx = q.spx := Finset.Subset.antisymm hpq.1 hqp.1
    have hT : Commuting A (p.spx : Set V) := commuting_of_isSimplex p.isSimplex
    have huniq := existsUnique_shortest_coset A hT p.rep
    have hp : p.rep⁻¹ * p.rep ∈ specialSub A (p.spx : Set V) ∧
        ∀ s ∈ (p.spx : Set V), ¬ IsRDesc A p.rep s := by
      refine ⟨by rw [inv_mul_cancel]; exact Subgroup.one_mem _, ?_⟩
      intro s hs
      exact p.no_rdesc s (Finset.mem_coe.1 hs)
    have hq : p.rep⁻¹ * q.rep ∈ specialSub A (p.spx : Set V) ∧
        ∀ s ∈ (p.spx : Set V), ¬ IsRDesc A q.rep s := by
      refine ⟨by rw [hspx]; exact hpq.2, ?_⟩
      intro s hs
      exact q.no_rdesc s (hspx ▸ Finset.mem_coe.1 hs)
    have h1 := huniq.unique hp hq
    exact Sph.ext' h1 hspx

/-! ### Chambers -/

/-- The coset `p` contains the group element `x`: the corresponding cell of the Davis complex
lies in the chamber `F_x`. -/
def InChamber (x : CayGroup A) (p : Sph A) : Prop :=
  p.rep⁻¹ * x ∈ specialSub A (p.spx : Set V)

/-- **The chamber `F_x`** as a subposet of the Davis poset. -/
def Chamber (A : CommRel V) (x : CayGroup A) : Type u := {p : Sph A // InChamber x p}

instance (x : CayGroup A) : PartialOrder (Chamber A x) := Subtype.partialOrder _

@[simp] theorem Chamber.le_def {x : CayGroup A} (p q : Chamber A x) :
    p ≤ q ↔ p.1 ≤ q.1 := Iff.rfl

/-- Inside one chamber the order is just inclusion of simplices. -/
theorem le_of_inChamber {x : CayGroup A} {p q : Sph A} (hp : InChamber x p) (hq : InChamber x q)
    (h : p.spx ⊆ q.spx) : p ≤ q := by
  refine ⟨h, ?_⟩
  have h1  :=
    specialSub_mono (by exact_mod_cast h) hp
  have h2 : x⁻¹ * q.rep ∈ specialSub A q.spx := by
    have := Subgroup.inv_mem _ hq
    rwa [mul_inv_rev, inv_inv] at this
  have h3 : p.rep⁻¹ * q.rep = (p.rep⁻¹ * x) * (x⁻¹ * q.rep) := by group
  rw [h3]
  exact Subgroup.mul_mem _ h1 h2

/-- The unique cell of the chamber `F_x` with a given mirror type. -/
def chamberPt (x : CayGroup A) {σ : Finset V} (hσ : IsSimplex A σ) : Sph A :=
  ⟨((existsUnique_shortest_coset A (commuting_of_isSimplex hσ) x).choose, σ),
    hσ, fun s hs => (existsUnique_shortest_coset A (commuting_of_isSimplex hσ) x).choose_spec.1.2
      s (Finset.mem_coe.2 hs)⟩

@[simp] theorem chamberPt_spx (x : CayGroup A) {σ : Finset V} (hσ : IsSimplex A σ) :
    (chamberPt x hσ).spx = σ := rfl

theorem chamberPt_inChamber (x : CayGroup A) {σ : Finset V} (hσ : IsSimplex A σ) :
    InChamber x (chamberPt x hσ) := by
  have h := (existsUnique_shortest_coset A (commuting_of_isSimplex hσ) x).choose_spec.1.1
  have := Subgroup.inv_mem _ h
  rw [mul_inv_rev, inv_inv] at this
  exact this


/-! ### The chamber is a cone -/

omit [DecidableEq V] in
theorem isSimplex_empty : IsSimplex A (∅ : Finset V) := by
  intro s hs
  exact absurd hs (by simp)

/-- The apex of the chamber `F_x`: the cell `x W_∅ = {x}`. -/
def chamberApex (x : CayGroup A) : Chamber A x :=
  ⟨chamberPt x (isSimplex_empty (A := A)), chamberPt_inChamber x _⟩

theorem chamberApex_le {x : CayGroup A} (p : Chamber A x) : chamberApex x ≤ p :=
  le_of_inChamber (chamberApex x).2 p.2 (Finset.empty_subset _)

/-- **The chamber is simply connected**: its order complex is a cone on the apex. -/
theorem chamber_simplyConnected (x : CayGroup A) :
    Comb.SimplyConnected (Comb.orderCx (Chamber A x)) :=
  Comb.simplyConnected_orderCx (chamberApex x) (fun _ => chamberApex x)
    (fun p => chamberApex_le p) (fun _ => le_refl _) (fun _ => le_refl _)

/-- The chamber is connected. -/
theorem chamber_isConnected (x : CayGroup A) :
    Comb.IsConnected (Comb.orderCx (Chamber A x)) :=
  Comb.isConnected_orderCx (chamberApex x) (fun _ => chamberApex x)
    (fun p => chamberApex_le p) (fun _ => le_refl _)

/-- **The chamber is acyclic in all degrees**: every increasing cycle of its simplicial chain
complex, in every degree including the augmentation degree, is a boundary. -/
theorem chamber_exists_bdry_eq_of_cycle (x : CayGroup A) {c : Nerve.Ch (Chamber A x)}
    (hc : c ∈ Nerve.Inc (Chamber A x)) (hcyc : Nerve.bdry c = 0) :
    ∃ y ∈ Nerve.Inc (Chamber A x), Nerve.bdry y = c :=
  Nerve.exists_bdry_eq_of_cycle (fun _ => chamberApex x) (chamberApex x)
    (fun _ _ _ => le_refl _) (fun p => chamberApex_le p) (fun _ => le_refl _) hc hcyc

/-! ### The intersection with the earlier chambers -/

section Inter

variable [Fintype V]

/-- **The chamber intersection formula for the actual subcomplexes.**  A cell of the chamber
`F_x` lies in some strictly earlier chamber (`y ≠ x`, `ℓ(y) ≤ ℓ(x)`) exactly when its mirror
type meets the descent set `D(x)`; that is,
`F_x ∩ ⋃_{earlier} F_y = ⋃_{s ∈ D(x)} (F_s)_x`. -/
theorem mem_earlier_chamber_iff {x : CayGroup A} {p : Sph A} (hp : InChamber x p) :
    (∃ y : CayGroup A, y ≠ x ∧ RACG.clen A y ≤ RACG.clen A x ∧ InChamber y p) ↔
      (p.spx ∩ rdescFinset A x).Nonempty := by
  have hT  := commuting_of_isSimplex p.isSimplex
  have hkey := exists_rdesc_iff_exists_earlier A hT x
  constructor
  · rintro ⟨y, hne, hlen, hy⟩
    have hxy : x⁻¹ * y ∈ specialSub A p.spx := by
      have h1 : x⁻¹ * p.rep ∈ specialSub A p.spx := by
        have := Subgroup.inv_mem _ hp
        rwa [mul_inv_rev, inv_inv] at this
      have h2 : x⁻¹ * y = (x⁻¹ * p.rep) * (p.rep⁻¹ * y) := by group
      rw [h2]
      exact Subgroup.mul_mem _ h1 hy
    obtain ⟨s, hs, hsd⟩ := hkey.1 ⟨y, hxy, hne, hlen⟩
    exact ⟨s, Finset.mem_inter.2 ⟨Finset.mem_coe.1 hs, (mem_rdescFinset A).2 hsd⟩⟩
  · rintro ⟨s, hs⟩
    obtain ⟨hsσ, hsd⟩ := Finset.mem_inter.1 hs
    obtain ⟨y, hxy, hne, hlen⟩ := hkey.2 ⟨s, Finset.mem_coe.2 hsσ, (mem_rdescFinset A).1 hsd⟩
    refine ⟨y, hne, hlen, ?_⟩
    have h1 : p.rep⁻¹ * y = (p.rep⁻¹ * x) * (x⁻¹ * y) := by group
    rw [InChamber, h1]
    exact Subgroup.mul_mem _ hp hxy

/-- **The attaching subcomplex of the chamber `F_x`**: the part of `F_x` contained in the union
of the earlier chambers, by `FiniteChains.Davis.mem_earlier_chamber_iff`. -/
def ChamberInter (A : CommRel V) (x : CayGroup A) : Type u :=
  {p : Sph A // InChamber x p ∧ (p.spx ∩ rdescFinset A x).Nonempty}

instance (x : CayGroup A) : PartialOrder (ChamberInter A x) := Subtype.partialOrder _

variable {x : CayGroup A}

/-- The descent set itself is a cell of the attaching subcomplex: the top vertex `D(x)`. -/
def interTop (hx : x ≠ 1) : ChamberInter A x :=
  ⟨chamberPt x (isSimplex_rdescFinset A x), chamberPt_inChamber x _, by
    simp only [chamberPt_spx, Finset.inter_self]
    exact rdescFinset_nonempty A hx⟩

theorem interTop_spx (hx : x ≠ 1) : (interTop hx).1.spx = rdescFinset A x := rfl

/-- The contraction `ρ(σ) = σ ∩ D(x)` of the text, inside the model. -/
def interRho (p : ChamberInter A x) : ChamberInter A x :=
  let hsubset : p.1.spx ∩ rdescFinset A x ⊆ p.1.spx := Finset.inter_subset_left
  let hsimplex := isSimplex_subset A hsubset p.1.isSimplex
  ⟨chamberPt x hsimplex,
    chamberPt_inChamber x hsimplex, by
      have hspx : (chamberPt x hsimplex).spx = p.1.spx ∩ rdescFinset A x :=
        chamberPt_spx x hsimplex
      rw [hspx]
      rw [Finset.inter_assoc, Finset.inter_self]
      exact p.2.2⟩

theorem interRho_spx (p : ChamberInter A x) :
    (interRho p).1.spx = p.1.spx ∩ rdescFinset A x := rfl

theorem interRho_le (p : ChamberInter A x) : interRho p ≤ p := by
  refine le_of_inChamber (interRho p).2.1 p.2.1 ?_
  rw [interRho_spx]
  exact Finset.inter_subset_left

theorem interRho_le_top (hx : x ≠ 1) (p : ChamberInter A x) : interRho p ≤ interTop hx := by
  refine le_of_inChamber (interRho p).2.1 (interTop hx).2.1 ?_
  rw [interRho_spx, interTop_spx]
  exact Finset.inter_subset_right

theorem interRho_mono {p q : ChamberInter A x} (h : p ≤ q) : interRho p ≤ interRho q := by
  have h1  := h.1
  refine le_of_inChamber (interRho p).2.1 (interRho q).2.1 ?_
  rw [interRho_spx, interRho_spx]
  grind

/-- **The attaching subcomplex of a chamber is simply connected**, proved inside the model by
the path contraction of `RequestProject/MirrorSimplyConnected.lean`. -/
theorem chamberInter_simplyConnected (hx : x ≠ 1) :
    Comb.SimplyConnected (Comb.orderCx (ChamberInter A x)) :=
  Comb.simplyConnected_orderCx (interTop hx) interRho interRho_le (interRho_le_top hx)
    (fun h => interRho_mono h)

/-- The attaching subcomplex is connected. -/
theorem chamberInter_isConnected (hx : x ≠ 1) :
    Comb.IsConnected (Comb.orderCx (ChamberInter A x)) :=
  Comb.isConnected_orderCx (interTop hx) interRho interRho_le (interRho_le_top hx)

/-- **The attaching subcomplex is acyclic in all degrees.** -/
theorem chamberInter_exists_bdry_eq_of_cycle (hx : x ≠ 1)
    {c : Nerve.Ch (ChamberInter A x)} (hc : c ∈ Nerve.Inc (ChamberInter A x))
    (hcyc : Nerve.bdry c = 0) :
    ∃ y ∈ Nerve.Inc (ChamberInter A x), Nerve.bdry y = c :=
  Nerve.exists_bdry_eq_of_cycle interRho (interTop hx) (fun _ _ h => interRho_mono h)
    interRho_le (interRho_le_top hx) hc hcyc

end Inter

end Davis
end FiniteChains

namespace FiniteChains
namespace Davis

open RACG Mirror Comb

universe u

variable {V : Type u} [DecidableEq V] {A : CommRel V}

/-- **Chambers are upward closed**: a cell above a cell of `F_x` lies in `F_x`. -/
theorem inChamber_of_le {x : CayGroup A} {p q : Sph A} (hpq : p ≤ q) (hp : InChamber x p) :
    InChamber x q := by
  have h1  :=
    specialSub_mono (by exact_mod_cast hpq.1) hp
  have h2 : q.rep⁻¹ * x = (p.rep⁻¹ * q.rep)⁻¹ * (p.rep⁻¹ * x) := by group
  rw [InChamber, h2]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hpq.2) h1

/-- Every loop of the Davis complex inside one chamber is null-homotopic there. -/
theorem nullIn_chamber (x : CayGroup A) : NullIn (InChamber (A := A) x) :=
  nullIn_of_simplyConnected (chamber_simplyConnected x)

/-- A chamber is connected. -/
theorem connectedIn_chamber (x : CayGroup A) : ConnectedIn (InChamber (A := A) x) :=
  connectedIn_of_isConnected (chamber_isConnected x)

section Inter

variable [Fintype V]

/-- The attaching subcomplex of a chamber is connected. -/
theorem connectedIn_chamberInter {x : CayGroup A} (hx : x ≠ 1) :
    ConnectedIn (fun p : Sph A => InChamber x p ∧ (p.spx ∩ rdescFinset A x).Nonempty) :=
  connectedIn_of_isConnected (chamberInter_isConnected hx)

/-- **The inductive step of the chamber argument.**  If the union `Prev` of the earlier chambers
is upward closed, kills its loops and is connected, and if its intersection with the chamber
`F_x` is the union of the descending mirrors — which is the content of
`FiniteChains.Davis.mem_earlier_chamber_iff` — then `Prev ∪ F_x` again kills its loops and is
connected. -/
theorem nullIn_union_chamber {x : CayGroup A} (hx : x ≠ 1) (Prev : Sph A → Prop)
    (hup : ∀ p q : Sph A, p ≤ q → Prev p → Prev q)
    (hPrevNull : NullIn Prev) (hPrevConn : ConnectedIn Prev)
    (hinter : ∀ p : Sph A, (Prev p ∧ InChamber x p) ↔
      (InChamber x p ∧ (p.spx ∩ rdescFinset A x).Nonempty)) :
    NullIn (fun p => Prev p ∨ InChamber x p) ∧
      ConnectedIn (fun p => Prev p ∨ InChamber x p) := by
  have hjmem  := (interTop hx).2
  have hj  := (hinter _).2 hjmem
  have hJconn  :=
    connectedIn_congr (fun p => (hinter p).symm) (connectedIn_chamberInter hx)
  have hmix : ∀ a b : Sph A, a ≤ b → (Prev a ∨ InChamber x a) → (Prev b ∨ InChamber x b) →
      ((Prev a ∧ Prev b) ∨ (InChamber x a ∧ InChamber x b)) := by
    intro a b hab ha _
    rcases ha with h | h
    · grind
    · exact Or.inr ⟨h, inChamber_of_le hab h⟩
  exact ⟨htpy_nil_of_pathIn_union (fun _ => Iff.rfl) hmix hPrevNull (nullIn_chamber x)
      hPrevConn (connectedIn_chamber x) hJconn hj,
    connectedIn_union (fun _ => Iff.rfl) hPrevConn (connectedIn_chamber x) hj⟩

end Inter

end Davis
end FiniteChains

namespace FiniteChains
namespace Davis

open RACG Mirror Comb

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

/-! ### The sharp intersection formula -/

omit [Fintype V] in
/-- Every coset contains its own representative, so every cell lies in a chamber. -/
theorem inChamber_rep (p : Sph A) : InChamber p.rep p := by
  rw [InChamber, inv_mul_cancel]
  exact Subgroup.one_mem _

/-- **The intersection formula with strict length.**  A cell of `F_x` lies in a strictly shorter
chamber exactly when its mirror type meets `D(x)`. -/
theorem mem_shorter_chamber_iff {x : CayGroup A} {p : Sph A} (hp : InChamber x p) :
    (∃ y : CayGroup A, RACG.clen A y < RACG.clen A x ∧ InChamber y p) ↔
      (p.spx ∩ rdescFinset A x).Nonempty := by
  constructor
  · rintro ⟨y, hlt, hy⟩
    refine (mem_earlier_chamber_iff hp).1 ⟨y, ?_, le_of_lt hlt, hy⟩
    intro hxy
    rw [hxy] at hlt
    omega
  · rintro ⟨s, hs⟩
    obtain ⟨hsσ, hsd⟩ := Finset.mem_inter.1 hs
    obtain ⟨h1, -, h3⟩ := earlier_of_rdesc A (Finset.mem_coe.2 hsσ)
      ((mem_rdescFinset A).1 hsd)
    refine ⟨x * gen A s, h3, ?_⟩
    have h2 : p.rep⁻¹ * (x * gen A s) = (p.rep⁻¹ * x) * (x⁻¹ * (x * gen A s)) := by group
    rw [InChamber, h2]
    exact Subgroup.mul_mem _ hp h1

/-! ### The filtration by length -/

/-- The union of the chambers `F_y` with `ℓ(y) ≤ n`. -/
def Upto (n : ℕ) (p : Sph A) : Prop := ∃ y : CayGroup A, RACG.clen A y ≤ n ∧ InChamber y p

omit [Fintype V] in
theorem upto_up {n : ℕ} {p q : Sph A} (hpq : p ≤ q) (hp : Upto n p) : Upto n q := by
  obtain ⟨y, hy, hyp⟩ := hp
  exact ⟨y, hy, inChamber_of_le hpq hyp⟩

omit [Fintype V] in
theorem upto_zero_iff (p : Sph A) : Upto 0 p ↔ InChamber 1 p := by simp_all [RACG.clen_eq_zero_iff, Upto]

/-- The ball of radius `n` in the word metric is finite. -/
theorem ball_finite (A : CommRel V) (n : ℕ) : {x : CayGroup A | RACG.clen A x ≤ n}.Finite := by
  refine Set.Finite.subset ((List.finite_length_le V n).image (cword A)) ?_
  intro x hx
  obtain ⟨l, hl, hlx⟩ := exists_cword A x
  refine ⟨l, ?_, hlx⟩
  have : l.length = RACG.clen A x := by rw [← hlx, clen_cword A hl]
  simp only [Set.mem_setOf_eq, this]
  exact hx

/-- The elements of length exactly `n` form a finite set. -/
theorem level_finite (A : CommRel V) (n : ℕ) : {x : CayGroup A | RACG.clen A x = n}.Finite :=
  (ball_finite A n).subset (fun _ hx => le_of_eq hx)

/-! ### Adding the chambers of one length level -/

/-- Adding, one at a time, finitely many chambers of length `n + 1` to the union of the chambers
of length at most `n`. -/
theorem nullIn_upto_insert (n : ℕ) (hnull : NullIn (Upto (A := A) n))
    (hconn : ConnectedIn (Upto (A := A) n)) :
    ∀ (S : Set (CayGroup A)), S.Finite → (∀ y ∈ S, RACG.clen A y = n + 1) →
      NullIn (fun p : Sph A => Upto n p ∨ ∃ y ∈ S, InChamber y p) ∧
        ConnectedIn (fun p : Sph A => Upto n p ∨ ∃ y ∈ S, InChamber y p) := by
  intro S hS
  induction S, hS using Set.Finite.induction_on with
  | empty => simp_all
  | @insert x S hxS hSfin ih =>
      intro hlen
      obtain ⟨hprevNull, hprevConn⟩ := ih (fun y hy => hlen y (Set.mem_insert_of_mem _ hy))
      have hxlen  := hlen x (Set.mem_insert _ _)
      have hx1 : x ≠ 1 := by
        intro h
        rw [h] at hxlen
        simp at hxlen
      set Prev : Sph A → Prop := fun p => Upto n p ∨ ∃ y ∈ S, InChamber y p with hPrev
      have hup : ∀ p q : Sph A, p ≤ q → Prev p → Prev q := by
        rintro p q hpq (h | ⟨y, hy, hyp⟩)
        · exact Or.inl (upto_up hpq h)
        · exact Or.inr ⟨y, hy, inChamber_of_le hpq hyp⟩
      have hinter : ∀ p : Sph A, (Prev p ∧ InChamber x p) ↔
          (InChamber x p ∧ (p.spx ∩ rdescFinset A x).Nonempty) := by
        intro p
        constructor
        · rintro ⟨hprev, hpx⟩
          refine ⟨hpx, ?_⟩
          rcases hprev with ⟨y, hy, hyp⟩ | ⟨y, hyS, hyp⟩
          · exact (mem_shorter_chamber_iff hpx).1 ⟨y, by omega, hyp⟩
          · refine (mem_earlier_chamber_iff hpx).1 ⟨y, ?_, ?_, hyp⟩
            · intro hxy
              exact hxS (hxy ▸ hyS)
            · rw [hlen y (Set.mem_insert_of_mem _ hyS), hxlen]
        · rintro ⟨hpx, hne⟩
          obtain ⟨y, hylt, hyp⟩ := (mem_shorter_chamber_iff hpx).2 hne
          refine ⟨Or.inl ⟨y, ?_, hyp⟩, hpx⟩
          omega
      obtain ⟨hN, hC⟩ := nullIn_union_chamber hx1 Prev hup hprevNull hprevConn hinter
      have hiff : ∀ p : Sph A, (Prev p ∨ InChamber x p) ↔
          (Upto n p ∨ ∃ y ∈ insert x S, InChamber y p) := by
        intro p
        constructor
        · grind
        · grind
      exact ⟨nullIn_congr hiff hN, connectedIn_congr hiff hC⟩

/-- **Every loop inside the first `n` length levels of chambers is null-homotopic, and these
unions are connected.** -/
theorem nullIn_upto (A : CommRel V) : ∀ n : ℕ,
    NullIn (Upto (A := A) n) ∧ ConnectedIn (Upto (A := A) n) := by
  intro n
  induction n with
  | zero =>
      constructor
      · exact nullIn_congr (fun p => (upto_zero_iff p).symm) (nullIn_chamber 1)
      · exact connectedIn_congr (fun p => (upto_zero_iff p).symm) (connectedIn_chamber 1)
  | succ n ih =>
      obtain ⟨hN, hC⟩ :=
        nullIn_upto_insert n ih.1 ih.2 {x : CayGroup A | RACG.clen A x = n + 1} (level_finite A (n + 1))
          (fun _ hy => hy)
      have hiff : ∀ p : Sph A,
          (Upto n p ∨ ∃ y ∈ {x : CayGroup A | RACG.clen A x = n + 1}, InChamber y p) ↔ Upto (n + 1) p := by
        intro p
        constructor
        · rintro (⟨y, hy, hyp⟩ | ⟨y, hy, hyp⟩)
          · exact ⟨y, by omega, hyp⟩
          · exact ⟨y, le_of_eq hy, hyp⟩
        · rintro ⟨y, hy, hyp⟩
          rcases Nat.lt_or_ge (RACG.clen A y) (n + 1) with h | h
          · exact Or.inl ⟨y, by omega, hyp⟩
          · exact Or.inr ⟨y, le_antisymm hy h, hyp⟩
      exact ⟨nullIn_congr hiff hN, connectedIn_congr hiff hC⟩

/-! ### Simple connectivity of the whole complex -/

/-- A bound on the lengths of the representatives occurring along an edge path. -/
def pathBound (l : List ((orderCx (Sph A)).E × Bool)) : ℕ :=
  (l.map (fun e => RACG.clen A (e.1.1.1).rep + RACG.clen A (e.1.1.2).rep)).sum

omit [Fintype V] in
theorem pathIn_upto_pathBound (l : List ((orderCx (Sph A)).E × Bool)) :
    PathIn (Upto (A := A) (pathBound l)) l := by
  intro e he
  have hmem : RACG.clen A (e.1.1.1).rep + RACG.clen A (e.1.1.2).rep ∈
      l.map (fun e => RACG.clen A (e.1.1.1).rep + RACG.clen A (e.1.1.2).rep) := List.mem_map_of_mem he
  have hle : RACG.clen A (e.1.1.1).rep + RACG.clen A (e.1.1.2).rep ≤ pathBound l :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ hmem
  exact ⟨⟨(e.1.1.1).rep, by omega, inChamber_rep _⟩,
    ⟨(e.1.1.2).rep, by omega, inChamber_rep _⟩⟩

/-- **The Davis complex is simply connected.** -/
theorem simplyConnected_davis (A : CommRel V) : SimplyConnected (orderCx (Sph A)) := by
  intro v l hp
  cases l with
  | nil => exact Htpy.refl _
  | cons e t =>
      have hin := pathIn_upto_pathBound (e :: t)
      have hv : Upto (pathBound (e :: t)) v := by
        obtain ⟨hstart, -⟩ := hp
        obtain ⟨he, -⟩ := pathIn_of_cons hin
        obtain ⟨ee, tag⟩ := e
        cases tag with
        | false => rw [hstart]; exact he.2
        | true => rw [hstart]; exact he.1
      exact (nullIn_upto A (pathBound (e :: t))).1 v (e :: t) hv hp hin

/-- The Davis complex is connected. -/
theorem isConnected_davis (A : CommRel V) : IsConnected (orderCx (Sph A)) := by
  intro p q
  obtain ⟨l, hl, -⟩ :=
    (nullIn_upto A (RACG.clen A p.rep + RACG.clen A q.rep)).2 p q
      ⟨p.rep, by omega, inChamber_rep _⟩ ⟨q.rep, by omega, inChamber_rep _⟩
  exact ⟨l, hl⟩

end Davis
end FiniteChains

namespace FiniteChains
namespace Davis

open RACG Mirror Comb Nerve

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

/-! ### Local acyclicity, supported on the subposets -/

omit [Fintype V] in
/-- **The chamber `F_x` is acyclic**, as a subgroup of chains of the ambient complex. -/
theorem acyclicIn_chamber (x : CayGroup A) : AcyclicIn (InChamber (A := A) x) := by
  refine Nerve.acyclicIn_of_subtype _ ⟨(chamberApex x).1, (chamberApex x).2⟩ ?_
  intro c hc hcyc
  exact chamber_exists_bdry_eq_of_cycle x hc hcyc

/-- **The attaching subcomplex of the chamber `F_x` is acyclic**, as a subgroup of chains of the
ambient complex. -/
theorem acyclicIn_chamberInter {x : CayGroup A} (hx : x ≠ 1) :
    AcyclicIn (fun p : Sph A => InChamber x p ∧ (p.spx ∩ rdescFinset A x).Nonempty) := by
  refine Nerve.acyclicIn_of_subtype _ ⟨(interTop hx).1, (interTop hx).2⟩ ?_
  intro c hc hcyc
  exact chamberInter_exists_bdry_eq_of_cycle hx hc hcyc

/-! ### Adding one chamber -/

/-- **The gluing step for chains.**  Adding one chamber to an upward closed acyclic union whose
intersection with the chamber is the attaching subcomplex keeps the union acyclic. -/
theorem acyclicIn_union_chamber {x : CayGroup A} (hx : x ≠ 1) (Prev : Sph A → Prop)
    (hup : ∀ p q : Sph A, p ≤ q → Prev p → Prev q)
    (hPrev : AcyclicIn Prev)
    (hinter : ∀ p : Sph A, (Prev p ∧ InChamber x p) ↔
      (InChamber x p ∧ (p.spx ∩ rdescFinset A x).Nonempty)) :
    AcyclicIn (fun p : Sph A => Prev p ∨ InChamber x p) := by
  refine Nerve.acyclicIn_union_of_unmixed (A := Prev) (B := InChamber (A := A) x)
    (fun _ => Iff.rfl) ?_ hPrev (acyclicIn_chamber x)
    (Nerve.acyclicIn_congr (fun p => (hinter p).symm) (acyclicIn_chamberInter hx))
  rintro a b hab (ha | ha) hb
  · grind
  · exact Or.inr ⟨ha, inChamber_of_le hab ha⟩

/-- Adding, one at a time, finitely many chambers of length `n + 1`. -/
theorem acyclicIn_upto_insert (n : ℕ) (hprev : AcyclicIn (Upto (A := A) n)) :
    ∀ (S : Set (CayGroup A)), S.Finite → (∀ y ∈ S, RACG.clen A y = n + 1) →
      AcyclicIn (fun p : Sph A => Upto n p ∨ ∃ y ∈ S, InChamber y p) := by
  intro S hS
  induction S, hS using Set.Finite.induction_on with
  | empty => simp_all
  | @insert x S hxS hSfin ih =>
      intro hlen
      have hPrevAcyc := ih (fun y hy => hlen y (Set.mem_insert_of_mem _ hy))
      have hxlen  := hlen x (Set.mem_insert _ _)
      have hx1 : x ≠ 1 := by
        intro h
        rw [h] at hxlen
        simp at hxlen
      set Prev : Sph A → Prop := fun p => Upto n p ∨ ∃ y ∈ S, InChamber y p with hPrev
      have hup : ∀ p q : Sph A, p ≤ q → Prev p → Prev q := by
        rintro p q hpq (h | ⟨y, hy, hyp⟩)
        · exact Or.inl (upto_up hpq h)
        · exact Or.inr ⟨y, hy, inChamber_of_le hpq hyp⟩
      have hinter : ∀ p : Sph A, (Prev p ∧ InChamber x p) ↔
          (InChamber x p ∧ (p.spx ∩ rdescFinset A x).Nonempty) := by
        intro p
        constructor
        · rintro ⟨hprev', hpx⟩
          refine ⟨hpx, ?_⟩
          rcases hprev' with ⟨y, hy, hyp⟩ | ⟨y, hyS, hyp⟩
          · exact (mem_shorter_chamber_iff hpx).1 ⟨y, by omega, hyp⟩
          · refine (mem_earlier_chamber_iff hpx).1 ⟨y, ?_, ?_, hyp⟩
            · intro hxy
              exact hxS (hxy ▸ hyS)
            · rw [hlen y (Set.mem_insert_of_mem _ hyS), hxlen]
        · rintro ⟨hpx, hne⟩
          obtain ⟨y, hylt, hyp⟩ := (mem_shorter_chamber_iff hpx).2 hne
          exact ⟨Or.inl ⟨y, by omega, hyp⟩, hpx⟩
      have hmain := acyclicIn_union_chamber hx1 Prev hup hPrevAcyc hinter
      refine Nerve.acyclicIn_congr (fun p => ?_) hmain
      constructor
      · grind
      · grind

/-- **Every cycle supported on the first `n` length levels of chambers is a boundary there.** -/
theorem acyclicIn_upto (A : CommRel V) : ∀ n : ℕ, AcyclicIn (Upto (A := A) n) := by
  intro n
  induction n with
  | zero =>
      exact Nerve.acyclicIn_congr (fun p => (upto_zero_iff p).symm) (acyclicIn_chamber 1)
  | succ n ih =>
      have h := acyclicIn_upto_insert n ih {x : CayGroup A | RACG.clen A x = n + 1}
        (level_finite A (n + 1)) (fun _ hy => hy)
      refine Nerve.acyclicIn_congr (fun p => ?_) h
      constructor
      · rintro (⟨y, hy, hyp⟩ | ⟨y, hy, hyp⟩)
        · exact ⟨y, by omega, hyp⟩
        · exact ⟨y, le_of_eq hy, hyp⟩
      · rintro ⟨y, hy, hyp⟩
        rcases Nat.lt_or_ge (RACG.clen A y) (n + 1) with h' | h'
        · exact Or.inl ⟨y, by omega, hyp⟩
        · exact Or.inr ⟨y, le_antisymm hy h', hyp⟩

/-! ### Acyclicity of the whole complex -/

/-- A bound on the lengths of the representatives of the vertices occurring in a chain. -/
def chainBound (z : Nerve.Ch (Sph A)) : ℕ :=
  z.support.sup (fun l => (l.map (fun p : Sph A => RACG.clen A p.rep)).sum)


/-- **`H_*(𝒟) = 0`.**  Every increasing cycle of the augmented simplicial chain complex of the
poset of spherical cosets — in every degree, in particular every two-cycle — is the boundary of
an increasing chain.  For `z ∈ C₂(𝒟)` with `∂z = 0` this produces `v ∈ C₃(𝒟)` with `∂₃ v = z`. -/
theorem exists_bdry_eq_of_cycle_davis (A : CommRel V) {z : Nerve.Ch (Sph A)}
    (hz : z ∈ Nerve.Inc (Sph A)) (hcyc : Nerve.bdry z = 0) :
    ∃ v ∈ Nerve.Inc (Sph A), Nerve.bdry v = z := by
  obtain ⟨v, hv, hdv⟩ :=
    acyclicIn_upto A (chainBound z) z (by
      rw [Nerve.mem_incOn_iff]
      intro l hl
      refine ⟨(Nerve.mem_inc_iff z).1 hz l hl, ?_⟩
      intro p hp
      refine ⟨p.rep, ?_, inChamber_rep p⟩
      have h1 : RACG.clen A p.rep ≤ (l.map (fun q : Sph A => RACG.clen A q.rep)).sum :=
        List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem hp)
      refine le_trans h1 ?_
      exact Finset.le_sup (f := fun l : List (Sph A) => (l.map (fun p : Sph A => RACG.clen A p.rep)).sum) hl) hcyc
  exact ⟨v, Nerve.incOn_le_inc _ hv, hdv⟩

end Davis
end FiniteChains

namespace FiniteChains

open MonoidAlgebra

attribute [local instance 0] Classical.propDecidable

variable {G : Type*} [Group G] (H : Subgroup G)

/-- The inclusion `ℤ[H] → ℤ[G]` of group rings. -/
def subRingHom : MonoidAlgebra ℤ H →+* MonoidAlgebra ℤ G :=
  MonoidAlgebra.mapDomainRingHom ℤ H.subtype

@[simp] theorem subRingHom_single (h : H) (m : ℤ) :
    subRingHom H (single h m) = single (h : G) m :=
  MonoidAlgebra.mapDomain_single

/-- Restriction of a group-ring element to the subgroup: the coefficients on `H`. -/
def restrictH : MonoidAlgebra ℤ G →+ MonoidAlgebra ℤ H :=
  (MonoidAlgebra.coeffAddEquiv (R := ℤ) (M := H)).symm.toAddMonoidHom.comp
    ((Finsupp.comapDomain.addMonoidHom (M := ℤ) (f := (Subtype.val : H → G))
      Subtype.coe_injective).comp (MonoidAlgebra.coeffAddEquiv (R := ℤ) (M := G)).toAddMonoidHom)

theorem restrictH_apply (x : MonoidAlgebra ℤ G) (h : H) :
    (restrictH H x).coeff h = x.coeff (h : G) := rfl

/-- The `g`-slice of a group-ring element: its coefficients on the left coset `gH`,
translated back to `H`. -/
def slice (g : G) : MonoidAlgebra ℤ G →+ MonoidAlgebra ℤ H :=
  (restrictH H).comp (AddMonoidHom.mulLeft (single g⁻¹ (1 : ℤ)))

theorem slice_apply (g : G) (x : MonoidAlgebra ℤ G) (h : H) :
    (slice H g x).coeff h = x.coeff (g * h) := by simp_all [restrictH_apply, MonoidAlgebra.coeff_single_mul_apply, slice]

theorem restrictH_single (p : G) (m : ℤ) :
    restrictH H (single p m) = if hp : p ∈ H then single ⟨p, hp⟩ m else 0 := by
  by_cases hp : p ∈ H
  · rw [dif_pos hp]
    ext h
    simp only [restrictH_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hh : (⟨p, hp⟩ : H) = h
    · subst hh; simp
    · rw [if_neg hh, if_neg (fun hc : p = h => hh (Subtype.ext hc))]
  · rw [dif_neg hp]
    ext h
    simp only [restrictH_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply,
               MonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
    have : h ≠ p := fun hc => hp (hc ▸ h.2)
    simp [this, Ne.symm this]

/-- **The slice is right `ℤ[H]`-linear.**  Multiplying on the right by an element of the
subgroup ring does not mix the cosets. -/
theorem slice_mul (g : G) (x : MonoidAlgebra ℤ G) (y : MonoidAlgebra ℤ H) :
    slice H g (x * subRingHom H y) = slice H g x * y := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp [add_mul, h₁, h₂]
  | single a m =>
      induction y using MonoidAlgebra.induction_linear with
      | zero => simp
      | add y₁ y₂ h₁ h₂ => simp [mul_add, h₁, h₂]
      | single b n =>
          have hslice : ∀ p c,
              slice H g (single p c) = if hp : g⁻¹ * p ∈ H then single ⟨g⁻¹ * p, hp⟩ c else 0 := by
            intro p c
            show restrictH H (single g⁻¹ (1 : ℤ) * single p c) = _
            rw [MonoidAlgebra.single_mul_single, one_mul, restrictH_single]
          rw [subRingHom_single, MonoidAlgebra.single_mul_single, hslice, hslice]
          by_cases hp : g⁻¹ * a ∈ H
          · have hp' : g⁻¹ * (a * b) ∈ H := by
              have : g⁻¹ * (a * b) = (g⁻¹ * a) * b := by group
              rw [this]
              exact H.mul_mem hp b.2
            rw [dif_pos hp, dif_pos hp', MonoidAlgebra.single_mul_single]
            congr 1
            exact Subtype.ext (by simp [mul_assoc])
          · have hp' : ¬ g⁻¹ * (a * b) ∈ H := by
              intro hc
              apply hp
              have : g⁻¹ * a = (g⁻¹ * (a * (b : G))) * (b : G)⁻¹ := by group
              rw [this]
              exact H.mul_mem hc (H.inv_mem b.2)
            rw [dif_neg hp, dif_neg hp', zero_mul]

/-- The coset piece of `x` at `g`, written as `g` times an element of the subgroup ring. -/
theorem cosetPiece_apply (g : G) (x : MonoidAlgebra ℤ G) (p : G) :
    (single g (1 : ℤ) * subRingHom H (slice H g x)).coeff p
      = if (QuotientGroup.mk p : G ⧸ H) = QuotientGroup.mk g then x.coeff p else 0 := by
  rw [MonoidAlgebra.coeff_single_mul_apply, one_mul]
  by_cases hp : g⁻¹ * p ∈ H
  · have hq  :=
      (QuotientGroup.eq (s := H)).2 (by simpa using H.inv_mem hp)
    rw [if_pos hq]
    have : (subRingHom H (slice H g x)).coeff (g⁻¹ * p) = (slice H g x).coeff ⟨g⁻¹ * p, hp⟩ := by
      show Finsupp.mapDomain H.subtype (slice H g x).coeff (((⟨g⁻¹ * p, hp⟩ : H) : G)) = _
      exact Finsupp.mapDomain_apply_of_injective Subtype.coe_injective _ _
    rw [this, slice_apply]
    congr 1
    group
  · have hq : ¬ ((QuotientGroup.mk p : G ⧸ H) = QuotientGroup.mk g) := by
      intro hc
      exact hp (by simpa using H.inv_mem ((QuotientGroup.eq).1 hc))
    rw [if_neg hq]
    have hnot : ∀ h : H, h ≠ g⁻¹ * p := by
      intro h hc
      exact hp (hc ▸ h.2)
    exact Finsupp.mapDomain_notin_range _ _ (by rintro ⟨h, hh⟩; exact hnot h hh)

/-- **Coset decomposition.**  Every element of `ℤ[G]` is the sum, over the finitely many
cosets meeting its support, of `g` times an element of `ℤ[H]`. -/
theorem sum_cosetPieces (x : MonoidAlgebra ℤ G) :
    ∑ C ∈ (x.coeff.support.image (fun p => (QuotientGroup.mk p : G ⧸ H))),
      single (Quotient.out C) (1 : ℤ) * subRingHom H (slice H (Quotient.out C) x) = x := by
  ext p
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  have hterm : ∀ C ∈ x.coeff.support.image (fun q => (QuotientGroup.mk q : G ⧸ H)),
      (single (Quotient.out C) 1 * subRingHom H (slice H (Quotient.out C) x)).coeff p
        = if (QuotientGroup.mk p) = C then x.coeff p else 0 := by
    intro C _
    rw [cosetPiece_apply]
    congr 1
    simp [Quotient.out_eq]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  by_cases hp : p ∈ x.coeff.support
  · grind
  · simp_all

/-- The coset decomposition over any finite set of cosets containing those that meet the
support. -/
theorem sum_cosetPieces_of_subset (x : MonoidAlgebra ℤ G) (S : Finset (G ⧸ H))
    (hS : x.coeff.support.image (fun p => (QuotientGroup.mk p : G ⧸ H)) ⊆ S) :
    ∑ C ∈ S, single (Quotient.out C) (1 : ℤ) * subRingHom H (slice H (Quotient.out C) x) = x := by
  have hvanish : ∀ C ∈ S, C ∉ x.coeff.support.image (fun p => (QuotientGroup.mk p : G ⧸ H)) →
      single (Quotient.out C) (1 : ℤ) * subRingHom H (slice H (Quotient.out C) x) = 0 := by
    intro C _ hC
    ext p
    simp only [MonoidAlgebra.coeff_zero]
    rw [cosetPiece_apply]
    by_cases hq : (QuotientGroup.mk p : G ⧸ H) = QuotientGroup.mk (Quotient.out C)
    · rw [if_pos hq]
      by_contra hne
      refine hC (Finset.mem_image.2 ⟨p, Finsupp.mem_support_iff.2 hne, ?_⟩)
      simpa using hq
    · simp_all
  rw [← Finset.sum_subset hS hvanish]
  exact sum_cosetPieces H x

variable {J : Type*} [Fintype J] {ι : Type*}

/-- The set of cycles of a matrix with entries in the subgroup ring, pushed into `ℤ[G]`. -/
def subgroupCycles (A : ι → J → MonoidAlgebra ℤ H) : Set (J → MonoidAlgebra ℤ G) :=
  {w | ∃ y : J → MonoidAlgebra ℤ H, (∀ i, ∑ j, y j * A i j = 0) ∧
        w = fun j => subRingHom H (y j)}

/-- **Base change of the module of Fox cycles.**  If the Fox matrix has its entries in the
group ring of a subgroup `H ≤ G`, then every cycle over `ℤ[G]` is a `ℤ[G]`-linear
combination of (the images of) cycles over `ℤ[H]`.  This is the generation statement used in
Lemma 3.9 and Proposition 3.11: the second homotopy group of the enlarged complex is
generated over the enlarged group ring by the image of the old one. -/
theorem cycle_mem_span_subgroup_cycles (A : ι → J → MonoidAlgebra ℤ H)
    (v : J → MonoidAlgebra ℤ G) (hv : ∀ i, ∑ j, v j * subRingHom H (A i j) = 0) :
    v ∈ Submodule.span (MonoidAlgebra ℤ G) (subgroupCycles H A) := by
  -- the slices of a cycle are cycles over `ℤ[H]`
  have hslice : ∀ g : G, ∀ i, ∑ j, slice H g (v j) * A i j = 0 := by
    intro g i
    have h := congrArg (slice H g) (hv i)
    rw [map_sum, map_zero] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => (slice_mul H g (v j) (A i j)).symm
  -- the finite set of cosets meeting the support of the cycle
  set S : Finset (G ⧸ H) :=
    (Finset.univ : Finset J).biUnion (fun j => (v j).coeff.support.image
      (fun p => (QuotientGroup.mk p))) with hS
  have hdecomp : v = ∑ C ∈ S, fun j =>
      single (Quotient.out C) 1 * subRingHom H (slice H (Quotient.out C) (v j)) := by
    funext j
    simp
    refine (sum_cosetPieces_of_subset H (v j) S ?_).symm
    exact Finset.subset_biUnion_of_mem
      (fun j => (v j).coeff.support.image (fun p => (QuotientGroup.mk p)))
      (Finset.mem_univ j)
  rw [hdecomp]
  refine Submodule.sum_mem _ fun C _ => ?_
  have hmem : (fun j => subRingHom H (slice H (Quotient.out C) (v j))) ∈ subgroupCycles H A :=
    ⟨fun j => slice H (Quotient.out C) (v j), hslice (Quotient.out C), rfl⟩
  have := Submodule.smul_mem (Submodule.span (MonoidAlgebra ℤ G) (subgroupCycles H A))
    (single (Quotient.out C) 1) (Submodule.subset_span hmem)
  simpa [Pi.smul_def, smul_eq_mul] using this

end FiniteChains

namespace FiniteChains
namespace Comb

universe u

/-! ### Endpoints of edge paths -/

theorem isPath_start_eq {V E : Type*} {src tgt : E → V} {l : List (E × Bool)} {a a' b b' : V}
    (h : IsPath src tgt l a b) (h' : IsPath src tgt l a' b') (hl : l ≠ []) : a = a' := by
  cases l with
  | nil => simp_all
  | cons eb l => simp_all

theorem isPath_endpoint_eq {V E : Type*} {src tgt : E → V} {l : List (E × Bool)} {a b b' : V}
    (h : IsPath src tgt l a b) (h' : IsPath src tgt l a b') : b = b' := by
  induction l generalizing a with
  | nil => simp_all
  | cons eb l ih => exact ih h.2 h'.2

variable {X Y : Complex2.{u}} {p : Hom X Y}

/-! ### Lifting germs -/

/-- Unique lifting of an oriented edge issued from a vertex of the base. -/
theorem exists_unique_liftGerm (hcov : IsCovering p) (a : X.V) {eb : Y.E × Bool}
    (h : germSrc Y.src Y.tgt eb = p.onV a) :
    ∃! x : X.E × Bool, germSrc X.src X.tgt x = a ∧ (p.onE x.1, x.2) = eb := by
  obtain ⟨hinj, hsurj⟩ := hcov.germ a
  obtain ⟨x, hx⟩ := hsurj ⟨eb, h⟩
  refine ⟨x.1, ⟨x.2, congrArg Subtype.val hx⟩, ?_⟩
  rintro y ⟨hy1, hy2⟩
  have hmap : germMap p a ⟨y, hy1⟩ = germMap p a x := by
    apply Subtype.ext
    rw [hx]
    exact hy2
  exact congrArg Subtype.val (hinj hmap)

/-- Two germs at the same vertex with the same image agree. -/
theorem liftGerm_unique (hcov : IsCovering p) {a : X.V} {x y : X.E × Bool}
    (hx : germSrc X.src X.tgt x = a) (hy : germSrc X.src X.tgt y = a)
    (h : (p.onE x.1, x.2) = (p.onE y.1, y.2)) : x = y := by
  have hs : germSrc Y.src Y.tgt (p.onE x.1, x.2) = p.onV a := by
    rw [germSrc_onE p x, hx]
  obtain ⟨z, -, hz⟩ := exists_unique_liftGerm hcov a hs
  grind

/-- The projection of the reverse of a germ is the reverse of its projection. -/
theorem onE_revGerm (p : Hom X Y) (x : X.E × Bool) :
    (p.onE (revGerm (X := X) x).1, (revGerm (X := X) x).2)
      = revGerm (X := Y) (p.onE x.1, x.2) := rfl

/-! ### Lifting two-cells -/

/-- Unique lifting of a two-cell with a prescribed lift of its basepoint. -/
theorem exists_unique_liftCell (hcov : IsCovering p) (f : Y.F) {v : X.V}
    (hv : Y.base f = p.onV v) : ∃! g : X.F, p.onF g = f ∧ X.base g = v := by
  obtain ⟨hinj, hsurj⟩ := hcov.cell
  obtain ⟨g, hg⟩ := hsurj ⟨(f, v), hv⟩
  have hg' : (p.onF g, X.base g) = (f, v) := congrArg Subtype.val hg
  refine ⟨g, ⟨congrArg Prod.fst hg', congrArg Prod.snd hg'⟩, ?_⟩
  rintro g' ⟨h1, h2⟩
  refine hinj (Subtype.ext ?_)
  show (p.onF g', X.base g') = (p.onF g, X.base g)
  rw [hg', h1, h2]

theorem mapPath_att (g : X.F) : mapPath p (X.att g) = Y.att (p.onF g) := (p.att_onF g).symm

/-! ### Lifting paths -/

/-- **Path lifting**: every edge path of the base issued from `p a` lifts to an edge path
issued from `a`. -/
theorem exists_liftPathAt (hcov : IsCovering p) :
    ∀ (l : List (Y.E × Bool)) (a : X.V) (b : Y.V), IsPath Y.src Y.tgt l (p.onV a) b →
      ∃ (m : List (X.E × Bool)) (c : X.V), IsPath X.src X.tgt m a c ∧ mapPath p m = l := by
  intro l
  induction l with
  | nil => intro a b _; exact ⟨[], a, rfl, rfl⟩
  | cons eb l ih =>
      intro a b hl
      obtain ⟨ha, hrest⟩ := hl
      obtain ⟨x, ⟨hx1, hx2⟩, -⟩ := exists_unique_liftGerm hcov a ha.symm
      have hstep : p.onV (germTgt X.src X.tgt x) = germTgt Y.src Y.tgt eb := by
        rw [← hx2, germTgt_onE p x]
      obtain ⟨m, c, hm, hmap⟩ := ih (germTgt X.src X.tgt x) b (by rw [hstep]; exact hrest)
      refine ⟨x :: m, c, ⟨hx1.symm, hm⟩, ?_⟩
      show (p.onE x.1, x.2) :: mapPath p m = eb :: l
      rw [hx2, hmap]

/-- **Uniqueness of lifts**: two lifts of the same edge path with the same initial vertex
coincide. -/
theorem liftPath_unique (hcov : IsCovering p) :
    ∀ (m m' : List (X.E × Bool)) (a b b' : X.V), IsPath X.src X.tgt m a b →
      IsPath X.src X.tgt m' a b' → mapPath p m = mapPath p m' → m = m' := by
  intro m
  induction m with
  | nil =>
      intro m' _ _ _ _ _ hmap
      exact (List.map_eq_nil_iff.mp hmap.symm).symm
  | cons x m ih =>
      intro m' a b b' hm hm' hmap
      cases m' with
      | nil => exact absurd hmap (by simp [mapPath])
      | cons y m' =>
          have hxy : (p.onE x.1, x.2) = (p.onE y.1, y.2) := by
            have h := congrArg List.head? hmap
            simpa [mapPath] using h
          have hx  := liftGerm_unique hcov hm.1.symm hm'.1.symm hxy
          subst hx
          have htail : mapPath p m = mapPath p m' := by
            have h := congrArg List.tail hmap
            simpa [mapPath] using h
          rw [ih m' (germTgt X.src X.tgt x) b b' hm.2 hm'.2 htail]

/-- The lift of the attaching path of a two-cell issued from a lift of its basepoint is the
attaching path of the lifted two-cell. -/
theorem eq_att_of_lift (hcov : IsCovering p) {A : List (X.E × Bool)} {v w : X.V} {g : X.F}
    (hA : IsPath X.src X.tgt A v w) (hg : X.base g = v)
    (hmap : mapPath p A = Y.att (p.onF g)) : A = X.att g := by
  refine liftPath_unique hcov A (X.att g) v w (X.base g) hA (hg ▸ X.att_isLoop g) ?_
  rw [hmap, mapPath_att]

/-! ### Lifting elementary cancellations -/

theorem lift_cancels (hcov : IsCovering p) {a c : X.V} {m : List (X.E × Bool)}
    (hm : IsPath X.src X.tgt m a c) {l' : List (Y.E × Bool)}
    (hc : Cancels Y (mapPath p m) l') :
    ∃ m', IsPath X.src X.tgt m' a c ∧ mapPath p m' = l' ∧ Htpy X a c m m' := by
  rcases hc with ⟨P, Q, x, hl, hl'⟩ | ⟨P, Q, f, hl, hl'⟩
  · -- deleting a backtrack
    obtain ⟨M₁, M₂, hsplit, hM₁, hM₂⟩ := List.map_eq_append_iff.mp hl
    obtain ⟨u, M₃, hM₂eq, hu, hM₃⟩ := List.map_eq_cons_iff.mp hM₂
    obtain ⟨w, Q', hM₃eq, hw, hQ'⟩ := List.map_eq_cons_iff.mp hM₃
    subst hM₃eq; subst hM₂eq; subst hsplit
    have hM₁' : mapPath p M₁ = P := hM₁
    have hQ'' : mapPath p Q' = Q := hQ'
    obtain ⟨v, hP, hu1, hw1, hQpath⟩ :
        ∃ v, IsPath X.src X.tgt M₁ a v ∧ v = germSrc X.src X.tgt u ∧
          germTgt X.src X.tgt u = germSrc X.src X.tgt w ∧
          IsPath X.src X.tgt Q' (germTgt X.src X.tgt w) c := by
      obtain ⟨v, hP, hrest⟩ := isPath_append_iff.mp hm
      exact ⟨v, hP, hrest.1, hrest.2.1, hrest.2.2⟩
    have hwrev : w = revGerm u := by
      refine liftGerm_unique hcov hw1.symm (by rw [germSrc_revGerm]) ?_
      rw [hw, onE_revGerm, ← hu]
    have hQstart : germTgt X.src X.tgt w = v := by
      rw [hwrev, germTgt_revGerm, ← hu1]
    have hpath'  :=
      isPath_append_iff.mpr ⟨v, hP, by rw [← hQstart]; exact hQpath⟩
    refine ⟨M₁ ++ Q', hpath', ?_, ?_⟩
    · simp_all
    · refine Htpy.of_step ⟨hm, hpath', Or.inl ⟨M₁, Q', u, ?_, rfl⟩⟩
      rw [hwrev]
  · -- deleting the attaching path of a two-cell
    obtain ⟨W, Q', hsplit, hW, hQ'⟩ := List.map_eq_append_iff.mp hl
    obtain ⟨M₁, A, hWeq, hM₁, hA⟩ := List.map_eq_append_iff.mp hW
    subst hWeq; subst hsplit
    have hM₁' : mapPath p M₁ = P := hM₁
    have hA' : mapPath p A = Y.att f := hA
    have hQ'' : mapPath p Q' = Q := hQ'
    obtain ⟨w, hWpath, hQpath⟩ := isPath_append_iff.mp hm
    obtain ⟨v, hM₁path, hApath⟩ := isPath_append_iff.mp hWpath
    rcases eq_or_ne A [] with hA0 | hA0
    · subst hA0
      have hvw : v = w := hApath
      subst hvw
      refine ⟨M₁ ++ Q', isPath_append_iff.mpr ⟨v, hM₁path, hQpath⟩, ?_, ?_⟩
      · rw [hl', mapPath_append, hM₁', hQ'']
      · have hmeq : M₁ ++ [] ++ Q' = M₁ ++ Q' := by simp
        rw [hmeq]
        exact Htpy.refl _
    · have hattne : Y.att f ≠ [] := by
        rw [← hA']
        simpa [mapPath] using hA0
      have himg : IsPath Y.src Y.tgt (Y.att f) (p.onV v) (p.onV w) := by
        have h := isPath_mapPath p hApath
        rwa [hA'] at h
      have hbase : Y.base f = p.onV v := isPath_start_eq (Y.att_isLoop f) himg hattne
      obtain ⟨g, ⟨hg1, hg2⟩, -⟩ := exists_unique_liftCell hcov f hbase
      have hAg : A = X.att g := by
        refine eq_att_of_lift hcov hApath hg2 ?_
        rw [hA', hg1]
      have hwv : w = v := by
        have hloop : IsPath X.src X.tgt A v v := by
          rw [hAg]
          exact hg2 ▸ X.att_isLoop g
        exact (isPath_endpoint_eq hApath hloop)
      subst hwv
      have hpath' :=
        isPath_append_iff.mpr ⟨w, hM₁path, hQpath⟩
      refine ⟨M₁ ++ Q', hpath', ?_, ?_⟩
      · simp_all
      · refine Htpy.of_step ⟨hm, hpath', Or.inr ⟨M₁, Q', g, ?_, rfl⟩⟩
        rw [hAg]

theorem lift_uncancels (hcov : IsCovering p) {a c : X.V} {m : List (X.E × Bool)}
    (hm : IsPath X.src X.tgt m a c) {l : List (Y.E × Bool)}
    (hpath : IsPath Y.src Y.tgt l (p.onV a) (p.onV c))
    (hc : Cancels Y l (mapPath p m)) :
    ∃ m', IsPath X.src X.tgt m' a c ∧ mapPath p m' = l ∧ Htpy X a c m m' := by
  rcases hc with ⟨P, Q, x, hl, hl'⟩ | ⟨P, Q, f, hl, hl'⟩
  · -- inserting a backtrack
    obtain ⟨M₁, Q', hsplit, hM₁, hQ'⟩ := List.map_eq_append_iff.mp hl'
    subst hsplit
    have hM₁' : mapPath p M₁ = P := hM₁
    have hQ'' : mapPath p Q' = Q := hQ'
    obtain ⟨v, hM₁path, hQpath⟩ := isPath_append_iff.mp hm
    have hPimg : IsPath Y.src Y.tgt P (p.onV a) (p.onV v) := by
      have h := isPath_mapPath p hM₁path
      rwa [hM₁'] at h
    have hxsrc : germSrc Y.src Y.tgt x = p.onV v := by
      subst hl
      obtain ⟨b₁, hPpath, hrest⟩ := isPath_append_iff.mp hpath
      have hb₁ : b₁ = p.onV v := isPath_endpoint_eq hPpath hPimg
      rw [← hb₁]
      exact hrest.1.symm
    obtain ⟨u, ⟨hu1, hu2⟩, -⟩ := exists_unique_liftGerm hcov v hxsrc
    have hQstart : germTgt X.src X.tgt (revGerm u) = v := by
      rw [germTgt_revGerm, hu1]
    have hpath' : IsPath X.src X.tgt (M₁ ++ u :: revGerm (X := X) u :: Q') a c := by
      refine isPath_append_iff.mpr ⟨v, hM₁path, ?_, ?_, ?_⟩
      · simp_all
      · simp
      · simp_all
    refine ⟨M₁ ++ u :: revGerm u :: Q', hpath', ?_, ?_⟩
    · have hmid : mapPath p (u :: revGerm (X := X) u :: Q') = x :: revGerm x :: Q := by
        show (p.onE u.1, u.2) ::
          (p.onE (revGerm u).1, (revGerm u).2) :: mapPath p Q' = _
        rw [hQ'', hu2, onE_revGerm, hu2]
      rw [hl, mapPath_append, hM₁', hmid]
    · refine (Htpy.of_step ⟨hpath', hm, Or.inl ⟨M₁, Q', u, rfl, rfl⟩⟩).symm
  · -- inserting the attaching path of a two-cell
    obtain ⟨M₁, Q', hsplit, hM₁, hQ'⟩ := List.map_eq_append_iff.mp hl'
    subst hsplit
    have hM₁' : mapPath p M₁ = P := hM₁
    have hQ'' : mapPath p Q' = Q := hQ'
    obtain ⟨v, hM₁path, hQpath⟩ := isPath_append_iff.mp hm
    have hPimg : IsPath Y.src Y.tgt P (p.onV a) (p.onV v) := by
      have h := isPath_mapPath p hM₁path
      rwa [hM₁'] at h
    rcases eq_or_ne (Y.att f) [] with hA0 | hA0
    · refine ⟨M₁ ++ Q', hm, ?_, Htpy.refl _⟩
      rw [hl, hA0, mapPath_append, hM₁', hQ'']
      simp
    · have hbase : Y.base f = p.onV v := by
        subst hl
        obtain ⟨b₂, hPA, -⟩ := isPath_append_iff.mp hpath
        obtain ⟨b₁, hPpath, hattpath⟩ := isPath_append_iff.mp hPA
        have hb₁ : b₁ = p.onV v := isPath_endpoint_eq hPpath hPimg
        rw [← hb₁]
        exact isPath_start_eq (Y.att_isLoop f) hattpath hA0
      obtain ⟨g, ⟨hg1, hg2⟩, -⟩ := exists_unique_liftCell hcov f hbase
      have hgloop  := hg2 ▸ X.att_isLoop g
      have hpath'  :=
        isPath_append_iff.mpr ⟨v, isPath_append_iff.mpr ⟨v, hM₁path, hgloop⟩, hQpath⟩
      refine ⟨M₁ ++ X.att g ++ Q', hpath', ?_, ?_⟩
      · rw [hl, mapPath_append, mapPath_append, hM₁', hQ'', mapPath_att, hg1]
      · exact (Htpy.of_step ⟨hpath', hm, Or.inr ⟨M₁, Q', g, rfl, rfl⟩⟩).symm

/-! ### Homotopy lifting -/

/-- **Homotopy lifting**: a homotopy of the projection of a lifted path is covered by a
homotopy of the lift, with the same endpoints. -/
theorem lift_htpy (hcov : IsCovering p) {a c : X.V} {m : List (X.E × Bool)}
    (hm : IsPath X.src X.tgt m a c) {l' : List (Y.E × Bool)}
    (h : Htpy Y (p.onV a) (p.onV c) (mapPath p m) l') :
    ∃ m', IsPath X.src X.tgt m' a c ∧ mapPath p m' = l' ∧ Htpy X a c m m' := by
  induction h with
  | refl => exact ⟨m, hm, rfl, Htpy.refl m⟩
  | tail _ hstep ih =>
      obtain ⟨m₁, hm₁, hmap₁, hhtpy₁⟩ := ih
      rcases hstep with hs | hs
      · obtain ⟨m₂, hm₂, hmap₂, hhtpy₂⟩ :=
          lift_cancels hcov hm₁ (by rw [hmap₁]; exact hs.2.2)
        exact ⟨m₂, hm₂, hmap₂, hhtpy₁.trans hhtpy₂⟩
      · obtain ⟨m₂, hm₂, hmap₂, hhtpy₂⟩ :=
          lift_uncancels hcov hm₁ hs.1 (by rw [hmap₁]; exact hs.2.2)
        exact ⟨m₂, hm₂, hmap₂, hhtpy₁.trans hhtpy₂⟩

/-- **A covering is injective on fundamental groups.** -/
theorem pi1Map_injective_of_isCovering (hcov : IsCovering p) (a : X.V) :
    Function.Injective (pi1Map p a) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨q⟩ hq
  have hnull  := Quotient.exact hq
  obtain ⟨m', hm', hmap', hhtpy⟩ := lift_htpy hcov q.2 hnull
  have hnil  := List.map_eq_nil_iff.mp hmap'
  subst hnil
  exact Quotient.sound hhtpy

end Comb
end FiniteChains

namespace FiniteChains
namespace Comb

universe u

variable {P Q : Type u} [Preorder P] [Preorder Q]

/-- **A covering of preorders.**  `f` is monotone, onto, and the elements above (resp. below) an
element `a` are carried bijectively onto the elements above (resp. below) `f a`. -/
structure IsPosetCover (f : P → Q) : Prop where
  /-- `f` is monotone. -/
  mono : Monotone f
  /-- `f` is onto. -/
  surj : Function.Surjective f
  /-- Unique lifting of the upper interval. -/
  up : ∀ (a : P) (q : Q), f a ≤ q → ∃! b : P, a ≤ b ∧ f b = q
  /-- Unique lifting of the lower interval. -/
  down : ∀ (a : P) (q : Q), q ≤ f a → ∃! b : P, b ≤ a ∧ f b = q

namespace IsPosetCover

variable {f : P → Q} (hf : IsPosetCover f)

include hf

/-- Two elements above `a` with the same image agree. -/
theorem up_inj {a b b' : P} (hb : a ≤ b) (hb' : a ≤ b') (h : f b = f b') : b = b' := by
  obtain ⟨c, -, huniq⟩ := hf.up a (f b) (hf.mono hb)
  grind

/-- Two elements below `a` with the same image agree. -/
theorem down_inj {a b b' : P} (hb : b ≤ a) (hb' : b' ≤ a) (h : f b = f b') : b = b' := by
  obtain ⟨c, -, huniq⟩ := hf.down a (f b) (hf.mono hb)
  grind

end IsPosetCover

/-- **The criterion.**  A covering of preorders induces a combinatorial covering of the
two-skeletons of the order complexes. -/
theorem isCovering_orderCxMap {f : P → Q} (hf : IsPosetCover f) :
    IsCovering (orderCxMap f hf.mono) := by
  refine ⟨hf.surj, ?_, ?_⟩
  · -- germs
    intro a
    constructor
    · rintro ⟨⟨e, b⟩, he⟩ ⟨⟨e', b'⟩, he'⟩ hEq
      have hb  := congrArg (fun g : Germ (orderCx Q) _ => g.1.2) hEq
      subst hb
      have hE  :=
        congrArg (fun g : Germ (orderCx Q) _ => (g.1.1.1.1, g.1.1.1.2)) hEq
      have h1  := congrArg Prod.fst hE
      have h2  := congrArg Prod.snd hE
      refine Subtype.ext (Prod.ext ?_ rfl)
      cases b with
      | false =>
          -- both edges end at `a`
          have hae  := he
          have hae'  := he'
          have hfst : e.1.1 = e'.1.1 :=
            hf.down_inj (a := a) (by rw [← hae]; exact e.2) (by rw [← hae']; exact e'.2) h1
          exact Subtype.ext (Prod.ext hfst (hae.trans hae'.symm))
      | true =>
          have hae  := he
          have hae'  := he'
          have hsnd : e.1.2 = e'.1.2 :=
            hf.up_inj (a := a) (by rw [← hae]; exact e.2) (by rw [← hae']; exact e'.2) h2
          exact Subtype.ext (Prod.ext (hae.trans hae'.symm) hsnd)
    · rintro ⟨⟨d, b⟩, hd⟩
      cases b with
      | true =>
          have hfa : f a = d.1.1 := hd.symm
          have hle : f a ≤ d.1.2 := by rw [hfa]; exact d.2
          obtain ⟨c, ⟨hac, hfc⟩, -⟩ := hf.up a d.1.2 hle
          refine ⟨⟨(⟨(a, c), hac⟩, true), rfl⟩, ?_⟩
          refine Subtype.ext (Prod.ext ?_ rfl)
          exact Subtype.ext (Prod.ext hfa hfc)
      | false =>
          have hfa : f a = d.1.2 := hd.symm
          have hle : d.1.1 ≤ f a := by rw [hfa]; exact d.2
          obtain ⟨c, ⟨hca, hfc⟩, -⟩ := hf.down a d.1.1 hle
          refine ⟨⟨(⟨(c, a), hca⟩, false), rfl⟩, ?_⟩
          refine Subtype.ext (Prod.ext ?_ rfl)
          exact Subtype.ext (Prod.ext hfc hfa)
  · -- two-cells
    constructor
    · rintro t t' hEq
      have hbase : t.1.1 = t'.1.1 :=
        congrArg (fun g : {gv : (orderCx Q).F × (orderCx P).V //
          (orderCx Q).base gv.1 = f gv.2} => g.1.2) hEq
      have hT : (f t.1.1, f t.1.2.1, f t.1.2.2)
          = (f t'.1.1, f t'.1.2.1, f t'.1.2.2) :=
        congrArg (fun g : {gv : (orderCx Q).F × (orderCx P).V //
          (orderCx Q).base gv.1 = f gv.2} => g.1.1.1) hEq
      have h2 : f t.1.2.1 = f t'.1.2.1 := congrArg (fun z : Q × Q × Q => z.2.1) hT
      have h3 : f t.1.2.2 = f t'.1.2.2 := congrArg (fun z : Q × Q × Q => z.2.2) hT
      have hmid : t.1.2.1 = t'.1.2.1 :=
        hf.up_inj t.2.1 (by rw [hbase]; exact t'.2.1) h2
      have htop : t.1.2.2 = t'.1.2.2 :=
        hf.up_inj (t.2.1.trans t.2.2) (by rw [hbase]; exact t'.2.1.trans t'.2.2) h3
      exact Subtype.ext (Prod.ext hbase (Prod.ext hmid htop))
    · rintro ⟨⟨s, a⟩, hs⟩
      have hfa : f a = s.1.1 := hs.symm
      obtain ⟨b, ⟨hab, hfb⟩, -⟩ := hf.up a s.1.2.1 (by rw [hfa]; exact s.2.1)
      obtain ⟨c, ⟨hbc, hfc⟩, -⟩ := hf.up b s.1.2.2 (by rw [hfb]; exact s.2.2)
      refine ⟨⟨(a, b, c), hab, hbc⟩, ?_⟩
      refine Subtype.ext (Prod.ext ?_ rfl)
      exact Subtype.ext (Prod.ext hfa (Prod.ext hfb hfc))

end Comb
end FiniteChains

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains
namespace Comb

universe u

variable {P Q : Type u} [Preorder P] [Preorder Q]

/-- One elementary cancellation between two paths, both lying inside the subposet `A`. -/
def StepIn (A : P → Prop) (a b : P) (l l' : List ((orderCx P).E × Bool)) : Prop :=
  Step (orderCx P) a b l l' ∧ PathIn A l ∧ PathIn A l'

/-- **Homotopy of edge paths inside a subposet**: the equivalence relation generated by the
elementary cancellations through paths lying inside `A`. -/
def HtpyIn (A : P → Prop) (a b : P) (p q : List ((orderCx P).E × Bool)) : Prop :=
  Relation.ReflTransGen (fun l l' => StepIn A a b l l' ∨ StepIn A a b l' l) p q

namespace HtpyIn

variable {A B : P → Prop} {a b c d : P} {p q r : List ((orderCx P).E × Bool)}

theorem refl (p : List ((orderCx P).E × Bool)) : HtpyIn A a b p p := Relation.ReflTransGen.refl

theorem trans (h : HtpyIn A a b p q) (h' : HtpyIn A a b q r) : HtpyIn A a b p r :=
  Relation.ReflTransGen.trans h h'

theorem symm (h : HtpyIn A a b p q) : HtpyIn A a b q p := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hstep.symm) ih

theorem of_step (h : StepIn A a b p q) : HtpyIn A a b p q :=
  Relation.ReflTransGen.single (Or.inl h)

/-- Forgetting the subposet: a homotopy inside `A` is a homotopy of the ambient complex. -/
theorem htpy (h : HtpyIn A a b p q) : Htpy (orderCx P) a b p q :=
  Relation.ReflTransGen.mono (fun _ _ hs => hs.imp (fun h => h.1) (fun h => h.1)) _ _ h

/-- Enlarging the subposet. -/
theorem mono (hAB : ∀ x, A x → B x) (h : HtpyIn A a b p q) : HtpyIn B a b p q :=
  Relation.ReflTransGen.mono
    (fun _ _ hs => hs.imp
      (fun h => ⟨h.1, pathIn_mono hAB h.2.1, pathIn_mono hAB h.2.2⟩)
      (fun h => ⟨h.1, pathIn_mono hAB h.2.1, pathIn_mono hAB h.2.2⟩)) _ _ h

/-- A homotopy inside `A` preserves the property of lying inside `A`. -/
theorem pathIn (h : HtpyIn A a b p q) (hp : PathIn A p) : PathIn A q := by
  induction h with
  | refl => exact hp
  | tail _ hstep ih =>
      rcases hstep with hs | hs
      · exact hs.2.2
      · exact hs.2.1

theorem isPath (h : HtpyIn A a b p q)
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b) :
    IsPath (orderCx P).src (orderCx P).tgt q a b := Htpy.isPath h.htpy hp

end HtpyIn

/-- An elementary cancellation survives inside a longer path. -/
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
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      refine Relation.ReflTransGen.tail ih ?_
      rcases hstep with h | h
      · exact Or.inl (h.append hr hs hrA hsA)
      · exact Or.inr (h.append hr hs hrA hsA)

/-- Homotopies inside `A` may be concatenated. -/
theorem HtpyIn.append_congr {A : P → Prop} {a b c : P} {p p' q q' : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b)
    (hq : IsPath (orderCx P).src (orderCx P).tgt q b c)
    (hpA : PathIn A p) (hqA : PathIn A q)
    (h : HtpyIn A a b p p') (h' : HtpyIn A b c q q') :
    HtpyIn A a c (p ++ q) (p' ++ q') := by
  have hp'  := h.isPath hp
  have hp'A  := h.pathIn hpA
  have h1 : HtpyIn A a c (p ++ q) (p' ++ q) := by
    simpa using
      h.congr_append (r := []) rfl hq (pathIn_nil A) hqA
  have h2 : HtpyIn A a c (p' ++ q) (p' ++ q') := by
    simpa using
      h'.congr_append (s := []) hp' rfl hp'A
        (pathIn_nil A)
  exact h1.trans h2

/-- Cancelling a path against its reverse, inside `A`. -/
theorem htpyIn_append_revPath {A : P → Prop} {p : List ((orderCx P).E × Bool)} {a b : P}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b) (hpA : PathIn A p) :
    HtpyIn A a a (p ++ revPath p) [] := by
  induction p generalizing a with
  | nil => cases hp; exact Relation.ReflTransGen.refl
  | cons eb p ih =>
      obtain ⟨ha, hrest⟩ := hp
      subst ha
      obtain ⟨hebA, hpA'⟩ := pathIn_of_cons hpA
      have hih  := ih hrest hpA'
      have hebPath  := isPath_single eb
      have hrevPath : IsPath (orderCx P).src (orderCx P).tgt [revGerm eb]
          (germTgt (orderCx P).src (orderCx P).tgt eb)
          (germSrc (orderCx P).src (orderCx P).tgt eb) := by
        exact ⟨(germSrc_revGerm eb).symm,
          germTgt_revGerm eb⟩
      have hsingleA  := pathIn_cons hebA (pathIn_nil A)
      have hrevA : PathIn A [revGerm eb] := pathIn_cons hebA (pathIn_nil A)
      have hcongr  :=
        hih.congr_append hebPath hrevPath hsingleA hrevA
      have hrw : (eb :: p) ++ revPath (eb :: p) = [eb] ++ (p ++ revPath p) ++ [revGerm eb] := by
        simp [revPath, List.append_assoc]
      have hlast : HtpyIn A (germSrc (orderCx P).src (orderCx P).tgt eb)
          (germSrc (orderCx P).src (orderCx P).tgt eb) [eb, revGerm eb] [] := by
        refine HtpyIn.of_step ⟨⟨?_, rfl, Or.inl ⟨[], [], eb, rfl, rfl⟩⟩, ?_, pathIn_nil A⟩
        · simp
        · exact pathIn_cons hebA (pathIn_cons hebA (pathIn_nil A))
      rw [hrw]
      refine hcongr.trans ?_
      simpa using hlast

theorem htpyIn_revPath_append {A : P → Prop} {p : List ((orderCx P).E × Bool)} {a b : P}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b) (hpA : PathIn A p) :
    HtpyIn A b b (revPath p ++ p) [] := by
  have h := htpyIn_append_revPath (isPath_revPath hp) (pathIn_revPath hpA)
  simpa using h

/-! ### Moving homotopies between a subposet and the ambient complex -/

/-- **Pushing a homotopy forward along a monotone map.**  If the values of `f` lie in the
subposet `C`, the image of a homotopy of the order complex of `Q` is a homotopy inside `C`. -/
theorem htpyIn_mapPath {C : P → Prop} (f : Q → P) (hf : Monotone f) (hC : ∀ x, C (f x))
    {a b : Q} {p q : List ((orderCx Q).E × Bool)} (h : Htpy (orderCx Q) a b p q) :
    HtpyIn C (f a) (f b) (mapPath (orderCxMap f hf) p) (mapPath (orderCxMap f hf) q) := by
  have hpathIn : ∀ l : List ((orderCx Q).E × Bool), PathIn C (mapPath (orderCxMap f hf) l) := by
    intro l e he
    simp only [mapPath, List.mem_map] at he
    obtain ⟨x, -, rfl⟩ := he
    exact ⟨hC _, hC _⟩
  have hstep : ∀ l l' : List ((orderCx Q).E × Bool), Step (orderCx Q) a b l l' →
      StepIn C (f a) (f b) (mapPath (orderCxMap f hf) l) (mapPath (orderCxMap f hf) l') := by
    intro l l' hs
    refine ⟨?_, hpathIn l, hpathIn l'⟩
    obtain ⟨hl, hl', hc⟩ := hs
    refine ⟨isPath_mapPath (orderCxMap f hf) hl, isPath_mapPath (orderCxMap f hf) hl', ?_⟩
    rcases hc with ⟨p', q', eb, hlEq, hl'Eq⟩ | ⟨p', q', t, hlEq, hl'Eq⟩
    · refine Or.inl ⟨mapPath (orderCxMap f hf) p', mapPath (orderCxMap f hf) q',
        ((orderCxMap f hf).onE eb.1, eb.2), ?_, ?_⟩
      · rw [hlEq]; simp [mapPath, revGerm]
      · rw [hl'Eq]; simp [mapPath]
    · refine Or.inr ⟨mapPath (orderCxMap f hf) p', mapPath (orderCxMap f hf) q',
        (orderCxMap f hf).onF t, ?_, ?_⟩
      · rw [hlEq]
        have hatt : mapPath (orderCxMap f hf) ((orderCx Q).att t) =
            (orderCx P).att ((orderCxMap f hf).onF t) := by
          rw [(orderCxMap f hf).att_onF t]; rfl
        simp [mapPath, orderCxMap, orderCx]
      · simp_all
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
      rcases hs with hel | hel
      · exact ih.trans (HtpyIn.of_step (hstep _ _ hel))
      · exact ih.trans (HtpyIn.of_step (hstep _ _ hel)).symm

/-! ### Lifting a homotopy inside `A` to the order complex of `A` -/

section Lift

variable {C : P → Prop}

theorem liftPathIn_append (l l' : List ((orderCx P).E × Bool)) (h : PathIn C l)
    (h' : PathIn C l') (hall : PathIn C (l ++ l')) :
    liftPathIn (A := C) (l ++ l') hall = liftPathIn l h ++ liftPathIn l' h' := by
  induction l with
  | nil => rfl
  | cons e t ih =>
      simp only [List.cons_append, liftPathIn, List.cons.injEq, true_and]
      exact ih (pathIn_of_cons h).2 (pathIn_of_cons hall).2

/-- The lift of the attaching path of a two-cell whose vertices lie in `C` is the attaching
path of the corresponding two-cell of the subposet. -/
theorem liftPathIn_att (t : OrdTri P) (hx : C t.1.1) (hy : C t.1.2.1) (hz : C t.1.2.2)
    (h : PathIn C ((orderCx P).att t)) :
    liftPathIn (A := C) ((orderCx P).att t) h =
      (orderCx {x : P // C x}).att
        (⟨(⟨t.1.1, hx⟩, ⟨t.1.2.1, hy⟩, ⟨t.1.2.2, hz⟩), t.2.1, t.2.2⟩ : OrdTri {x : P // C x}) :=
  rfl

/-- **Lifting a homotopy inside `C` to the order complex of `C`.** -/
theorem htpy_lift_of_htpyIn {a b : P} {p q : List ((orderCx P).E × Bool)}
    (h : HtpyIn C a b p q) (ha : C a) (hb : C b) (hp : PathIn C p) (hq : PathIn C q) :
    Htpy (orderCx {x : P // C x}) ⟨a, ha⟩ ⟨b, hb⟩ (liftPathIn p hp) (liftPathIn q hq) := by
  have hstep : ∀ l l' : List ((orderCx P).E × Bool), ∀ hl hl',
      StepIn C a b l l' →
      Step (orderCx {x : P // C x}) ⟨a, ha⟩ ⟨b, hb⟩ (liftPathIn l hl) (liftPathIn l' hl') := by
    intro l l' hl hl' hs
    obtain ⟨⟨hpl, hpl', hc⟩, -, -⟩ := hs
    refine ⟨isPath_liftPathIn l hl ha hb hpl, isPath_liftPathIn l' hl' ha hb hpl', ?_⟩
    rcases hc with ⟨p', q', eb, hlEq, hl'Eq⟩ | ⟨p', q', t, hlEq, hl'Eq⟩
    · subst hlEq
      subst hl'Eq
      have hp'  := pathIn_of_append_left hl
      have hrest  := pathIn_of_append_right hl
      have heb  := (pathIn_of_cons hrest).1
      have hq'  := (pathIn_of_cons (pathIn_of_cons hrest).2).2
      refine Or.inl ⟨liftPathIn p' hp', liftPathIn q' hq', liftGermIn eb heb, ?_, ?_⟩
      · rw [liftPathIn_append p' (eb :: revGerm eb :: q') hp' hrest]
        rfl
      · exact liftPathIn_append p' q' hp' hq' _
    · subst hlEq
      subst hl'Eq
      have hfront  := pathIn_of_append_left hl
      have hp'  := pathIn_of_append_left hfront
      have hatt  := pathIn_of_append_right hfront
      have hq'  := pathIn_of_append_right hl
      have h1 := hatt (⟨(t.1.1, t.1.2.1), t.2.1⟩, true) (by simp [orderCx])
      have h2 := hatt (⟨(t.1.2.1, t.1.2.2), t.2.2⟩, true) (by simp [orderCx])
      have hx  := h1.1
      have hy  := h1.2
      have hz  := h2.2
      refine Or.inr ⟨liftPathIn p' hp', liftPathIn q' hq',
        ⟨(⟨t.1.1, hx⟩, ⟨t.1.2.1, hy⟩, ⟨t.1.2.2, hz⟩), t.2.1, t.2.2⟩,
        ?_, ?_⟩
      · rw [liftPathIn_append (p' ++ (orderCx P).att t) q' hfront hq',
          liftPathIn_append p' ((orderCx P).att t) hp' hatt,
          liftPathIn_att t hx hy hz hatt]
      · exact liftPathIn_append p' q' hp' hq' _
  revert hq
  induction h with
  | refl => intro hq; exact Htpy.refl _
  | @tail u v _ hs ih =>
      intro hq
      have hu : PathIn C u := by
        rcases hs with h' | h'
        · exact h'.2.1
        · exact h'.2.2
      refine (ih hu).trans ?_
      rcases hs with h' | h'
      · exact Htpy.of_step (hstep u v hu hq h')
      · exact (Htpy.of_step (hstep v u hq hu h')).symm

end Lift

end Comb
end FiniteChains
end

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains
namespace Comb

universe u

variable {P Q : Type u} [Preorder P] [Preorder Q]

/-! ### Injectivity on path classes -/

/-- **`B` is injective on path classes inside `U`**: a loop inside `B` that is null-homotopic
inside `U` is null-homotopic inside `B`. -/
def InjIn (U B : P → Prop) : Prop :=
  ∀ (v : P) (l : List ((orderCx P).E × Bool)), B v →
    IsPath (orderCx P).src (orderCx P).tgt l v v → PathIn B l →
    HtpyIn U v v l [] → HtpyIn B v v l []

/-- Every loop inside `J` is null-homotopic inside `J`. -/
def SimplyConnectedIn (J : P → Prop) : Prop :=
  ∀ (v : P) (l : List ((orderCx P).E × Bool)), J v →
    IsPath (orderCx P).src (orderCx P).tgt l v v → PathIn J l → HtpyIn J v v l []

theorem injIn_self (U : P → Prop) : InjIn U U := fun _ _ _ _ _ h => h

/-- Both endpoints of an oriented edge with endpoints in `C` lie in `C`. -/
theorem germ_ends {C : P → Prop} {eb : (orderCx P).E × Bool} (h : C eb.1.1.1 ∧ C eb.1.1.2) :
    C (germSrc (orderCx P).src (orderCx P).tgt eb) ∧
      C (germTgt (orderCx P).src (orderCx P).tgt eb) := by
  obtain ⟨e, tag⟩ := eb
  cases tag
  · exact ⟨h.2, h.1⟩
  · exact ⟨h.1, h.2⟩

/-- Injectivity on path classes only depends on the ambient subposet up to equivalence. -/
theorem injIn_congr_left {U U' B : P → Prop} (h : ∀ x, U x ↔ U' x) (hinj : InjIn U B) :
    InjIn U' B :=
  fun v l hv hp hl hh => hinj v l hv hp hl (HtpyIn.mono (fun x hx => (h x).2 hx) hh)

/-- Injectivity on path classes composes. -/
theorem injIn_trans {U A B : P → Prop} (hBA : ∀ x, B x → A x)
    (hUA : InjIn U A) (hAB : InjIn A B) : InjIn U B := by
  intro v l hv hp hl h
  exact hAB v l hv hp hl (hUA v l (hBA v hv) hp (pathIn_mono hBA hl) h)

/-- Simple connectedness of a subposet, in the form produced by the order-complex results of the
project. -/
theorem simplyConnectedIn_of_simplyConnected {J : P → Prop}
    (hJ : SimplyConnected (orderCx {x : P // J x})) : SimplyConnectedIn J := by
  intro v l hv hp hl
  have hlift := isPath_liftPathIn l hl hv hv hp
  have hnull := hJ ⟨v, hv⟩ (liftPathIn l hl) hlift
  have h := htpyIn_mapPath (fun x : {x : P // J x} => (x : P)) monotone_subtypeVal
    (fun x => x.2) hnull
  rw [show mapPath (orderCxMap (fun x : {x : P // J x} => (x : P)) monotone_subtypeVal)
      (liftPathIn l hl) = l from mapPath_liftPathIn l hl] at h
  simpa [mapPath] using h

/-! ### The retraction on paths -/

section Retr

variable (A : P → Prop) (j0 : P) (γ : P → List ((orderCx P).E × Bool))

open Classical in
/-- The retraction on vertices: a vertex of `A` stays where it is, any other vertex goes to the
base vertex `j0` of the intersection. -/
def retrVert (u : P) : P := if A u then u else j0

open Classical in
/-- The retraction on oriented edges: an edge of `A` is unchanged, any other edge `u → v` is
replaced by `γ u ⁻¹ γ v`. -/
def retrGerm (eb : (orderCx P).E × Bool) : List ((orderCx P).E × Bool) :=
  if A eb.1.1.1 ∧ A eb.1.1.2 then [eb]
  else revPath (γ (germSrc (orderCx P).src (orderCx P).tgt eb)) ++
    γ (germTgt (orderCx P).src (orderCx P).tgt eb)

/-- The retraction on edge paths. -/
def retrPath : List ((orderCx P).E × Bool) → List ((orderCx P).E × Bool)
  | [] => []
  | eb :: t => retrGerm A γ eb ++ retrPath t

variable {A j0 γ}

@[simp] theorem retrPath_nil : retrPath A γ [] = [] := rfl

@[simp] theorem retrPath_cons (eb : (orderCx P).E × Bool) (t : List ((orderCx P).E × Bool)) :
    retrPath A γ (eb :: t) = retrGerm A γ eb ++ retrPath A γ t := rfl

theorem retrPath_append (l l' : List ((orderCx P).E × Bool)) :
    retrPath A γ (l ++ l') = retrPath A γ l ++ retrPath A γ l' := by
  induction l with
  | nil => rfl
  | cons eb t ih => simp_all

omit [Preorder P] in
theorem retrVert_of_mem {u : P} (hu : A u) : retrVert A j0 u = u := by
  simp [retrVert, hu]


theorem retrGerm_of_mem {eb : (orderCx P).E × Bool} (h : A eb.1.1.1 ∧ A eb.1.1.2) :
    retrGerm A γ eb = [eb] := by
  simp [retrGerm, h]

theorem retrGerm_of_not_mem {eb : (orderCx P).E × Bool} (h : ¬ (A eb.1.1.1 ∧ A eb.1.1.2)) :
    retrGerm A γ eb = revPath (γ (germSrc (orderCx P).src (orderCx P).tgt eb)) ++
      γ (germTgt (orderCx P).src (orderCx P).tgt eb) := by
  simp [retrGerm, h]

/-- A path inside `A` is returned unchanged. -/
theorem retrPath_eq_self {l : List ((orderCx P).E × Bool)} (hl : PathIn A l) :
    retrPath A γ l = l := by
  induction l with
  | nil => rfl
  | cons eb t ih =>
      obtain ⟨heb, ht⟩ := pathIn_of_cons hl
      rw [retrPath_cons, retrGerm_of_mem heb, ih ht, List.singleton_append]

/-- The retraction lands inside `A`. -/
theorem pathIn_retrPath (hγA : ∀ u : P, PathIn A (γ u)) (l : List ((orderCx P).E × Bool)) :
    PathIn A (retrPath A γ l) := by
  induction l with
  | nil => exact pathIn_nil A
  | cons eb t ih =>
      refine pathIn_append ?_ ih
      by_cases h : A eb.1.1.1 ∧ A eb.1.1.2
      · rw [retrGerm_of_mem h]
        exact pathIn_cons h (pathIn_nil A)
      · rw [retrGerm_of_not_mem h]
        exact pathIn_append (pathIn_revPath (hγA _)) (hγA _)

end Retr

/-! ### The gluing step -/

section Gluing

variable {A B U J : P → Prop} {j0 : P} {γ : P → List ((orderCx P).E × Bool)}

variable (hJA : ∀ x, J x → A x) (hJmk : ∀ x, A x → B x → J x)
  (hγpath : ∀ u : P, J u → IsPath (orderCx P).src (orderCx P).tgt (γ u) j0 u)
  (hγin : ∀ u : P, PathIn J (γ u)) (hγnil : ∀ u : P, ¬ J u → γ u = [])

include hJA hγin in
theorem pathIn_gamma_of_subset (u : P) : PathIn A (γ u) :=
  pathIn_mono hJA (hγin u)

include hJA hJmk hγpath hγnil in
/-- The chosen path from the base vertex to the image of a vertex of `B`. -/
theorem isPath_gamma {u : P} (hu : B u) :
    IsPath (orderCx P).src (orderCx P).tgt (γ u) j0 (retrVert A j0 u) := by
  by_cases hA : A u
  · rw [retrVert_of_mem hA]
    exact hγpath u (hJmk u hA hu)
  · rw [(show retrVert A j0 u = j0 by
    simp [retrVert, hA]), hγnil u (fun h => hA (hJA u h))]
    rfl

include hJA hJmk hγpath hγnil in
/-- The image of an oriented edge is a path between the images of its endpoints. -/
theorem isPath_retrGerm (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    {eb : (orderCx P).E × Bool} (h1 : U eb.1.1.1) (h2 : U eb.1.1.2) :
    IsPath (orderCx P).src (orderCx P).tgt (retrGerm A γ eb)
      (retrVert A j0 (germSrc (orderCx P).src (orderCx P).tgt eb))
      (retrVert A j0 (germTgt (orderCx P).src (orderCx P).tgt eb)) := by
  by_cases hA : A eb.1.1.1 ∧ A eb.1.1.2
  · rw [retrGerm_of_mem hA]
    have hAs := germ_ends hA
    rw [retrVert_of_mem hAs.1, retrVert_of_mem hAs.2]
    exact isPath_single _
  · rw [retrGerm_of_not_mem hA]
    have hB : B eb.1.1.1 ∧ B eb.1.1.2 := by
      rcases hmix eb.1.1.1 eb.1.1.2 eb.1.2 h1 h2 with h | h
      · simp_all
      · exact h
    have hBs := germ_ends hB
    refine isPath_append_iff.mpr ⟨j0, ?_, isPath_gamma hJA hJmk hγpath hγnil hBs.2⟩
    exact isPath_revPath (isPath_gamma hJA hJmk hγpath hγnil hBs.1)

include hJA hJmk hγpath hγnil in
/-- The image of a path is a path between the images of its endpoints. -/
theorem isPath_retrPath (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b)) :
    ∀ (l : List ((orderCx P).E × Bool)) {a b : P},
      IsPath (orderCx P).src (orderCx P).tgt l a b → PathIn U l →
      IsPath (orderCx P).src (orderCx P).tgt (retrPath A γ l) (retrVert A j0 a)
        (retrVert A j0 b) := by
  intro l
  induction l with
  | nil => simp
  | cons eb t ih =>
      intro a b hp hU
      obtain ⟨ha, hrest⟩ := hp
      subst ha
      obtain ⟨hUe, hUt⟩ := pathIn_of_cons hU
      refine isPath_append_iff.mpr
        ⟨retrVert A j0 (germTgt (orderCx P).src (orderCx P).tgt eb), ?_, ih hrest hUt⟩
      exact isPath_retrGerm hJA hJmk hγpath hγnil hmix hUe.1 hUe.2

include hJA hJmk hγpath hγin in
/-- **On the edges of `J` the two formulas agree.**  This is the only place where the simple
connectedness of the intersection is used. -/
theorem htpyIn_retrGerm_of_pathIn_B (hJsc : SimplyConnectedIn J) (hj0 : J j0)
    {eb : (orderCx P).E × Bool} (hB : B eb.1.1.1 ∧ B eb.1.1.2) :
    HtpyIn A (retrVert A j0 (germSrc (orderCx P).src (orderCx P).tgt eb))
      (retrVert A j0 (germTgt (orderCx P).src (orderCx P).tgt eb))
      (retrGerm A γ eb)
      (revPath (γ (germSrc (orderCx P).src (orderCx P).tgt eb)) ++
        γ (germTgt (orderCx P).src (orderCx P).tgt eb)) := by
  by_cases hA : A eb.1.1.1 ∧ A eb.1.1.2
  · -- the edge lies in `J`
    set s : P := germSrc (orderCx P).src (orderCx P).tgt eb with hs
    set t : P := germTgt (orderCx P).src (orderCx P).tgt eb with ht
    have hAs  := germ_ends hA
    have hBs  := germ_ends hB
    have hJs  := hJmk s hAs.1 hBs.1
    have hJt  := hJmk t hAs.2 hBs.2
    have hγs : IsPath (orderCx P).src (orderCx P).tgt (γ s) j0 s := hγpath s hJs
    have hγt := hγpath t hJt
    have hγsA := pathIn_gamma_of_subset hJA hγin s
    have hγtA := pathIn_gamma_of_subset hJA hγin t
    have hebPath  := isPath_single eb
    have hebA  := pathIn_cons hA (pathIn_nil A)
    -- the loop `γ s · eb · γ t ⁻¹` lies in `J` and is therefore null-homotopic inside `J`
    have hloopPath : IsPath (orderCx P).src (orderCx P).tgt
        (γ s ++ ([eb] ++ revPath (γ t))) j0 j0 :=
      isPath_append_iff.mpr ⟨s, hγs,
        isPath_append_iff.mpr ⟨t, hebPath, isPath_revPath hγt⟩⟩
    have hebJ : J eb.1.1.1 ∧ J eb.1.1.2 :=
      ⟨hJmk _ hA.1 hB.1, hJmk _ hA.2 hB.2⟩
    have hloopIn  :=
      pathIn_append (hγin s)
        (pathIn_append (pathIn_cons hebJ (pathIn_nil J)) (pathIn_revPath (hγin t)))
    have hnull  :=
      HtpyIn.mono hJA (hJsc j0 _ hj0 hloopPath hloopIn)
    -- conjugate the null-homotopy by `γ s ⁻¹` and `γ t`
    have hconj  :=
      hnull.congr_append (isPath_revPath hγs) hγt (pathIn_revPath hγsA) hγtA
    -- the left-hand side is homotopic to `eb`
    have hcancel1 : HtpyIn A s s (revPath (γ s) ++ γ s) [] := htpyIn_revPath_append hγs hγsA
    have hcancel2 : HtpyIn A t t (revPath (γ t) ++ γ t) [] := htpyIn_revPath_append hγt hγtA
    have hstep1 : HtpyIn A s t ([eb] ++ (revPath (γ t) ++ γ t)) ([eb] ++ []) :=
      HtpyIn.append_congr hebPath
        (isPath_append_iff.mpr ⟨j0, isPath_revPath hγt, hγt⟩) hebA
        (pathIn_append (pathIn_revPath hγtA) hγtA) (HtpyIn.refl _) hcancel2
    have hstep2 : HtpyIn A s t ((revPath (γ s) ++ γ s) ++ ([eb] ++ (revPath (γ t) ++ γ t)))
        ([] ++ ([eb] ++ (revPath (γ t) ++ γ t))) :=
      HtpyIn.append_congr (isPath_append_iff.mpr ⟨j0, isPath_revPath hγs, hγs⟩)
        (isPath_append_iff.mpr ⟨t, hebPath, isPath_append_iff.mpr ⟨j0, isPath_revPath hγt, hγt⟩⟩)
        (pathIn_append (pathIn_revPath hγsA) hγsA)
        (pathIn_append hebA (pathIn_append (pathIn_revPath hγtA) hγtA))
        hcancel1 (HtpyIn.refl _)
    have hmain : HtpyIn A s t [eb] (revPath (γ s) ++ γ t) := by
      have h1 : HtpyIn A s t [eb] ((revPath (γ s) ++ γ s) ++ ([eb] ++ (revPath (γ t) ++ γ t))) := by
        refine (HtpyIn.trans ?_ hstep2.symm)
        simpa using hstep1.symm
      refine h1.trans ?_
      have h2 : (revPath (γ s) ++ γ s) ++ ([eb] ++ (revPath (γ t) ++ γ t)) =
          revPath (γ s) ++ (γ s ++ ([eb] ++ revPath (γ t))) ++ γ t := by
        simp [List.append_assoc]
      rw [h2]
      refine hconj.trans ?_
      simpa using HtpyIn.refl (A := A) (a := s) (b := t) (revPath (γ s) ++ γ t)
    rw [retrGerm_of_mem hA, retrVert_of_mem hAs.1, retrVert_of_mem hAs.2]
    exact hmain
  · rw [retrGerm_of_not_mem hA]
    exact HtpyIn.refl _

include hJA hJmk hγpath hγin hγnil in
/-- **Telescoping along a path of `B`.**  The image of a path of `B` from `u` to `v` is
homotopic, inside `A`, to `γ u ⁻¹ γ v`. -/
theorem htpyIn_retrPath_of_pathIn_B (hJsc : SimplyConnectedIn J) (hj0 : J j0) :
    ∀ (l : List ((orderCx P).E × Bool)) {u v : P},
      IsPath (orderCx P).src (orderCx P).tgt l u v → PathIn B l → B u → B v →
      HtpyIn A (retrVert A j0 u) (retrVert A j0 v) (retrPath A γ l)
        (revPath (γ u) ++ γ v) := by
  intro l
  induction l with
  | nil =>
      intro u v hp _ hu _
      have huv  := hp
      subst huv
      have hγu :=
        isPath_gamma hJA hJmk hγpath hγnil hu
      have hγuA := pathIn_gamma_of_subset hJA hγin u
      exact (htpyIn_revPath_append hγu hγuA).symm
  | cons eb t ih =>
      intro u v hp hBl hu hv
      obtain ⟨ha, hrest⟩ := hp
      subst ha
      obtain ⟨hBe, hBt⟩ := pathIn_of_cons hBl
      set m : P := germTgt (orderCx P).src (orderCx P).tgt eb with hm
      have hBm  := (germ_ends hBe).2
      have hγu :=
        isPath_gamma hJA hJmk hγpath hγnil hu
      have hγm :=
        isPath_gamma hJA hJmk hγpath hγnil hBm
      have hγv :=
        isPath_gamma hJA hJmk hγpath hγnil hv
      have hγuA : PathIn A (γ (germSrc (orderCx P).src (orderCx P).tgt eb)) :=
        pathIn_gamma_of_subset hJA hγin _
      have hγmA := pathIn_gamma_of_subset hJA hγin m
      have hγvA := pathIn_gamma_of_subset hJA hγin v
      have hgerm := htpyIn_retrGerm_of_pathIn_B hJA hJmk hγpath hγin hJsc hj0 hBe
      have hih := ih hrest hBt hBm hv
      have hfirst : IsPath (orderCx P).src (orderCx P).tgt (retrGerm A γ eb)
          (retrVert A j0 (germSrc (orderCx P).src (orderCx P).tgt eb)) (retrVert A j0 m) := by
        refine HtpyIn.isPath hgerm.symm ?_
        exact isPath_append_iff.mpr ⟨j0, isPath_revPath hγu, hγm⟩
      have hsecond  :=
        HtpyIn.isPath hih.symm (isPath_append_iff.mpr ⟨j0, isPath_revPath hγm, hγv⟩)
      have hfirstA : PathIn A (retrGerm A γ eb) := by
        by_cases hA : A eb.1.1.1 ∧ A eb.1.1.2
        · rw [retrGerm_of_mem hA]; exact pathIn_cons hA (pathIn_nil A)
        · rw [retrGerm_of_not_mem hA]
          exact pathIn_append (pathIn_revPath hγuA) hγmA
      have hsecondA  :=
        pathIn_retrPath (fun x => pathIn_gamma_of_subset hJA hγin x) t
      have hcomb  :=
        HtpyIn.append_congr hfirst hsecond hfirstA hsecondA hgerm hih
      refine hcomb.trans ?_
      -- cancel `γ m ⁻¹ γ m` in the middle
      have hcancel  :=
        htpyIn_append_revPath hγm hγmA
      have hmid  :=
        hcancel.congr_append (isPath_revPath hγu) hγv (pathIn_revPath hγuA) hγvA
      have hrw : (revPath (γ (germSrc (orderCx P).src (orderCx P).tgt eb)) ++ γ m) ++
          (revPath (γ m) ++ γ v) =
          revPath (γ (germSrc (orderCx P).src (orderCx P).tgt eb)) ++
            (γ m ++ revPath (γ m)) ++ γ v := by
        simp [List.append_assoc]
      rw [hrw]
      simpa using hmid

include hJA hJmk hγpath hγin hγnil in
/-- **The retraction respects one elementary cancellation.** -/
theorem htpyIn_retrPath_of_stepIn
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    (hJsc : SimplyConnectedIn J) (hj0 : J j0) {a b : P}
    {l l' : List ((orderCx P).E × Bool)} (h : StepIn U a b l l') :
    HtpyIn A (retrVert A j0 a) (retrVert A j0 b) (retrPath A γ l) (retrPath A γ l') := by
  obtain ⟨⟨hpl, hpl', hc⟩, hUl, hUl'⟩ := h
  have hγA := fun x => pathIn_gamma_of_subset hJA hγin x
  rcases hc with ⟨p', q', eb, hlEq, hl'Eq⟩ | ⟨p', q', t, hlEq, hl'Eq⟩
  · -- a backtrack
    subst hlEq
    subst hl'Eq
    have hUp'  := pathIn_of_append_left hUl
    have hUrest  := pathIn_of_append_right hUl
    obtain ⟨hUe, hUrest'⟩ := pathIn_of_cons hUrest
    have hUq'  := (pathIn_of_cons hUrest').2
    -- endpoints of the pieces
    obtain ⟨c, hpc, hrest⟩ := isPath_append_iff.mp hpl
    obtain ⟨hcs, hrest2⟩ := hrest
    obtain ⟨hmid, hq'⟩ := hrest2
    have hPp'  :=
      isPath_retrPath hJA hJmk hγpath hγnil hmix p' hpc hUp'
    have hcq  := hq'
    have hPq'  :=
      isPath_retrPath hJA hJmk hγpath hγnil hmix q' hcq hUq'
    have hrevTgt  := germTgt_revGerm eb
    -- the two images cancel
    have hkey : HtpyIn A (retrVert A j0 (germSrc (orderCx P).src (orderCx P).tgt eb))
        (retrVert A j0 (germSrc (orderCx P).src (orderCx P).tgt eb))
        (retrGerm A γ eb ++ retrGerm A γ (revGerm eb)) [] := by
      by_cases hA : A eb.1.1.1 ∧ A eb.1.1.2
      · have hA' : A (revGerm eb).1.1.1 ∧ A (revGerm eb).1.1.2 := hA
        rw [retrGerm_of_mem hA, retrGerm_of_mem hA']
        have hsrc : A (germSrc (orderCx P).src (orderCx P).tgt eb) := (germ_ends hA).1
        refine HtpyIn.of_step ⟨⟨?_, rfl, Or.inl ⟨[], [], eb, rfl, rfl⟩⟩, ?_, pathIn_nil A⟩
        · refine ⟨?_, ?_, ?_⟩
          · rw [retrVert_of_mem hsrc]
          · exact (germSrc_revGerm (X := orderCx P) eb).symm
          · rw [retrVert_of_mem hsrc]; exact germTgt_revGerm (X := orderCx P) eb
        · exact pathIn_cons hA (pathIn_cons hA (pathIn_nil A))
      · have hA' : ¬ (A (revGerm eb).1.1.1 ∧ A (revGerm eb).1.1.2) := hA
        rw [retrGerm_of_not_mem hA, retrGerm_of_not_mem hA']
        have hB : B eb.1.1.1 ∧ B eb.1.1.2 := by
          rcases hmix eb.1.1.1 eb.1.1.2 eb.1.2 hUe.1 hUe.2 with h | h
          · simp_all
          · exact h
        have hBs := germ_ends hB
        set s : P := germSrc (orderCx P).src (orderCx P).tgt eb with hs
        set t : P := germTgt (orderCx P).src (orderCx P).tgt eb with ht
        have hγs : IsPath (orderCx P).src (orderCx P).tgt (γ s) j0 (retrVert A j0 s) :=
          isPath_gamma hJA hJmk hγpath hγnil hBs.1
        have hγt : IsPath (orderCx P).src (orderCx P).tgt (γ t) j0 (retrVert A j0 t) :=
          isPath_gamma hJA hJmk hγpath hγnil hBs.2
        have hsimp : germSrc (orderCx P).src (orderCx P).tgt (revGerm eb) = t := by
          simpa only [ht] using germSrc_revGerm (X := orderCx P) eb
        have hsimp' : germTgt (orderCx P).src (orderCx P).tgt (revGerm eb) = s := by
          simpa only [hs] using germTgt_revGerm (X := orderCx P) eb
        rw [hsimp, hsimp']
        -- `(γ s ⁻¹ γ t)(γ t ⁻¹ γ s) ≃ []`
        have hcancelt : HtpyIn A j0 j0 (γ t ++ revPath (γ t)) [] :=
          htpyIn_append_revPath hγt (hγA t)
        have hmid : HtpyIn A (retrVert A j0 s) (retrVert A j0 s)
            (revPath (γ s) ++ (γ t ++ revPath (γ t)) ++ γ s)
            (revPath (γ s) ++ [] ++ γ s) :=
          hcancelt.congr_append (isPath_revPath hγs) hγs (pathIn_revPath (hγA s)) (hγA s)
        have hrw : (revPath (γ s) ++ γ t) ++ (revPath (γ t) ++ γ s) =
            revPath (γ s) ++ (γ t ++ revPath (γ t)) ++ γ s := by
          simp [List.append_assoc]
        rw [hrw]
        refine hmid.trans ?_
        simpa using htpyIn_revPath_append hγs (hγA s)
    have hcs' : c = germSrc (orderCx P).src (orderCx P).tgt eb := hcs
    subst hcs'
    have hglue : HtpyIn A (retrVert A j0 a) (retrVert A j0 b)
        (retrPath A γ p' ++ (retrGerm A γ eb ++ retrGerm A γ (revGerm eb)) ++ retrPath A γ q')
        (retrPath A γ p' ++ [] ++ retrPath A γ q') := by
      refine hkey.congr_append hPp' ?_ (pathIn_retrPath hγA p') (pathIn_retrPath hγA q')
      rw [hrevTgt] at hPq'
      exact hPq'
    have hrwl : retrPath A γ (p' ++ eb :: revGerm eb :: q') =
        retrPath A γ p' ++ (retrGerm A γ eb ++ retrGerm A γ (revGerm eb)) ++ retrPath A γ q' := by
      rw [retrPath_append]
      simp [retrPath, List.append_assoc]
    rw [hrwl, retrPath_append]
    simpa using hglue
  · -- a two-cell
    subst hlEq
    subst hl'Eq
    have hfront : PathIn U (p' ++ (orderCx P).att t) := pathIn_of_append_left hUl
    have hUp' : PathIn U p' := pathIn_of_append_left hfront
    have hUatt : PathIn U ((orderCx P).att t) := pathIn_of_append_right hfront
    have hUq' : PathIn U q' := pathIn_of_append_right hUl
    obtain ⟨c, hfrontPath, hq'⟩ := isPath_append_iff.mp hpl
    obtain ⟨d, hpc, hatt⟩ := isPath_append_iff.mp hfrontPath
    have hbase : d = t.1.1 := hatt.1
    have hbase' : c = t.1.1 := by
      obtain ⟨-, h2⟩ := hatt
      obtain ⟨-, h2'⟩ := h2
      obtain ⟨-, h3⟩ := h2'
      exact h3.symm
    subst hbase
    subst hbase'
    have hPp' : IsPath (orderCx P).src (orderCx P).tgt (retrPath A γ p')
        (retrVert A j0 a) (retrVert A j0 t.1.1) :=
      isPath_retrPath hJA hJmk hγpath hγnil hmix p' hpc hUp'
    have hPq' : IsPath (orderCx P).src (orderCx P).tgt (retrPath A γ q')
        (retrVert A j0 t.1.1) (retrVert A j0 b) :=
      isPath_retrPath hJA hJmk hγpath hγnil hmix q' hq' hUq'
    have hv1 := hUatt (⟨(t.1.1, t.1.2.1), t.2.1⟩, true) (by simp [orderCx])
    have hv2 := hUatt (⟨(t.1.2.1, t.1.2.2), t.2.2⟩, true) (by simp [orderCx])
    have hUx : U t.1.1 := hv1.1
    have hUy : U t.1.2.1 := hv1.2
    have hUz : U t.1.2.2 := hv2.2
    have hkey : HtpyIn A (retrVert A j0 t.1.1) (retrVert A j0 t.1.1)
        (retrPath A γ ((orderCx P).att t)) [] := by
      by_cases hallA : A t.1.1 ∧ A t.1.2.1 ∧ A t.1.2.2
      · -- the two-cell lies in `A`
        have hattA : PathIn A ((orderCx P).att t) := by
          intro e he
          have hmem : e = (⟨(t.1.1, t.1.2.1), t.2.1⟩, true) ∨
              e = (⟨(t.1.2.1, t.1.2.2), t.2.2⟩, true) ∨
              e = (⟨(t.1.1, t.1.2.2), le_trans t.2.1 t.2.2⟩, false) := by
            simpa [orderCx, or_assoc] using he
          rcases hmem with rfl | rfl | rfl
          · simp_all
          · simp_all
          · simp_all
        rw [retrPath_eq_self hattA, retrVert_of_mem hallA.1]
        refine HtpyIn.of_step ⟨⟨(orderCx P).att_isLoop t, rfl,
          Or.inr ⟨[], [], t, by simp, rfl⟩⟩, hattA, pathIn_nil A⟩
      · -- the two-cell lies in `B`
        have hallB : B t.1.1 ∧ B t.1.2.1 ∧ B t.1.2.2 := by
          by_cases hx : A t.1.1
          · by_cases hy : A t.1.2.1
            · have hz : ¬ A t.1.2.2 := fun hz => hallA ⟨hx, hy, hz⟩
              have h1 := hmix t.1.2.1 t.1.2.2 t.2.2 hUy hUz
              have h2 := hmix t.1.1 t.1.2.2 (le_trans t.2.1 t.2.2) hUx hUz
              rcases h1 with h1 | h1
              · simp_all
              · simp_all
            · grind
          · grind
        have hattB : PathIn B ((orderCx P).att t) := by
          intro e he
          have hmem : e = (⟨(t.1.1, t.1.2.1), t.2.1⟩, true) ∨
              e = (⟨(t.1.2.1, t.1.2.2), t.2.2⟩, true) ∨
              e = (⟨(t.1.1, t.1.2.2), le_trans t.2.1 t.2.2⟩, false) := by
            simpa [orderCx, or_assoc] using he
          rcases hmem with rfl | rfl | rfl
          · simp_all
          · simp_all
          · simp_all
        have htel := htpyIn_retrPath_of_pathIn_B (A := A) (γ := γ) hJA hJmk hγpath hγin hγnil hJsc hj0 ((orderCx P).att t) ((orderCx P).att_isLoop t) hattB hallB.1 hallB.1
        refine htel.trans ?_
        have hγx : IsPath (orderCx P).src (orderCx P).tgt (γ t.1.1) j0
            (retrVert A j0 t.1.1) := isPath_gamma hJA hJmk hγpath hγnil hallB.1
        exact htpyIn_revPath_append hγx (hγA t.1.1)
    have hglue : HtpyIn A (retrVert A j0 a) (retrVert A j0 b)
        (retrPath A γ p' ++ retrPath A γ ((orderCx P).att t) ++ retrPath A γ q')
        (retrPath A γ p' ++ [] ++ retrPath A γ q') :=
      hkey.congr_append hPp' hPq' (pathIn_retrPath hγA p') (pathIn_retrPath hγA q')
    rw [retrPath_append, retrPath_append, retrPath_append]
    simpa using hglue

include hJA hJmk hγpath hγin hγnil in
/-- The retraction respects homotopies inside `U`. -/
theorem htpyIn_retrPath_of_htpyIn
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    (hJsc : SimplyConnectedIn J) (hj0 : J j0) {a b : P}
    {p q : List ((orderCx P).E × Bool)} (h : HtpyIn U a b p q) :
    HtpyIn A (retrVert A j0 a) (retrVert A j0 b) (retrPath A γ p) (retrPath A γ q) := by
  induction h with
  | refl => exact HtpyIn.refl _
  | tail _ hstep ih =>
      refine ih.trans ?_
      rcases hstep with hs | hs
      · exact htpyIn_retrPath_of_stepIn hJA hJmk hγpath hγin hγnil hmix hJsc hj0 hs
      · exact (htpyIn_retrPath_of_stepIn hJA hJmk hγpath hγin hγnil hmix hJsc hj0 hs).symm

end Gluing

/-- **The gluing step for injectivity on path classes.**  If `U = A ∪ B`, no comparability inside
`U` is mixed, and the intersection `J = A ∩ B` is nonempty, connected and simply connected, then
a loop inside `A` which is null-homotopic inside `U` is null-homotopic inside `A`.  Nothing is
assumed about `B`. -/
theorem injIn_union_of_unmixed {A B U J : P → Prop}
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    (hJdef : ∀ x, J x ↔ (A x ∧ B x))
    (hJconn : ConnectedIn J) (hJsc : SimplyConnectedIn J)
    {j0 : P} (hj0 : J j0) :
    InjIn U A := by
  have hJA  := fun x h => ((hJdef x).1 h).1
  have hJmk  := fun x h h' => (hJdef x).2 ⟨h, h'⟩
  -- choose the paths `γ`
  have hex : ∀ u : P, ∃ g : List ((orderCx P).E × Bool),
      (J u → IsPath (orderCx P).src (orderCx P).tgt g j0 u) ∧ PathIn J g ∧ (¬ J u → g = []) := by
    intro u
    by_cases hu : J u
    · obtain ⟨g, hg, hgin⟩ := hJconn j0 u hj0 hu
      exact ⟨g, fun _ => hg, hgin, fun h => absurd hu h⟩
    · exact ⟨[], fun h => absurd h hu, pathIn_nil J, fun _ => rfl⟩
  choose γ hγpath hγin hγnil using hex
  intro v l hv hp hl hnull
  have h := htpyIn_retrPath_of_htpyIn (J := J) (γ := γ) hJA hJmk
    hγpath hγin hγnil hmix hJsc hj0 hnull
  rw [retrPath_eq_self hl, retrVert_of_mem hv] at h
  simpa using h

/-! ### The initial step: a monotone retraction -/

/-- A monotone map that fixes the vertices of `B` returns a path of `B` unchanged. -/
theorem mapPath_liftPathIn_of_fix {C B : P → Prop} (f : {x : P // C x} → P) (hf : Monotone f)
    (hfix : ∀ z : {x : P // C x}, B z.1 → f z = z.1) :
    ∀ (l : List ((orderCx P).E × Bool)) (hl : PathIn C l), PathIn B l →
      mapPath (orderCxMap f hf) (liftPathIn l hl) = l
  | [], _, _ => rfl
  | e :: t, hl, hB => by
      have hrest : mapPath (orderCxMap f hf) (liftPathIn t (pathIn_of_cons hl).2) = t :=
        mapPath_liftPathIn_of_fix f hf hfix t (pathIn_of_cons hl).2 (pathIn_of_cons hB).2
      obtain ⟨he1, he2⟩ := (pathIn_of_cons hB).1
      obtain ⟨hc1, hc2⟩ := (pathIn_of_cons hl).1
      simp only [liftPathIn, mapPath, List.map_cons, List.cons.injEq]
      constructor
      · refine Prod.ext ?_ rfl
        refine Subtype.ext ?_
        refine Prod.ext ?_ ?_
        · exact hfix ⟨e.1.1.1, hc1⟩ he1
        · exact hfix ⟨e.1.1.2, hc2⟩ he2
      · exact hrest

/-- **A monotone retraction is injective on path classes.**  If the subposet `C` retracts
monotonically onto a smaller subposet `B`, fixing `B` pointwise, then a loop inside `B` that is
null-homotopic inside `C` is null-homotopic inside `B`. -/
theorem injIn_of_monotone_retraction {C B : P → Prop} (hBC : ∀ x, B x → C x)
    (f : {x : P // C x} → P) (hf : Monotone f) (hfB : ∀ z, B (f z))
    (hfix : ∀ z : {x : P // C x}, B z.1 → f z = z.1) :
    InjIn C B := by
  intro v l hv hp hl hnull
  have hvC  := hBC v hv
  have hlC  := pathIn_mono hBC hl
  have hlift  :=
    htpy_lift_of_htpyIn hnull hvC hvC hlC (pathIn_nil C)
  have hpush := htpyIn_mapPath (C := B) f hf hfB hlift
  rw [mapPath_liftPathIn_of_fix f hf hfix l hlC hl, hfix ⟨v, hvC⟩ hv] at hpush
  simpa [mapPath, liftPathIn] using hpush

/-! ### Passing to an increasing exhaustion -/

/-- **Finiteness of null-homotopies.**  A homotopy of the ambient complex only uses finitely many
cells, so it takes place inside one member of an increasing exhaustion. -/
theorem exists_htpyIn_of_htpy {D : ℕ → P → Prop} (hmono : ∀ m n, m ≤ n → ∀ x, D m x → D n x)
    (hcov : ∀ x : P, ∃ n, D n x) {a b : P} {p q : List ((orderCx P).E × Bool)}
    (h : Htpy (orderCx P) a b p q) : ∃ n, HtpyIn (D n) a b p q := by
  have hpath : ∀ l : List ((orderCx P).E × Bool), ∃ n, PathIn (D n) l := by
    intro l
    induction l with
    | nil => exact ⟨0, pathIn_nil _⟩
    | cons e t ih =>
        obtain ⟨n, hn⟩ := ih
        obtain ⟨n1, hn1⟩ := hcov e.1.1.1
        obtain ⟨n2, hn2⟩ := hcov e.1.1.2
        refine ⟨max n (max n1 n2), pathIn_cons ⟨?_, ?_⟩ ?_⟩
        · grind
        · grind
        · exact pathIn_mono (hmono n _ (le_max_left _ _)) hn
  induction h with
  | refl => exact ⟨0, Relation.ReflTransGen.refl⟩
  | @tail u v _ hstep ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨m1, hm1⟩ := hpath u
      obtain ⟨m2, hm2⟩ := hpath v
      refine ⟨max n (max m1 m2), ?_⟩
      refine (HtpyIn.mono (hmono n _ (le_max_left _ _)) hn).trans ?_
      have hu  :=
        pathIn_mono (hmono m1 _ (le_trans (le_max_left m1 m2) (le_max_right n _))) hm1
      have hv  :=
        pathIn_mono (hmono m2 _ (le_trans (le_max_right m1 m2) (le_max_right n _))) hm2
      rcases hstep with hs | hs
      · exact HtpyIn.of_step ⟨hs, hu, hv⟩
      · exact (HtpyIn.of_step ⟨hs, hv, hu⟩).symm

end Comb
end FiniteChains

namespace FiniteChains
namespace Comb

universe u

variable {P Q R : Type u} [Preorder P] [Preorder Q] [Preorder R]

/-- A homotopy inside the whole poset is an ordinary homotopy. -/
theorem htpyIn_true_iff {a b : P} {p q : List ((orderCx P).E × Bool)} :
    HtpyIn (fun _ : P => True) a b p q ↔ Htpy (orderCx P) a b p q := by
  constructor
  · exact HtpyIn.htpy
  · intro h
    refine Relation.ReflTransGen.mono (fun x y hs => ?_) _ _ h
    exact hs.imp (fun h => ⟨h, fun _ _ => ⟨trivial, trivial⟩, fun _ _ => ⟨trivial, trivial⟩⟩)
      (fun h => ⟨h, fun _ _ => ⟨trivial, trivial⟩, fun _ _ => ⟨trivial, trivial⟩⟩)

/-- A monotone map followed by a monotone left inverse returns an edge path unchanged. -/
theorem mapPath_comp_eq_self {f : Q → P} (hf : Monotone f) {g : P → Q} (hg : Monotone g)
    (hgf : ∀ y, g (f y) = y) :
    ∀ l : List ((orderCx Q).E × Bool),
      mapPath (orderCxMap g hg) (mapPath (orderCxMap f hf) l) = l
  | [] => rfl
  | e :: t => by
      simp only [mapPath, List.map_cons, List.cons.injEq]
      refine ⟨?_, ?_⟩
      · refine Prod.ext ?_ rfl
        refine Subtype.ext (Prod.ext ?_ ?_)
        · exact hgf e.1.1.1
        · exact hgf e.1.1.2
      · simpa [mapPath] using mapPath_comp_eq_self hf hg hgf t

/-- Simple connectedness transfers along an order isomorphism. -/
theorem simplyConnected_orderCx_of_orderIso (e : P ≃o Q) (h : SimplyConnected (orderCx Q)) :
    SimplyConnected (orderCx P) := by
  intro a p hp
  have hmono : Monotone e := fun _ _ hxy => e.monotone hxy
  have hmono' : Monotone e.symm := fun _ _ hxy => e.symm.monotone hxy
  have himg := h (e a) (mapPath (orderCxMap e hmono) p)
    (isPath_mapPath (orderCxMap e hmono) hp)
  have hpush := mapPath_htpy (orderCxMap e.symm hmono') himg
  rw [mapPath_comp_eq_self hmono hmono' (fun y => e.symm_apply_apply y) p] at hpush
  simpa [mapPath] using hpush

/-- Connectivity transfers along an order isomorphism. -/
theorem isConnected_orderCx_of_orderIso (e : P ≃o Q) (h : IsConnected (orderCx Q)) :
    IsConnected (orderCx P) := by
  intro a b
  have hmono' : Monotone e.symm := fun _ _ hxy => e.symm.monotone hxy
  obtain ⟨l, hl⟩ := h (e a) (e b)
  refine ⟨mapPath (orderCxMap e.symm hmono') l, ?_⟩
  have := isPath_mapPath (orderCxMap e.symm hmono') hl
  simpa [e.symm_apply_apply] using this

/-- The lift of the image of an edge path, pushed back by a monotone retraction, is the original
path. -/
theorem mapPath_liftPathIn_mapPath {Bp : P → Prop} {f : Q → P} (hf : Monotone f)
    (hfB : ∀ y, Bp (f y)) {g : {z : P // Bp z} → Q} (hg : Monotone g)
    (hgf : ∀ y, g ⟨f y, hfB y⟩ = y) :
    ∀ (l : List ((orderCx Q).E × Bool)) (hl : PathIn Bp (mapPath (orderCxMap f hf) l)),
      mapPath (orderCxMap g hg) (liftPathIn (mapPath (orderCxMap f hf) l) hl) = l
  | [], _ => rfl
  | e :: t, hl => by
      have hrest := mapPath_liftPathIn_mapPath hf hfB hg hgf t (pathIn_of_cons hl).2
      simp only [mapPath, List.map_cons, liftPathIn, List.cons.injEq]
      refine ⟨?_, ?_⟩
      · refine Prod.ext ?_ rfl
        refine Subtype.ext (Prod.ext ?_ ?_)
        · exact hgf e.1.1.1
        · exact hgf e.1.1.2
      · simpa [mapPath] using hrest

/-- The image of an edge path under a monotone map with values in `Bp` lies inside `Bp`. -/
theorem pathIn_mapPath_of_image {Bp : P → Prop} {f : Q → P} (hf : Monotone f)
    (hfB : ∀ y, Bp (f y)) (l : List ((orderCx Q).E × Bool)) :
    PathIn Bp (mapPath (orderCxMap f hf) l) := by
  intro e he
  simp only [mapPath, List.mem_map] at he
  obtain ⟨x, -, rfl⟩ := he
  exact ⟨hfB _, hfB _⟩

/-- **From injectivity on path classes to injectivity on loops.**  If the image of a monotone map
`f` with a monotone retraction `g` is injective on path classes inside the whole poset, then a
loop of the source which becomes null-homotopic in the target is null-homotopic. -/
theorem htpy_nil_of_injIn {Bp : P → Prop} (hinj : InjIn (fun _ : P => True) Bp)
    {f : Q → P} (hf : Monotone f) (hfB : ∀ y, Bp (f y))
    {g : {z : P // Bp z} → Q} (hg : Monotone g) (hgf : ∀ y, g ⟨f y, hfB y⟩ = y)
    {y : Q} {p : List ((orderCx Q).E × Bool)}
    (hp : IsPath (orderCx Q).src (orderCx Q).tgt p y y)
    (h : Htpy (orderCx P) (f y) (f y) (mapPath (orderCxMap f hf) p) []) :
    Htpy (orderCx Q) y y p [] := by
  have hpB  := pathIn_mapPath_of_image hf hfB p
  have hloop  :=
    isPath_mapPath (orderCxMap f hf) hp
  have hIn  :=
    hinj (f y) _ (hfB y) hloop hpB (htpyIn_true_iff.mpr h)
  have hlift  :=
    htpy_lift_of_htpyIn hIn (hfB y) (hfB y) hpB (pathIn_nil Bp)
  have hpush := mapPath_htpy (orderCxMap g hg) hlift
  rw [mapPath_liftPathIn_mapPath hf hfB hg hgf p hpB] at hpush
  simp at hpush
  rw [hgf y] at hpush
  simpa [mapPath, liftPathIn] using hpush

/-- **Injectivity of the induced map of fundamental groups.** -/
theorem pi1Map_injective_of_injIn {Bp : P → Prop} (hinj : InjIn (fun _ : P => True) Bp)
    {f : Q → P} (hf : Monotone f) (hfB : ∀ y, Bp (f y))
    {g : {z : P // Bp z} → Q} (hg : Monotone g) (hgf : ∀ y, g ⟨f y, hfB y⟩ = y) (y : Q) :
    Function.Injective (Comb.pi1Map (orderCxMap f hf) y) := by
  refine (injective_iff_map_eq_one _).mpr ?_
  intro c hc
  induction c using Quotient.inductionOn with
  | h p =>
      have h  :=
        Quotient.exact hc
      exact Quotient.sound (htpy_nil_of_injIn hinj hf hfB hg hgf p.2 h)

end Comb
end FiniteChains

namespace FiniteChains
namespace Comb

universe u v

variable {P : Type u} [Preorder P] {G : Type v} [Group G]

/-! ### Cocycles on a preorder -/

/-- A cocycle on a preorder with values in a group: a value for every ordered pair, required to
be multiplicative along chains.  On comparable pairs this is the same thing as a functor from
`P`, viewed as a category, to `G`; the values on incomparable pairs are irrelevant. -/
structure OrdCocycle (P : Type u) [Preorder P] (G : Type v) [Group G] where
  /-- The value on a pair of elements. -/
  val : P → P → G
  /-- Multiplicativity along a chain. -/
  comp : ∀ {a b c : P}, a ≤ b → b ≤ c → val a b * val b c = val a c

namespace OrdCocycle

variable (c : OrdCocycle P G)

@[simp] theorem val_refl (a : P) : c.val a a = 1 := by
  have h := c.comp (le_refl a) (le_refl a)
  simpa using h

/-- The value of the cocycle on an oriented edge of the order complex. -/
def readGerm (g : (orderCx P).E × Bool) : G :=
  if g.2 then c.val g.1.1.1 g.1.1.2 else (c.val g.1.1.1 g.1.1.2)⁻¹

@[simp] theorem readGerm_ordPos {a b : P} (h : a ≤ b) : c.readGerm (ordPos h) = c.val a b := rfl

@[simp] theorem readGerm_ordNeg {a b : P} (h : a ≤ b) :
    c.readGerm (ordNeg h) = (c.val a b)⁻¹ := rfl

@[simp] theorem readGerm_revGerm (g : (orderCx P).E × Bool) :
    c.readGerm (revGerm (X := orderCx P) g) = (c.readGerm g)⁻¹ := by
  obtain ⟨e, b⟩ := g
  cases b <;> simp [readGerm, revGerm]

/-- The value of the cocycle on an edge path: the product of the values of its edges. -/
def readPath (l : List ((orderCx P).E × Bool)) : G := (l.map c.readGerm).prod

@[simp] theorem readPath_nil : c.readPath [] = 1 := rfl

@[simp] theorem readPath_cons (g : (orderCx P).E × Bool) (l : List ((orderCx P).E × Bool)) :
    c.readPath (g :: l) = c.readGerm g * c.readPath l := rfl

@[simp] theorem readPath_append (l l' : List ((orderCx P).E × Bool)) :
    c.readPath (l ++ l') = c.readPath l * c.readPath l' := by
  simp [readPath]

@[simp] theorem readPath_att (t : OrdTri P) : c.readPath ((orderCx P).att t) = 1 := by
  obtain ⟨⟨a, b, d⟩, hab, hbd⟩ := t
  show c.readGerm (ordPos hab) * (c.readGerm (ordPos hbd) *
    (c.readGerm (ordNeg (hab.trans hbd)) * 1)) = 1
  rw [readGerm_ordPos, readGerm_ordPos, readGerm_ordNeg, mul_one, ← mul_assoc, c.comp hab hbd,
    mul_inv_cancel]

/-- An elementary cancellation does not change the value of a path. -/
theorem readPath_cancels {l l' : List ((orderCx P).E × Bool)}
    (h : Cancels (orderCx P) l l') : c.readPath l = c.readPath l' := by
  rcases h with ⟨p, q, g, hl, hl'⟩ | ⟨p, q, t, hl, hl'⟩
  · simp_all
  · simp_all

/-- Homotopic paths have the same value. -/
theorem readPath_htpy {a b : P} {l l' : List ((orderCx P).E × Bool)}
    (h : Htpy (orderCx P) a b l l') : c.readPath l = c.readPath l' := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      rcases hstep with hs | hs
      · exact ih.trans (c.readPath_cancels hs.2.2)
      · exact ih.trans (c.readPath_cancels hs.2.2).symm

/-- **The reading homomorphism** attached to a cocycle: the monodromy of the associated flat
bundle, read on edge loops. -/
def monodromy (x : P) : Pi1 (orderCx P) x →* G where
  toFun := Quotient.lift (fun p : Loop (orderCx P) x => c.readPath p.1)
    (fun _ _ h => c.readPath_htpy h)
  map_one' := rfl
  map_mul' := by
    rintro ⟨p⟩ ⟨q⟩
    exact c.readPath_append p.1 q.1

@[simp] theorem monodromy_mk (x : P) (p : Loop (orderCx P) x) :
    c.monodromy x (Pi1.mk p) = c.readPath p.1 := rfl

end OrdCocycle

/-! ### The cone lemma -/

/-- **A loop inside a subposet with a largest element is null-homotopic.**  The subposet need
not be an interval: all that is used is an element of `A` above every element of `A`. -/
theorem htpy_nil_of_pathIn_le_top {A : P → Prop} {d : P} (hd : A d)
    (hAd : ∀ x, A x → x ≤ d) {v : P} (hv : A v) {l : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt l v v) (hl : PathIn A l) :
    Htpy (orderCx P) v v l [] := by
  refine htpy_nil_of_pathIn ?_ hv hp hl
  refine simplyConnected_orderCx ⟨d, hd⟩ id (fun x => le_refl x)
    (fun x => hAd x.1 x.2) ?_
  intro x y h
  exact h

end Comb
end FiniteChains
end

namespace FiniteChains
namespace Comb

universe u

variable {P Q : Type u} [Preorder P] [Preorder Q]

/-- **The naturality homotopy for a single edge, traversed forwards.** -/
theorem htpy_square_pos {f g : P → Q} (hf : Monotone f) (hg : Monotone g)
    (hfg : ∀ x, f x ≤ g x) {a b : P} (h : a ≤ b) :
    Htpy (orderCx Q) (f a) (g b) [ordPos (hf h), ordPos (hfg b)]
      [ordPos (hfg a), ordPos (hg h)] :=
  (htpy_orderCx_tri (hf h) (hfg b)).trans (htpy_orderCx_tri (hfg a) (hg h)).symm

/-- **The naturality homotopy for a single edge, traversed backwards.** -/
theorem htpy_square_neg {f g : P → Q} (hf : Monotone f) (hg : Monotone g)
    (hfg : ∀ x, f x ≤ g x) {a b : P} (h : a ≤ b) :
    Htpy (orderCx Q) (f b) (g a) [ordNeg (hf h), ordPos (hfg a)]
      [ordPos (hfg b), ordNeg (hg h)] := by
  -- multiply the forward square by the inverse edges on both sides
  have hpos := htpy_square_pos hf hg hfg h
  -- `[f b, f a]⁻¹ · ([f a, f b] [f b, g b]) · [g a, g b]⁻¹ ≃ [f b, g b] ... `
  have h1  :=
    hpos.congr_append (isPath_ordNeg (hf h)) (isPath_ordNeg (hg h))
  have h2  :=
    (htpy_ordNeg_ordPos (hf h)).congr_append (isPath_nil' (f b))
      (show IsPath (orderCx Q).src (orderCx Q).tgt [ordPos (hfg b), ordNeg (hg h)] (f b) (g a)
        from ⟨rfl, rfl, rfl⟩)
  have h3  :=
    (htpy_ordPos_ordNeg (hg h)).congr_append
      (show IsPath (orderCx Q).src (orderCx Q).tgt [ordNeg (hf h), ordPos (hfg a)] (f b) (g a)
        from ⟨rfl, rfl, rfl⟩) (isPath_nil' (g a))
  simp at h1 h2 h3 ⊢
  exact (h3.symm.trans h1.symm).trans h2

/-- **The naturality homotopy.**  For two monotone maps with `f ≤ g` pointwise, the image of a
path under `f` followed by the edge at its end is homotopic to the edge at its start followed by
the image under `g`. -/
theorem htpy_mapPath_le {f g : P → Q} (hf : Monotone f) (hg : Monotone g)
    (hfg : ∀ x, f x ≤ g x) :
    ∀ (p : List ((orderCx P).E × Bool)) {u v : P},
      IsPath (orderCx P).src (orderCx P).tgt p u v →
      Htpy (orderCx Q) (f u) (g v)
        (mapPath (orderCxMap f hf) p ++ [ordPos (hfg v)])
        ([ordPos (hfg u)] ++ mapPath (orderCxMap g hg) p) := by
  intro p
  induction p with
  | nil =>
      intro u v hp
      cases hp
      exact Htpy.refl _
  | cons eb p ih =>
      rintro u v ⟨hu, hrest⟩
      obtain ⟨⟨⟨a, b⟩, hab⟩, tag⟩ := eb
      cases tag with
      | true =>
          have hua  := hu
          subst hua
          have hrest'  := hrest
          have hih := ih hrest'
          -- `[f a, f b] · (image of p under f) · [f v, g v]`
          have h1  :=
            Htpy.append_congr (isPath_ordPos (hf hab))
              (isPath_append_iff.mpr ⟨f v, isPath_mapPath (orderCxMap f hf) hrest',
                isPath_ordPos (hfg v)⟩) (Htpy.refl _) hih
          have h2  :=
            Htpy.append_congr
              (show IsPath (orderCx Q).src (orderCx Q).tgt
                [ordPos (hf hab), ordPos (hfg b)] (f u) (g b) from ⟨rfl, rfl, rfl⟩)
              (isPath_mapPath (orderCxMap g hg) hrest')
              (htpy_square_pos hf hg hfg hab) (Htpy.refl _)
          have hgoal := h1.trans h2
          simpa [mapPath, orderCxMap, ordPos, ordNeg, List.append_assoc] using hgoal
      | false =>
          have hub  := hu
          subst hub
          have hrest'  := hrest
          have hih := ih hrest'
          have h1  :=
            Htpy.append_congr (isPath_ordNeg (hf hab))
              (isPath_append_iff.mpr ⟨f v, isPath_mapPath (orderCxMap f hf) hrest',
                isPath_ordPos (hfg v)⟩) (Htpy.refl _) hih
          have h2  :=
            Htpy.append_congr
              (show IsPath (orderCx Q).src (orderCx Q).tgt
                [ordNeg (hf hab), ordPos (hfg a)] (f u) (g a) from ⟨rfl, rfl, rfl⟩)
              (isPath_mapPath (orderCxMap g hg) hrest')
              (htpy_square_neg hf hg hfg hab) (Htpy.refl _)
          have hgoal := h1.trans h2
          simpa [mapPath, orderCxMap, ordPos, ordNeg, List.append_assoc] using hgoal

/-- **The conjugation form of the naturality homotopy for a loop.**  The image of a loop under
`g` is homotopic to the image under `f` conjugated by the edge at the basepoint. -/
theorem htpy_loop_mapPath_le {f g : P → Q} (hf : Monotone f) (hg : Monotone g)
    (hfg : ∀ x, f x ≤ g x) {u : P} {p : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p u u) :
    Htpy (orderCx Q) (g u) (g u) (mapPath (orderCxMap g hg) p)
      ([ordNeg (hfg u)] ++ mapPath (orderCxMap f hf) p ++ [ordPos (hfg u)]) := by
  have hnat := htpy_mapPath_le hf hg hfg p hp
  have hfp  :=
    isPath_mapPath (orderCxMap f hf) hp
  have hgp  :=
    isPath_mapPath (orderCxMap g hg) hp
  -- prepend `[g u, f u]` to the naturality homotopy and cancel a backtrack
  have h1  :=
    hnat.congr_append (isPath_ordNeg (hfg u)) (isPath_nil' (g u))
  have h2  :=
    (htpy_ordNeg_ordPos (hfg u)).congr_append (isPath_nil' (g u)) hgp
  simp at h1 h2 ⊢
  exact (h2.symm.trans h1.symm)

end Comb
end FiniteChains

namespace FiniteChains
namespace Comb

universe u

open Nerve

variable {X Sg : Type u} [Preorder X] [Preorder Sg]

/-- The poset underlying the mapping cylinder of a monotone map `a : Σ →o X`. -/
def CylP (_a : Sg →o X) : Type u := X ⊕ Sg

namespace CylP

variable (a : Sg →o X)

/-- The order of the mapping cylinder: the two ends keep their own orders, and an element of the
outer end lies below the elements of `X` above its image. -/
protected def le : CylP a → CylP a → Prop
  | Sum.inl x, Sum.inl y => x ≤ y
  | Sum.inl _, Sum.inr _ => False
  | Sum.inr s, Sum.inl y => a s ≤ y
  | Sum.inr s, Sum.inr t => s ≤ t

instance : Preorder (CylP a) where
  le := CylP.le a
  le_refl p := by
    cases p with
    | inl x => exact le_refl x
    | inr s => exact le_refl s
  le_trans p q r hpq hqr := by
    cases p with
    | inl x =>
        cases q with
        | inl y =>
            cases r with
            | inl z => exact le_trans hpq hqr
            | inr t => exact hqr.elim
        | inr t => exact hpq.elim
    | inr s =>
        cases q with
        | inl y =>
            cases r with
            | inl z => exact le_trans hpq hqr
            | inr t => exact hqr.elim
        | inr t =>
            cases r with
            | inl z => exact le_trans (a.monotone hpq) hqr
            | inr u => exact le_trans hpq hqr

end CylP

variable (a : Sg →o X)

/-- The inclusion of the base. -/
def cylIn (x : X) : CylP a := Sum.inl x

/-- The inclusion of the **outer end**. -/
def cylOuter (s : Sg) : CylP a := Sum.inr s

/-- The retraction of the cylinder onto its base. -/
def cylRetr : CylP a → X := Sum.elim id a

@[simp] theorem cylRetr_cylIn (x : X) : cylRetr a (cylIn a x) = x := rfl

@[simp] theorem cylRetr_cylOuter (s : Sg) : cylRetr a (cylOuter a s) = a s := rfl

theorem cylIn_injective : Function.Injective (cylIn a) := fun _ _ h => Sum.inl_injective h

theorem cylIn_monotone : Monotone (cylIn a) := fun _ _ h => h

theorem cylRetr_monotone : Monotone (cylRetr a) := by
  intro p q hpq
  cases p with
  | inl x =>
      cases q with
      | inl y => exact hpq
      | inr t => exact hpq.elim
  | inr s =>
      cases q with
      | inl y => exact hpq
      | inr t => exact a.monotone hpq

/-- The composite `ι ∘ r`, the "collapse the cylinder onto its base" map. -/
def cylCollapse : CylP a → CylP a := fun p => cylIn a (cylRetr a p)

theorem cylCollapse_monotone : Monotone (cylCollapse a) :=
  (cylIn_monotone a).comp (cylRetr_monotone a)

/-- The identity lies below the collapse: this is what makes the prism operator a chain
homotopy between them. -/
theorem le_cylIn_cylRetr (p : CylP a) : p ≤ cylCollapse a p := by
  cases p with
  | inl x => exact le_refl x
  | inr s => exact le_refl (a s)

/-! ### The chain homotopy -/

end Comb
end FiniteChains

namespace FiniteChains
namespace Comb

universe u v

/-! ### Pullback of a cocycle -/

section Comap

variable {P Q : Type u} [Preorder P] [Preorder Q] {G : Type v} [Group G]

/-- A cocycle pulls back along a monotone map. -/
def OrdCocycle.comap (f : P → Q) (hf : Monotone f) (c : OrdCocycle Q G) : OrdCocycle P G where
  val a b := c.val (f a) (f b)
  comp hab hbc := c.comp (hf hab) (hf hbc)

@[simp] theorem OrdCocycle.comap_val (f : P → Q) (hf : Monotone f) (c : OrdCocycle Q G)
    (a b : P) : (c.comap f hf).val a b = c.val (f a) (f b) := rfl

end Comap

/-! ### The poset with adjoined cone points -/

variable {P : Type u} [Preorder P] {T : Type u}

/-- The preorder `P` with a new point above the down-closure of `S t` for every `t : T`. -/
def ConeAdj (_S : T → P → Prop) : Type u := P ⊕ T

namespace ConeAdj

variable {S : T → P → Prop}

/-- The inclusion of the original poset. -/
def inc (p : P) : ConeAdj S := Sum.inl p

/-- The cone point attached to `t`. -/
def apex (t : T) : ConeAdj S := Sum.inr t

/-- The order of `ConeAdj`: the old order on `P`, a new point above everything below some
element of `S t`, and no relation between two distinct new points. -/
protected def le (S : T → P → Prop) : ConeAdj S → ConeAdj S → Prop
  | Sum.inl p, Sum.inl q => p ≤ q
  | Sum.inl p, Sum.inr t => ∃ r, S t r ∧ p ≤ r
  | Sum.inr _, Sum.inl _ => False
  | Sum.inr t, Sum.inr t' => t = t'

instance : Preorder (ConeAdj S) where
  le := ConeAdj.le S
  le_refl p := by
    cases p with
    | inl x => exact le_refl x
    | inr t => rfl
  le_trans p q r hpq hqr := by
    cases p with
    | inl x =>
        cases q with
        | inl y =>
            cases r with
            | inl z => exact le_trans hpq hqr
            | inr t =>
                obtain ⟨w, hw, hyw⟩ := hqr
                exact ⟨w, hw, le_trans hpq hyw⟩
        | inr t =>
            cases r with
            | inl z => exact hqr.elim
            | inr t' =>
                cases hqr
                exact hpq
    | inr t =>
        cases q with
        | inl y => exact hpq.elim
        | inr t' =>
            cases r with
            | inl z => exact hqr.elim
            | inr t'' => exact hpq.trans hqr

@[simp] theorem inc_le_inc {p q : P} : (inc p : ConeAdj S) ≤ inc q ↔ p ≤ q := Iff.rfl

@[simp] theorem inc_le_apex {p : P} {t : T} :
    (inc p : ConeAdj S) ≤ apex t ↔ ∃ r, S t r ∧ p ≤ r := Iff.rfl


theorem inc_monotone : Monotone (inc : P → ConeAdj S) := fun _ _ h => h

/-- The defining relation: an element of `S t` lies under the cone point `t`. -/
theorem inc_le_apex_of_mem {p : P} {t : T} (h : S t p) : (inc p : ConeAdj S) ≤ apex t :=
  ⟨p, h, le_refl p⟩

omit [Preorder P] in
theorem inc_injective : Function.Injective (inc : P → ConeAdj S) := fun _ _ h => Sum.inl_injective h

end ConeAdj

/-! ### Extending a cocycle over the cone points -/

variable {G : Type v} [Group G] {S : T → P → Prop}

/-- The extension of a cocycle over the adjoined cone points, given a trivialisation `h t` of
the cocycle under each cone point. -/
def OrdCocycle.coneAdjVal (c : OrdCocycle P G) (h : T → P → G) :
    ConeAdj S → ConeAdj S → G
  | Sum.inl p, Sum.inl q => c.val p q
  | Sum.inl p, Sum.inr t => h t p
  | Sum.inr _, Sum.inl _ => 1
  | Sum.inr _, Sum.inr _ => 1

/-- **Extension of a cocycle over the cone points.**  The hypothesis is that `h t` trivialises
the cocycle on the elements lying under the cone point `t`. -/
def OrdCocycle.coneAdj (c : OrdCocycle P G) (h : T → P → G)
    (hh : ∀ (t : T) {p q : P}, p ≤ q → (ConeAdj.inc q : ConeAdj S) ≤ ConeAdj.apex t →
      c.val p q * h t q = h t p) :
    OrdCocycle (ConeAdj S) G where
  val := c.coneAdjVal h
  comp := by
    rintro (p | t) (q | t') (r | t'') hpq hqr
    · exact c.comp hpq hqr
    · exact hh t'' hpq hqr
    · exact absurd hqr (fun x => x)
    · cases (hqr : t' = t'')
      show h t' p * 1 = h t' p
      rw [mul_one]
    · exact absurd hpq (fun x => x)
    · exact absurd hpq (fun x => x)
    · exact absurd hqr (fun x => x)
    · show (1 : G) * 1 = 1
      rw [mul_one]

@[simp] theorem OrdCocycle.coneAdj_val_inc (c : OrdCocycle P G) (h : T → P → G) (hh) (p q : P) :
    (c.coneAdj (S := S) h hh).val (ConeAdj.inc p) (ConeAdj.inc q) = c.val p q := rfl

@[simp] theorem OrdCocycle.coneAdj_val_apex (c : OrdCocycle P G) (h : T → P → G) (hh)
    (p : P) (t : T) :
    (c.coneAdj (S := S) h hh).val (ConeAdj.inc p) (ConeAdj.apex t) = h t p := rfl

/-! ### The cone lemma in the form used below -/

/-- **A loop all of whose edges lie under a fixed element is null-homotopic.** -/
theorem htpy_nil_of_pathIn_le {Pp : Type u} [Preorder Pp] (d : Pp) {v : Pp} (hv : v ≤ d)
    {l : List ((orderCx Pp).E × Bool)}
    (hp : IsPath (orderCx Pp).src (orderCx Pp).tgt l v v)
    (hl : PathIn (fun x => x ≤ d) l) :
    Htpy (orderCx Pp) v v l [] :=
  htpy_nil_of_pathIn_le_top (A := fun x => x ≤ d) (le_refl d) (fun _ hx => hx) hv hp hl

end Comb
end FiniteChains

namespace FiniteChains
namespace PresModel

open Comb

universe u

variable {α J : Type u}

/-! ### Two elementary congruences for edges of an order complex -/

theorem ordPos_congr {P : Type u} [Preorder P] {a b a' b' : P} (ha : a = a') (hb : b = b')
    (h : a ≤ b) (h' : a' ≤ b') : ordPos h = ordPos h' := by simp_all

theorem ordNeg_congr {P : Type u} [Preorder P] {a b a' b' : P} (ha : a = a') (hb : b = b')
    (h : a ≤ b) (h' : a' ≤ b') : ordNeg h = ordNeg h' := by simp_all

/-! ### The subdivided rose -/

/-- The cells of the subdivided rose: the base vertex, the midpoint of the loop of a generator,
and the two halves of that loop. -/
inductive Rose (α : Type u) : Type u
  | base : Rose α
  | mid (i : α) : Rose α
  | edg (i : α) (b : Bool) : Rose α

namespace Rose

/-- The face order of the subdivided rose. -/
protected def le : Rose α → Rose α → Prop
  | base, base => True
  | base, edg _ _ => True
  | mid i, mid i' => i = i'
  | mid i, edg i' _ => i = i'
  | edg i b, edg i' b' => i = i' ∧ b = b'
  | _, _ => False

instance : Preorder (Rose α) where
  le := Rose.le
  le_refl x := by
    cases x with
    | base => exact trivial
    | mid i => exact rfl
    | edg i b => exact ⟨rfl, rfl⟩
  le_trans a b c hab hbc := by
    cases a <;> cases b <;> cases c <;> simp_all [Rose.le]

@[simp] theorem base_le_edg (i : α) (b : Bool) : (base : Rose α) ≤ edg i b := trivial

@[simp] theorem mid_le_edg (i : α) (b : Bool) : (mid i : Rose α) ≤ edg i b := rfl

end Rose

/-! ### The subdivided attaching circles -/

/-- The four elements of the circle attached to one letter of a relator: the corner in front of
the letter, the midpoint of the letter, and the two halves of the letter. -/
inductive CPos : Type
  | cor : CPos
  | cmid : CPos
  | cedgL : CPos
  | cedgR : CPos
  deriving DecidableEq

/-- The disjoint union of the subdivided attaching circles of the relators with words `w`.  The
element `(j, k, t)` belongs to the circle of the relator `j` at the position `k` of its word;
positions beyond the length of the word carry no relation. -/
def TCirc (_w : J → List (α × Bool)) : Type u := J × ℕ × CPos

namespace TCirc

variable (w : J → List (α × Bool))

/-- An element of a circle. -/
def pt (j : J) (k : ℕ) (t : CPos) : TCirc w := (j, k, t)

@[simp] theorem pt_fst (j : J) (k : ℕ) (t : CPos) : (pt w j k t).1 = j := rfl

@[simp] theorem pt_snd_snd (j : J) (k : ℕ) (t : CPos) : (pt w j k t).2.2 = t := rfl

@[simp] theorem pt_eq (j : J) (k : ℕ) (t : CPos) : pt w j k t = (j, k, t) := rfl

/-- The cyclic successor of a position of the word of the relator `j`. -/
def csucc (j : J) (k : ℕ) : ℕ := (k + 1) % (w j).length

/-- The strict relations of the circles: the corner and the midpoint of a letter lie under its
two halves, and the corner in front of the next letter lies under the right half. -/
protected def lt : TCirc w → TCirc w → Prop
  | (j, k, t), (j', k', t') =>
      j = j' ∧ k' < (w j).length ∧
        ((t = CPos.cor ∧ t' = CPos.cedgL ∧ k = k') ∨
         (t = CPos.cmid ∧ t' = CPos.cedgL ∧ k = k') ∨
         (t = CPos.cmid ∧ t' = CPos.cedgR ∧ k = k') ∨
         (t = CPos.cor ∧ t' = CPos.cedgR ∧ k = csucc w j k'))

/-- The face order of the circles. -/
protected def le (x y : TCirc w) : Prop := x = y ∨ TCirc.lt w x y

theorem lt_left_tag {x y : TCirc w} (h : TCirc.lt w x y) :
    x.2.2 = CPos.cor ∨ x.2.2 = CPos.cmid := by
  obtain ⟨-, -, h⟩ := h
  grind

theorem lt_right_tag {x y : TCirc w} (h : TCirc.lt w x y) :
    y.2.2 = CPos.cedgL ∨ y.2.2 = CPos.cedgR := by
  obtain ⟨-, -, h⟩ := h
  grind

instance : Preorder (TCirc w) where
  le := TCirc.le w
  le_refl _ := Or.inl rfl
  le_trans a b c hab hbc := by
    rcases hab with rfl | h1
    · exact hbc
    rcases hbc with rfl | h2
    · exact Or.inr h1
    exact absurd ((lt_left_tag w h2).elim (fun h => (lt_right_tag w h1).elim
      (fun h' => by rw [h'] at h; exact absurd h (by decide))
      (fun h' => by rw [h'] at h; exact absurd h (by decide)))
      (fun h => (lt_right_tag w h1).elim
      (fun h' => by rw [h'] at h; exact absurd h (by decide))
      (fun h' => by rw [h'] at h; exact absurd h (by decide)))) not_false

/-- The corner of a letter lies under its left half. -/
theorem cor_le_cedgL {j : J} {k : ℕ} (hk : k < (w j).length) :
    pt w j k CPos.cor ≤ pt w j k CPos.cedgL :=
  Or.inr ⟨rfl, hk, Or.inl ⟨rfl, rfl, rfl⟩⟩

/-- The midpoint of a letter lies under its left half. -/
theorem cmid_le_cedgL {j : J} {k : ℕ} (hk : k < (w j).length) :
    pt w j k CPos.cmid ≤ pt w j k CPos.cedgL :=
  Or.inr ⟨rfl, hk, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩

/-- The midpoint of a letter lies under its right half. -/
theorem cmid_le_cedgR {j : J} {k : ℕ} (hk : k < (w j).length) :
    pt w j k CPos.cmid ≤ pt w j k CPos.cedgR :=
  Or.inr ⟨rfl, hk, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))⟩

/-- The corner in front of the next letter lies under the right half of a letter. -/
theorem cor_csucc_le_cedgR {j : J} {k : ℕ} (hk : k < (w j).length) :
    pt w j (csucc w j k) CPos.cor ≤ pt w j k CPos.cedgR :=
  Or.inr ⟨rfl, hk, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))⟩

end TCirc

/-! ### The attaching map -/

variable (w : J → List (α × Bool))

/-- The attaching map of the circles onto the rose: a corner goes to the base vertex, the
midpoint of a letter to the midpoint of its generator, and the two halves of a letter to the two
halves of the loop of its generator, in the order prescribed by the sign of the letter. -/
def aFun : TCirc w → Rose α
  | (_, _, CPos.cor) => Rose.base
  | (j, k, CPos.cmid) =>
      match (w j)[k]? with
      | some p => Rose.mid p.1
      | none => Rose.base
  | (j, k, CPos.cedgL) =>
      match (w j)[k]? with
      | some p => Rose.edg p.1 (!p.2)
      | none => Rose.base
  | (j, k, CPos.cedgR) =>
      match (w j)[k]? with
      | some p => Rose.edg p.1 p.2
      | none => Rose.base

@[simp] theorem aFun_cor (j : J) (k : ℕ) : aFun w (j, k, CPos.cor) = Rose.base := rfl

theorem aFun_cmid_of_get {j : J} {k : ℕ} {p : α × Bool} (h : (w j)[k]? = some p) :
    aFun w (j, k, CPos.cmid) = Rose.mid p.1 := by simp_all [aFun]

theorem aFun_cedgL_of_get {j : J} {k : ℕ} {p : α × Bool} (h : (w j)[k]? = some p) :
    aFun w (j, k, CPos.cedgL) = Rose.edg p.1 (!p.2) := by simp_all [aFun]

theorem aFun_cedgR_of_get {j : J} {k : ℕ} {p : α × Bool} (h : (w j)[k]? = some p) :
    aFun w (j, k, CPos.cedgR) = Rose.edg p.1 p.2 := by simp_all [aFun]

theorem aFun_pt_cmid_of_get {j : J} {k : ℕ} {p : α × Bool} (h : (w j)[k]? = some p) :
    aFun w (TCirc.pt w j k CPos.cmid) = Rose.mid p.1 := aFun_cmid_of_get w h

theorem aFun_pt_cedgL_of_get {j : J} {k : ℕ} {p : α × Bool} (h : (w j)[k]? = some p) :
    aFun w (TCirc.pt w j k CPos.cedgL) = Rose.edg p.1 (!p.2) := aFun_cedgL_of_get w h

theorem aFun_pt_cedgR_of_get {j : J} {k : ℕ} {p : α × Bool} (h : (w j)[k]? = some p) :
    aFun w (TCirc.pt w j k CPos.cedgR) = Rose.edg p.1 p.2 := aFun_cedgR_of_get w h

theorem aFun_pt_cor (j : J) (k : ℕ) : aFun w (TCirc.pt w j k CPos.cor) = Rose.base := rfl

/-- The letter at a valid position, as an element of the word. -/
theorem exists_get_of_lt {j : J} {k : ℕ} (hk : k < (w j).length) :
    ∃ p : α × Bool, (w j)[k]? = some p :=
  ⟨(w j)[k], List.getElem?_eq_getElem hk⟩

theorem aFun_monotone : Monotone (aFun w) := by
  rintro x y (rfl | h)
  · exact le_refl _
  obtain ⟨j, k, t⟩ := x
  obtain ⟨j', k', t'⟩ := y
  obtain ⟨hj, hk', hcase⟩ := h
  subst hj
  obtain ⟨p, hp⟩ := exists_get_of_lt w hk'
  rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · rw [aFun_cor, aFun_cedgL_of_get w hp]
    exact Rose.base_le_edg _ _
  · rw [aFun_cmid_of_get w hp, aFun_cedgL_of_get w hp]
    exact Rose.mid_le_edg _ _
  · rw [aFun_cmid_of_get w hp, aFun_cedgR_of_get w hp]
    exact Rose.mid_le_edg _ _
  · rw [aFun_cor, aFun_cedgR_of_get w hp]
    exact Rose.base_le_edg _ _

/-- The attaching map as a monotone map. -/
def aHom : TCirc w →o Rose α := ⟨aFun w, aFun_monotone w⟩

/-! ### The model -/

/-- The mapping cylinder of the attaching map: the rose with the attaching circles sitting under
their images. -/
abbrev CylBase : Type u := CylP (aHom w)

/-- The circle of the relator `j`, as a subset of the cylinder. -/
def circSet (j : J) (x : CylBase w) : Prop :=
  ∃ k t, k < (w j).length ∧ x = cylOuter (aHom w) (TCirc.pt w j k t)

/-- **The poset model of the presentation complex**: the mapping cylinder of the attaching
circles with a cone point added over each circle. -/
def PresPos : Type u := ConeAdj (circSet w)

instance : Preorder (PresPos w) := inferInstanceAs (Preorder (ConeAdj (circSet w)))

/-- The rose inside the model. -/
def iRose (x : Rose α) : PresPos w := ConeAdj.inc (cylIn (aHom w) x)

/-- The attaching circles inside the model. -/
def iCirc (x : TCirc w) : PresPos w := ConeAdj.inc (cylOuter (aHom w) x)

/-- The two-cell of the relator `j`. -/
def apexOf (j : J) : PresPos w := ConeAdj.apex j

theorem iRose_monotone : Monotone (iRose w) := fun _ _ h => h

theorem iCirc_monotone : Monotone (iCirc w) := fun _ _ h => h

theorem iRose_aFun_monotone : Monotone (fun x => iRose w (aFun w x)) :=
  (iRose_monotone w).comp (aFun_monotone w)

/-- The defining relation of the cylinder: a point of a circle lies under its image. -/
theorem iCirc_le_iRose_aFun (x : TCirc w) : iCirc w x ≤ iRose w (aFun w x) :=
  le_refl (aFun w x)

/-- A point of the circle of `j` lies under the two-cell of `j`. -/
theorem iCirc_le_apexOf {j : J} {k : ℕ} (t : CPos) (hk : k < (w j).length) :
    iCirc w (TCirc.pt w j k t) ≤ apexOf w j :=
  ConeAdj.inc_le_apex_of_mem ⟨k, t, hk, rfl⟩

/-- The base point of the model. -/
def ptBase : PresPos w := iRose w Rose.base

/-! ### The loops of the generators -/

/-- The loop of the generator `i`: the four-edge circuit of its subdivided loop. -/
def genLoop (i : α) : List ((orderCx (PresPos w)).E × Bool) :=
  [ordPos ((iRose_monotone w) (Rose.base_le_edg i false)),
   ordNeg ((iRose_monotone w) (Rose.mid_le_edg i false)),
   ordPos ((iRose_monotone w) (Rose.mid_le_edg i true)),
   ordNeg ((iRose_monotone w) (Rose.base_le_edg i true))]

theorem isPath_genLoop (i : α) :
    IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt (genLoop w i)
      (ptBase w) (ptBase w) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The loop of a generator traversed backwards. -/
def genLoopRev (i : α) : List ((orderCx (PresPos w)).E × Bool) :=
  [ordPos ((iRose_monotone w) (Rose.base_le_edg i true)),
   ordNeg ((iRose_monotone w) (Rose.mid_le_edg i true)),
   ordPos ((iRose_monotone w) (Rose.mid_le_edg i false)),
   ordNeg ((iRose_monotone w) (Rose.base_le_edg i false))]


/-- The loop of a letter: the loop of its generator, reversed for a negative letter. -/
def letterLoop (p : α × Bool) : List ((orderCx (PresPos w)).E × Bool) :=
  if p.2 then genLoop w p.1 else genLoopRev w p.1

/-- The loop read off a word. -/
def wordLoop (l : List (α × Bool)) : List ((orderCx (PresPos w)).E × Bool) :=
  l.flatMap (letterLoop w)

@[simp] theorem wordLoop_nil : wordLoop w ([] : List (α × Bool)) = [] := rfl

@[simp] theorem wordLoop_append (l l' : List (α × Bool)) :
    wordLoop w (l ++ l') = wordLoop w l ++ wordLoop w l' := by
  simp [wordLoop]


theorem isPath_wordLoop (l : List (α × Bool)) :
    IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt (wordLoop w l)
      (ptBase w) (ptBase w) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      have hsplit : wordLoop w (p :: l) = letterLoop w p ++ wordLoop w l := rfl
      rw [hsplit]
      exact isPath_append_iff.mpr ⟨ptBase w, (by
        obtain ⟨i, b⟩ := p
        cases b with
        | true => exact isPath_genLoop w i
        | false => exact (⟨rfl, rfl, rfl, rfl, rfl⟩)), ih⟩

/-! ### The loops of the attaching circles -/

/-- The four edges of the circle of `j` at the position `k`, as a path of the order complex of
the circles. -/
def segAt (j : J) (k : ℕ) : List ((orderCx (TCirc w)).E × Bool) :=
  if hk : k < (w j).length then
    [ordPos (TCirc.cor_le_cedgL w hk), ordNeg (TCirc.cmid_le_cedgL w hk),
     ordPos (TCirc.cmid_le_cedgR w hk), ordNeg (TCirc.cor_csucc_le_cedgR w hk)]
  else []

/-- The path along the circle of `j` through its first `m` letters. -/
def circPath (j : J) : ℕ → List ((orderCx (TCirc w)).E × Bool)
  | 0 => []
  | m + 1 => circPath j m ++ segAt w j m

/-- The attaching loop of the relator `j`. -/
def circLoop (j : J) : List ((orderCx (TCirc w)).E × Bool) := circPath w j (w j).length

end PresModel
end FiniteChains

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains
namespace PresModel

open Comb

universe u

variable {α J : Type u} (w : J → List (α × Bool))

/-! ### The attaching circle as a path -/


theorem isPath_circPath (j : J) : ∀ {m : ℕ}, m ≤ (w j).length →
    IsPath (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt (circPath w j m)
      (TCirc.pt w j 0 CPos.cor) (TCirc.pt w j (m % (w j).length) CPos.cor) := by
  intro m
  induction m with
  | zero =>
      intro _
      show TCirc.pt w j 0 CPos.cor = TCirc.pt w j (0 % (w j).length) CPos.cor
      rw [Nat.zero_mod]
  | succ m ih =>
      intro hm
      have hlt  := lt_of_lt_of_le (Nat.lt_succ_self m) hm
      have hmod  := Nat.mod_eq_of_lt hlt
      have hprev := ih (le_of_lt hlt)
      rw [hmod] at hprev
      exact isPath_append_iff.mpr ⟨_, hprev, (by
        rw [segAt, dif_pos hlt]
        exact ⟨rfl, rfl, rfl, rfl, rfl⟩)⟩

/-- The attaching loop of a relator is a loop at the corner in front of its first letter. -/
theorem isPath_circLoop (j : J) :
    IsPath (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt (circLoop w j)
      (TCirc.pt w j 0 CPos.cor) (TCirc.pt w j 0 CPos.cor) := by
  have h := isPath_circPath w j (le_refl (w j).length)
  rwa [Nat.mod_self] at h

/-! ### The attaching circle lies under the two-cell -/

theorem pathIn_mapPath_segAt (j : J) {k : ℕ} (hk : k < (w j).length) :
    PathIn (fun x : PresPos w => x ≤ apexOf w j)
      (mapPath (orderCxMap (iCirc w) (iCirc_monotone w)) (segAt w j k)) := by
  have hcs : TCirc.csucc w j k < (w j).length :=
    Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le k) hk)
  rw [segAt, dif_pos hk]
  intro e he
  simp only [mapPath, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he
  obtain ⟨g, hg, rfl⟩ := he
  rcases hg with rfl | rfl | rfl | rfl
  · exact ⟨iCirc_le_apexOf w CPos.cor hk, iCirc_le_apexOf w CPos.cedgL hk⟩
  · exact ⟨iCirc_le_apexOf w CPos.cmid hk, iCirc_le_apexOf w CPos.cedgL hk⟩
  · exact ⟨iCirc_le_apexOf w CPos.cmid hk, iCirc_le_apexOf w CPos.cedgR hk⟩
  · exact ⟨iCirc_le_apexOf w CPos.cor hcs, iCirc_le_apexOf w CPos.cedgR hk⟩

theorem pathIn_mapPath_circPath (j : J) : ∀ {m : ℕ}, m ≤ (w j).length →
    PathIn (fun x : PresPos w => x ≤ apexOf w j)
      (mapPath (orderCxMap (iCirc w) (iCirc_monotone w)) (circPath w j m)) := by
  intro m
  induction m with
  | zero => intro _; exact pathIn_nil _
  | succ m ih =>
      intro hm
      have hlt  := lt_of_lt_of_le (Nat.lt_succ_self m) hm
      show PathIn _ (mapPath _ (circPath w j m ++ segAt w j m))
      rw [mapPath_append]
      intro e he
      rcases List.mem_append.1 he with h | h
      · exact ih (le_of_lt hlt) e h
      · exact pathIn_mapPath_segAt w j hlt e h

/-! ### The attaching circle is carried onto the loop of its word -/

theorem mapPath_segAt (j : J) {k : ℕ} (hk : k < (w j).length) :
    mapPath (orderCxMap (fun x => iRose w (aFun w x)) (iRose_aFun_monotone w)) (segAt w j k)
      = letterLoop w (w j)[k] := by
  have hp : (w j)[k]? = some (w j)[k] := List.getElem?_eq_getElem hk
  have hcor : iRose w (aFun w (TCirc.pt w j k CPos.cor)) = iRose w Rose.base := rfl
  have hcorS : iRose w (aFun w (TCirc.pt w j (TCirc.csucc w j k) CPos.cor))
      = iRose w Rose.base := rfl
  have hmid : iRose w (aFun w (TCirc.pt w j k CPos.cmid))
      = iRose w (Rose.mid (w j)[k].1) := by rw [aFun_pt_cmid_of_get w hp]
  have hL : iRose w (aFun w (TCirc.pt w j k CPos.cedgL))
      = iRose w (Rose.edg (w j)[k].1 (!(w j)[k].2)) := by rw [aFun_pt_cedgL_of_get w hp]
  have hR : iRose w (aFun w (TCirc.pt w j k CPos.cedgR))
      = iRose w (Rose.edg (w j)[k].1 (w j)[k].2) := by rw [aFun_pt_cedgR_of_get w hp]
  rw [segAt, dif_pos hk]
  show [ordPos ((iRose_aFun_monotone w) (TCirc.cor_le_cedgL w hk)),
      ordNeg ((iRose_aFun_monotone w) (TCirc.cmid_le_cedgL w hk)),
      ordPos ((iRose_aFun_monotone w) (TCirc.cmid_le_cedgR w hk)),
      ordNeg ((iRose_aFun_monotone w) (TCirc.cor_csucc_le_cedgR w hk))]
    = letterLoop w (w j)[k]
  rcases hpair : (w j)[k] with ⟨i, b⟩
  rw [hpair] at hmid hL hR
  cases b with
  | true =>
      show _ = genLoop w i
      simp only [genLoop, List.cons.injEq, and_true]
      exact ⟨ordPos_congr hcor hL _ _, ordNeg_congr hmid hL _ _, ordPos_congr hmid hR _ _,
        ordNeg_congr hcorS hR _ _⟩
  | false =>
      show _ = genLoopRev w i
      simp only [genLoopRev, List.cons.injEq, and_true]
      exact ⟨ordPos_congr hcor hL _ _, ordNeg_congr hmid hL _ _, ordPos_congr hmid hR _ _,
        ordNeg_congr hcorS hR _ _⟩

theorem mapPath_circPath (j : J) : ∀ {m : ℕ}, m ≤ (w j).length →
    mapPath (orderCxMap (fun x => iRose w (aFun w x)) (iRose_aFun_monotone w)) (circPath w j m)
      = wordLoop w ((w j).take m) := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
      intro hm
      have hlt  := lt_of_lt_of_le (Nat.lt_succ_self m) hm
      have hsplit : (w j).take (m + 1) = (w j).take m ++ [(w j)[m]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        rfl
      show mapPath _ (circPath w j m ++ segAt w j m) = _
      rw [mapPath_append, ih (le_of_lt hlt), mapPath_segAt w j hlt, hsplit, wordLoop_append]
      congr 1
      simp [wordLoop]

/-! ### The loop of a relator word is null-homotopic in the model -/

theorem htpy_wordLoop_nil (j : J) :
    Htpy (orderCx (PresPos w)) (ptBase w) (ptBase w) (wordLoop w (w j)) [] := by
  by_cases h0 : 0 < (w j).length
  case neg =>
    have hnil  := List.length_eq_zero_iff.mp (Nat.eq_zero_of_not_pos h0)
    rw [hnil]
    exact Htpy.refl _
  case pos =>
  set u : TCirc w := TCirc.pt w j 0 CPos.cor with hu
  have hloop  :=
    isPath_circLoop w j
  have hfg  := iCirc_le_iRose_aFun w
  -- the image of the attaching circle in the base copy is the loop of the word
  have himg : mapPath (orderCxMap (fun x => iRose w (aFun w x)) (iRose_aFun_monotone w))
      (circLoop w j) = wordLoop w (w j) := by
    have h := mapPath_circPath w j (le_refl (w j).length)
    rwa [List.take_length] at h
  -- the attaching circle itself dies under the cone point of the two-cell
  have hcone  :=
    htpy_nil_of_pathIn_le (apexOf w j) (iCirc_le_apexOf w CPos.cor h0)
      (isPath_mapPath (orderCxMap (iCirc w) (iCirc_monotone w)) hloop)
      (pathIn_mapPath_circPath w j (le_refl (w j).length))
  -- the naturality homotopy relates the two images
  have hnat := htpy_loop_mapPath_le (iCirc_monotone w) (iRose_aFun_monotone w) hfg hloop
  rw [himg] at hnat
  have h1  :=
    hcone.congr_append (isPath_ordNeg (hfg u)) (isPath_ordPos (hfg u))
  have h2  := htpy_ordNeg_ordPos (hfg u)
  refine hnat.trans (h1.trans ?_)
  simpa using h2

/-! ### The comparison homomorphism -/

/-- The class of the loop of a word. -/
def wordClass (l : List (α × Bool)) : Pi1 (orderCx (PresPos w)) (ptBase w) :=
  Pi1.mk ⟨wordLoop w l, isPath_wordLoop w l⟩

/-- The class of the loop of a generator. -/
def genClass (i : α) : Pi1 (orderCx (PresPos w)) (ptBase w) :=
  Pi1.mk ⟨genLoop w i, isPath_genLoop w i⟩

theorem wordClass_append (l l' : List (α × Bool)) :
    wordClass w (l ++ l') = wordClass w l * wordClass w l' := by
  refine Quotient.sound ?_
  simp



/-- The homomorphism of the free group into the fundamental group of the model. -/
def alphaFree : FreeGroup α →* Pi1 (orderCx (PresPos w)) (ptBase w) :=
  FreeGroup.lift (genClass w)

theorem alphaFree_of (i : α) : alphaFree w (FreeGroup.of i) = genClass w i := rfl

theorem alphaFree_mk (l : List (α × Bool)) : alphaFree w (FreeGroup.mk l) = wordClass w l := by
  induction l with
  | nil => rfl
  | cons eb l ih =>
      obtain ⟨i, b⟩ := eb
      have hsplit : ((i, b) :: l) = [(i, b)] ++ l := rfl
      rw [hsplit, ← FreeGroup.mul_mk, map_mul, ih, wordClass_append]
      congr 1
      cases b
      · rfl
      · rfl

/-- **The relators die in the model.** -/
theorem alphaFree_relator (j : J) : alphaFree w (FreeGroup.mk (w j)) = 1 := by
  rw [alphaFree_mk]
  exact Quotient.sound (htpy_wordLoop_nil w j)

/-! ### The model of a presentation -/

/-- A word representing each relator of the presentation `ρ`. -/
def presWords (ρ : J → FreeGroup α) : J → List (α × Bool) := fun j => Quot.out (ρ j)

theorem mk_presWords (ρ : J → FreeGroup α) (j : J) :
    FreeGroup.mk (presWords ρ j) = ρ j := Quot.out_eq _

end PresModel
end FiniteChains

namespace FiniteChains
namespace PresModel

open Comb

universe u v

variable {α J : Type u} (w : J → List (α × Bool)) {G : Type v} [Group G] (gen : α → G)

/-! ### The values of letters and words -/

/-- The value of a letter. -/
def letterVal (p : α × Bool) : G := if p.2 then gen p.1 else (gen p.1)⁻¹

/-- The value of a word. -/
def wordVal (l : List (α × Bool)) : G := FreeGroup.lift gen (FreeGroup.mk l)

@[simp] theorem wordVal_nil : wordVal (gen := gen) [] = 1 := rfl

theorem wordVal_append (l l' : List (α × Bool)) :
    wordVal gen (l ++ l') = wordVal gen l * wordVal gen l' := by
  rw [wordVal, wordVal, wordVal, ← FreeGroup.mul_mk, map_mul]

theorem wordVal_single (p : α × Bool) : wordVal gen [p] = letterVal gen p := by
  obtain ⟨i, b⟩ := p
  cases b <;> simp [wordVal, letterVal, FreeGroup.lift_mk]

/-! ### The cocycle of the rose -/

/-- The cocycle of the subdivided rose: the generator is read off the second half of its loop. -/
def roseVal : Rose α → Rose α → G
  | Rose.base, Rose.edg i b => if b then (gen i)⁻¹ else 1
  | _, _ => 1

@[simp] theorem roseVal_base_edg (i : α) (b : Bool) :
    roseVal gen Rose.base (Rose.edg i b) = if b then (gen i)⁻¹ else 1 := rfl

@[simp] theorem roseVal_mid_edg (i i' : α) (b : Bool) :
    roseVal gen (Rose.mid i) (Rose.edg i' b) = 1 := rfl

@[simp] theorem roseVal_self (x : Rose α) : roseVal gen x x = 1 := by
  cases x <;> rfl

/-- The cocycle of the rose. -/
def roseCoc : OrdCocycle (Rose α) G where
  val := roseVal gen
  comp := by
    intro a b c hab hbc
    cases b with
    | base =>
        cases a with
        | base => rw [roseVal_self, one_mul]
        | mid i => exact hab.elim
        | edg i b => exact hab.elim
    | mid i =>
        cases a with
        | base => exact hab.elim
        | mid i' =>
            have hii : i' = i := hab
            subst hii
            rw [roseVal_self, one_mul]
        | edg i' b => exact hab.elim
    | edg i bb =>
        cases c with
        | base => exact hbc.elim
        | mid i' => exact hbc.elim
        | edg i' b' =>
            obtain ⟨hi, hb⟩ := hbc
            subst hi
            subst hb
            rw [roseVal_self, mul_one]

/-- The cocycle of the mapping cylinder: the cocycle of the rose read through the retraction. -/
def cylCoc : OrdCocycle (CylBase w) G :=
  (roseCoc gen).comap (cylRetr (aHom w)) (cylRetr_monotone (aHom w))

/-! ### The trivialisation over a two-cell -/

/-- The prefix product of the first `k` letters of the relator `j`. -/
def prefixVal (j : J) (k : ℕ) : G := wordVal gen ((w j).take k)

@[simp] theorem prefixVal_zero (j : J) : prefixVal w gen j 0 = 1 := rfl

theorem prefixVal_succ (j : J) {k : ℕ} (hk : k < (w j).length) :
    prefixVal w gen j (k + 1) = prefixVal w gen j k * letterVal gen (w j)[k] := by
  have hsplit : (w j).take (k + 1) = (w j).take k ++ [(w j)[k]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk]
    rfl
  rw [prefixVal, prefixVal, hsplit, wordVal_append, wordVal_single]

/-- The value of the trivialisation at a point of a circle. -/
def trivVal (j : J) (k : ℕ) (t : CPos) : G :=
  match t with
  | CPos.cor => (prefixVal w gen j k)⁻¹
  | _ => (roseVal gen Rose.base (aFun w (j, k, CPos.cedgL)))⁻¹ * (prefixVal w gen j k)⁻¹

/-- The trivialisation of the cocycle under the cone point of the relator `j`. -/
def trivFun (_j : J) : CylBase w → G :=
  Sum.elim (fun _ => 1) (fun x => trivVal w gen x.1 x.2.1 x.2.2)

/-- The prefix product at the cyclic successor of a position: the relator word closes up
because it evaluates to `1`. -/
theorem prefixVal_csucc (hrel : ∀ j : J, wordVal gen (w j) = 1) (j : J) {k : ℕ}
    (hk : k < (w j).length) :
    prefixVal w gen j (TCirc.csucc w j k) = prefixVal w gen j (k + 1) := by
  rcases lt_or_eq_of_le (Nat.succ_le_of_lt hk) with hlt | heq
  · rw [TCirc.csucc, Nat.mod_eq_of_lt hlt]
  · have hlen : (w j).length = k + 1 := heq.symm
    have h0 : TCirc.csucc w j k = 0 := by rw [TCirc.csucc, hlen, Nat.mod_self]
    rw [h0, prefixVal_zero, prefixVal, ← hlen, List.take_length, hrel j]

/-- **The trivialisation is parallel for the cocycle**: this is the cocycle identity for a
comparability of the attaching circle and the cone point over it. -/
theorem trivVal_step (hrel : ∀ j : J, wordVal gen (w j) = 1) {x y : TCirc w} (h : x ≤ y) :
    roseVal gen (aFun w x) (aFun w y) * trivVal w gen y.1 y.2.1 y.2.2
      = trivVal w gen x.1 x.2.1 x.2.2 := by
  rcases h with rfl | hlt
  · simp
  obtain ⟨j, k, t⟩ := x
  obtain ⟨j', k', t'⟩ := y
  obtain ⟨hj, hk', hcase⟩ := hlt
  subst hj
  obtain ⟨p, hp⟩ := exists_get_of_lt w hk'
  have hL  := aFun_cedgL_of_get w hp
  have hR  := aFun_cedgR_of_get w hp
  have hM  := aFun_cmid_of_get w hp
  rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · -- corner ≤ left half
    show roseVal gen Rose.base (aFun w (j, k, CPos.cedgL))
        * ((roseVal gen Rose.base (aFun w (j, k, CPos.cedgL)))⁻¹
          * (prefixVal w gen j k)⁻¹) = (prefixVal w gen j k)⁻¹
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  · -- midpoint ≤ left half
    rw [hM, hL, roseVal_mid_edg, one_mul]
    rfl
  · -- midpoint ≤ right half
    rw [hM, hR, roseVal_mid_edg, one_mul]
    rfl
  · -- the corner in front of the next letter ≤ right half: here the letter is read
    show roseVal gen (aFun w (j, TCirc.csucc w j k', CPos.cor)) (aFun w (j, k', CPos.cedgR))
        * trivVal w gen j k' CPos.cedgR = trivVal w gen j (TCirc.csucc w j k') CPos.cor
    show roseVal gen Rose.base (aFun w (j, k', CPos.cedgR))
        * ((roseVal gen Rose.base (aFun w (j, k', CPos.cedgL)))⁻¹
          * (prefixVal w gen j k')⁻¹) = (prefixVal w gen j (TCirc.csucc w j k'))⁻¹
    rw [prefixVal_csucc w gen hrel j hk', prefixVal_succ w gen j hk', hL, hR,
      roseVal_base_edg, roseVal_base_edg]
    have hpk : (w j)[k'] = p := by
      have := List.getElem?_eq_getElem hk'
      rw [hp] at this
      exact (Option.some.injEq _ _ ▸ this.symm) ▸ rfl
    rw [hpk, letterVal]
    cases hp2 : p.2 with
    | true => simp
    | false => simp

/-- **The cocycle of the model.**  The hypothesis is that every relator word evaluates to `1`,
which is what makes the trivialisation over a two-cell consistent. -/
def presCoc (hrel : ∀ j : J, wordVal gen (w j) = 1) : OrdCocycle (PresPos w) G :=
  (cylCoc w gen).coneAdj (trivFun w gen) (by
    intro t p q hpq hq
    obtain ⟨r, hr, hqr⟩ := hq
    obtain ⟨k0, t0, hk0, rfl⟩ := hr
    -- the elements under a cone point are the points of its circle
    cases q with
    | inl y => exact hqr.elim
    | inr y =>
        cases p with
        | inl x => exact hpq.elim
        | inr x => exact trivVal_step w gen hrel hpq)

/-! ### The reading homomorphism -/

/-- **The reading homomorphism** of the model: the monodromy of the cocycle. -/
def reading (hrel : ∀ j : J, wordVal gen (w j) = 1) :
    Pi1 (orderCx (PresPos w)) (ptBase w) →* G :=
  (presCoc w gen hrel).monodromy (ptBase w)

/-- **The reading homomorphism reads the generators.** -/
theorem reading_genClass (hrel : ∀ j : J, wordVal gen (w j) = 1) (i : α) :
    reading w gen hrel (genClass w i) = gen i := by
  show roseVal gen Rose.base (Rose.edg i false) *
      ((roseVal gen (Rose.mid i) (Rose.edg i false))⁻¹ *
        (roseVal gen (Rose.mid i) (Rose.edg i true) *
          ((roseVal gen Rose.base (Rose.edg i true))⁻¹ * 1))) = gen i
  simp

/-! ### Injectivity of the comparison -/

end PresModel
end FiniteChains
end
