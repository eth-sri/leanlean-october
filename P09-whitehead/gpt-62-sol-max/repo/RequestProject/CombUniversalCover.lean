module

public import RequestProject.CombCoveringLift

@[expose] public section

/-!
# The universal cover of a combinatorial two-complex

This file constructs the universal cover of a combinatorial two-complex `X` (in the sense of
`RequestProject/CellComplex.lean`) from scratch, in the classical way: its vertices are the
homotopy classes, in the sense of `RequestProject/CombPi1.lean`, of edge paths issued from a
base vertex.

* `FiniteChains.Comb.UV` — the vertices: homotopy classes of edge paths starting at `x₀`;
* `FiniteChains.Comb.uCover` — the universal cover as a `Comb.Complex2`: an edge is a
  vertex `c` together with an edge `e` of `X` issued from the endpoint of `c`, and a two-cell
  is a vertex `c` together with a two-cell of `X` based at the endpoint of `c`, attached along
  the lift of its attaching loop;
* `FiniteChains.Comb.univProj` — the projection to `X`, and
  `FiniteChains.Comb.isCovering_univProj` — it is a combinatorial covering;
* `FiniteChains.Comb.isConnected_univCover` — the cover is connected when `X` is;
* `FiniteChains.Comb.simplyConnected_univCover` — the cover is simply connected: lifting is
  compatible with homotopies, and a loop upstairs is the lift of a null-homotopic loop;
* `FiniteChains.Comb.univDeck` — the deck action of `π₁(X, x₀)` by left concatenation, and
  `FiniteChains.Comb.isRegular_univProj` — the cover is regular with this deck group.
-/

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains
namespace Comb

universe u

variable {X : Complex2.{u}}

/-! ### The endpoint of an edge path -/

/-- The endpoint of a list of oriented edges read from `a`. -/
def endpt (X : Complex2.{u}) : X.V → List (X.E × Bool) → X.V
  | a, [] => a
  | _, eb :: t => endpt X (germTgt X.src X.tgt eb) t



theorem endpt_eq_of_isPath {p : List (X.E × Bool)} {a b : X.V}
    (h : IsPath X.src X.tgt p a b) : endpt X a p = b := by
  induction p generalizing a with
  | nil => exact h
  | cons eb t ih => exact ih h.2

theorem endpt_append (a : X.V) (p q : List (X.E × Bool)) :
    endpt X a (p ++ q) = endpt X (endpt X a p) q := by
  induction p generalizing a with
  | nil => rfl
  | cons eb t ih => exact ih _

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
      have hq  := h.isPath p.2
      have he  := endpt_eq_of_isPath hq
      rw [he]
      exact h.symm
    · intro p q r h h'
      have hq  := h.isPath p.2
      have he  := endpt_eq_of_isPath hq
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
    have hq  := h.isPath p.2
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
    IsPath X.src X.tgt (p ++ [eb]) a (endpt X a (p ++ [eb])) := by
  rw [endpt_append_single a p eb h]
  exact isPath_append_iff.mpr ⟨germSrc X.src X.tgt eb, h ▸ hp, isPath_single eb⟩

open Classical in
/-- Appending an oriented edge to a path from `x₀` (the path is left unchanged if the edge
does not start at its endpoint). -/
noncomputable def extendP (eb : X.E × Bool) (p : PathFrom X x₀) : PathFrom X x₀ :=
  if h : endpt X x₀ p.1 = germSrc X.src X.tgt eb then ⟨p.1 ++ [eb], isPath_append_single p.2 eb h⟩
  else p

theorem extendP_pos {p : PathFrom X x₀} {eb : X.E × Bool}
    (h : endpt X x₀ p.1 = germSrc X.src X.tgt eb) : (extendP eb p).1 = p.1 ++ [eb] := by
  classical
  simp only [extendP, dif_pos h]

theorem extendP_neg {p : PathFrom X x₀} {eb : X.E × Bool}
    (h : ¬ endpt X x₀ p.1 = germSrc X.src X.tgt eb) : (extendP eb p).1 = p.1 := by
  classical
  simp only [extendP, dif_neg h]

/-- Appending an oriented edge to a class of paths. -/
noncomputable def extend (eb : X.E × Bool) (c : UV X x₀) : UV X x₀ :=
  Quotient.map (extendP eb) (by
    intro p q hpq
    have hq  := hpq.isPath p.2
    have he  := endpt_eq_of_isPath hq
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

/-- Extending a class by a whole path. -/
noncomputable def extendList (q : List (X.E × Bool)) (c : UV X x₀) : UV X x₀ :=
  q.foldl (fun d eb => extend eb d) c

@[simp] theorem extendList_nil (c : UV X x₀) : extendList [] c = c := rfl

@[simp] theorem extendList_cons (eb : X.E × Bool) (q : List (X.E × Bool)) (c : UV X x₀) :
    extendList (eb :: q) c = extendList q (extend eb c) := rfl

theorem extendList_append (q r : List (X.E × Bool)) (c : UV X x₀) :
    extendList (q ++ r) c = extendList r (extendList q c) := by
  induction q generalizing c with
  | nil => rfl
  | cons eb t ih => tauto

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
      simpa using Htpy.refl (X := X) (a := x₀) (b := endpt X x₀ p.1) p.1
  | cons eb t ih =>
      intro p r w hq hr
      have h'  := hq.1
      have hend : endpt X x₀ (extendP eb p).1 = germTgt X.src X.tgt eb := by
        rw [extendP_pos h', endpt_append_single x₀ p.1 eb h']
      rw [extendList_cons, extend_mk]
      refine ih (p := extendP eb p) (r := r) (w := w) ?_ ?_
      · rw [hend]; exact hq.2
      · rw [extendP_pos h', hr]; simp

theorem endV_extendList : ∀ {q : List (X.E × Bool)} {c : UV X x₀} {w : X.V},
    IsPath X.src X.tgt q (endV c) w → endV (extendList q c) = w := by
  intro q
  induction q with
  | nil => simp
  | cons eb t ih =>
      intro c w hq
      have h  := hq.1
      refine ih (c := extend eb c) (w := w) ?_
      rw [endV_extend h]
      exact hq.2

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
      rw [extendList_mk (p := p) (r := ⟨p.1 ++ l, by simp_all⟩) hl rfl,
        extendList_mk (p := p) (r := ⟨p.1 ++ l', by simp_all⟩) hl' rfl]
      refine Quotient.sound ?_
      show Htpy X x₀ (endpt X x₀ (p.1 ++ l)) (p.1 ++ l) (p.1 ++ l')
      rw [hend]
      exact Htpy.append_congr p.2 hl (Htpy.refl _) h

/-- Extending by an edge and then by its reverse returns the original class. -/
theorem extend_revGerm {c : UV X x₀} {eb : X.E × Bool} (h : endV c = germSrc X.src X.tgt eb) :
    extend (revGerm eb) (extend eb c) = c := by
  have hp : IsPath X.src X.tgt [eb, revGerm eb] (endV c) (endV c) :=
    ⟨h, (germSrc_revGerm eb).symm, (germTgt_revGerm eb).trans h.symm⟩
  exact extendList_htpy (l' := []) hp (Htpy.of_step ⟨hp, rfl, Or.inl ⟨[], [], eb, rfl, rfl⟩⟩)

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
noncomputable def uTgt (ce : UE X x₀) : UV X x₀ := extend (ce.1.2, true) ce.1.1

/-- The basepoint of a two-cell of the universal cover. -/
def uBase (cf : UF X x₀) : UV X x₀ := cf.1.1

/-- The lift of an oriented edge at a vertex of the cover. -/
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
/-- The lift of an edge path at a vertex of the cover. -/
noncomputable def uLiftPath : List (X.E × Bool) → UV X x₀ → List (UE X x₀ × Bool)
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
noncomputable def uAtt (cf : UF X x₀) : List (UE X x₀ × Bool) :=
  uLiftPath (X.att cf.1.2) cf.1.1

theorem germSrc_liftGerm {c : UV X x₀} {eb : X.E × Bool}
    (h : endV c = germSrc X.src X.tgt eb) :
    germSrc uSrc uTgt (liftGerm c eb h) = c := by
  obtain ⟨e, b⟩ := eb
  cases b with
  | true => rfl
  | false =>
      exact extend_revGerm (eb := (e, false)) h

theorem germTgt_liftGerm {c : UV X x₀} {eb : X.E × Bool}
    (h : endV c = germSrc X.src X.tgt eb) :
    germTgt uSrc uTgt (liftGerm c eb h) = extend eb c := by
  obtain ⟨e, b⟩ := eb
  cases b with
  | true => rfl
  | false => rfl

/-- The lift of a path is a path of the cover, from the given vertex to the extended one. -/
theorem isPath_uLiftPath : ∀ (q : List (X.E × Bool)) (c : UV X x₀) (w : X.V),
    IsPath X.src X.tgt q (endV c) w → IsPath uSrc uTgt (uLiftPath q c) c (extendList q c) := by
  intro q
  induction q with
  | nil => tauto
  | cons eb t ih =>
      intro c w hq
      have h  := hq.1
      rw [uLiftPath_cons h, extendList_cons]
      refine ⟨(germSrc_liftGerm h).symm, ?_⟩
      rw [germTgt_liftGerm h]
      refine ih (extend eb c) w ?_
      rw [endV_extend h]
      exact hq.2

/-- Extending a class along the attaching loop of a two-cell based at its endpoint returns
the same class: this is exactly the two-cell cancellation. -/
theorem extendList_att {c : UV X x₀} {f : X.F} (h : endV c = X.base f) :
    extendList (X.att f) c = c := by
  have hp' : IsPath X.src X.tgt (X.att f) (endV c) (endV c) := by rw [h]; exact X.att_isLoop f
  exact extendList_htpy (l' := []) hp' (Htpy.of_step ⟨hp', rfl, Or.inr ⟨[], [], f, by simp, rfl⟩⟩)

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
  | nil => tauto
  | cons eb t ih =>
      intro c w hq
      have h  := hq.1
      rw [uLiftPath_cons h, List.map_cons, ih (extend eb c) w (by rw [endV_extend h]; exact hq.2)]
      obtain ⟨e, b⟩ := eb
      cases b <;> rfl

variable (X x₀) in
/-- **The universal cover** of a combinatorial two-complex. -/
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
/-- The projection of the universal cover to the complex. -/
noncomputable def univProj : Hom (uCover X x₀) X where
  onV := endV
  onE := fun ce => ce.1.2
  onF := fun cf => cf.1.2
  src_onE := fun ce => ce.2.symm
  tgt_onE := by
    intro ce
    show X.tgt ce.1.2 = endV (extend (ce.1.2, true) ce.1.1)
    have h  := ce.2
    rw [endV_extend h]
    rfl
  base_onF := fun cf => cf.2.symm
  att_onF := by
    intro cf
    have h  := cf.2
    have hatt : IsPath X.src X.tgt (X.att cf.1.2) (endV cf.1.1) (X.base cf.1.2) :=
      h ▸ X.att_isLoop cf.1.2
    exact (map_uLiftPath (X.att cf.1.2) cf.1.1 (X.base cf.1.2) hatt).symm

/-! ### The projection is a covering -/

theorem endV_surjective (hX : IsConnected X) : Function.Surjective (endV (X := X) (x₀ := x₀)) := by
  intro v
  obtain ⟨p, hp⟩ := hX x₀ v
  have he  := endpt_eq_of_isPath hp
  exact ⟨UV.mk ⟨p, by simp_all⟩, he⟩

theorem uniqueLifts_univProj : HasUniqueLifts (univProj X x₀) := by
  constructor
  · intro c
    refine Function.bijective_iff_has_inverse.mpr
      ⟨fun e => ⟨liftGerm c e.1 e.2.symm, germSrc_liftGerm e.2.symm⟩, ?_, ?_⟩
    · rintro ⟨⟨⟨⟨d, e⟩, hd⟩, b⟩, hc⟩
      cases b
      · have hc' : extend (e, true) d = c := hc
        have he : extend (e, false) c = d := hc' ▸ extend_revGerm (eb := (e, true)) hd
        exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext he rfl)) rfl)
      · exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext hc.symm rfl)) rfl)
    · rintro ⟨⟨e, b⟩, h⟩; cases b <;> rfl
  · exact ((Equiv.prodComm (UV X x₀) X.F).subtypeEquiv (fun _ => eq_comm)).bijective

theorem isCovering_univProj (hX : IsConnected X) : IsCovering (univProj X x₀) :=
  ⟨endV_surjective hX, uniqueLifts_univProj.germ, uniqueLifts_univProj.cell⟩

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
          extendList_mk (p := ({ val := [], property := rfl })) (r := p)
            (w := endpt X x₀ p.1) hp (by simp)
        rwa [hext] at hlift
  intro c d
  obtain ⟨l, hl⟩ := key c
  obtain ⟨m, hm⟩ := key d
  refine ⟨revPath (X := uCover X x₀) l ++ m, ?_⟩
  exact isPath_append_iff (X := uCover X x₀).mpr
    ⟨UV.base X x₀, isPath_revPath (X := uCover X x₀) hl, hm⟩

/-! ### The cover is simply connected -/

/-- Lifting is additive along concatenation. -/
theorem uLiftPath_append : ∀ (l : List (X.E × Bool)) (m : List (X.E × Bool)) (c : UV X x₀)
    (w : X.V), IsPath X.src X.tgt l (endV c) w →
      uLiftPath (l ++ m) c = uLiftPath l c ++ uLiftPath m (extendList l c) := by
  intro l
  induction l with
  | nil => tauto
  | cons eb t ih =>
      intro m c w hl
      have h  := hl.1
      rw [List.cons_append, uLiftPath_cons h, uLiftPath_cons h, extendList_cons,
        ih m (extend eb c) w (by rw [endV_extend h]; exact hl.2)]
      rfl

/-- The lift of a path of the cover's projection is the original path. -/
theorem eq_uLiftPath_of_isPath (L : List ((uCover X x₀).E × Bool)) (c d : UV X x₀)
    (h : IsPath (uCover X x₀).src (uCover X x₀).tgt L c d) :
    L = uLiftPath (mapPath (univProj X x₀) L) c := by
  have hp := isPath_mapPath (univProj X x₀) h
  exact liftPath_unique uniqueLifts_univProj _ _ _ _ _ h (isPath_uLiftPath _ _ _ hp)
    (map_uLiftPath _ _ _ hp).symm

/-- A graph map into a universal cover sends a path to the unique lift of its projection. -/
theorem map_eq_uLiftPath {K : Complex2.{u}} (v : K.V → UV X x₀) (e : K.E → UE X x₀)
    (hs : ∀ d, uSrc (e d) = v (K.src d)) (ht : ∀ d, uTgt (e d) = v (K.tgt d))
    {l : List (K.E × Bool)} {a b : K.V} (h : IsPath K.src K.tgt l a b) :
    (l.map fun d => (e d.1, d.2)) = uLiftPath (l.map fun d => ((e d.1).1.2, d.2)) (v a) := by
  simpa only [mapPath, List.map_map, Function.comp_def, univProj] using
    eq_uLiftPath_of_isPath _ _ _ (isPath_map v e hs ht h)

/-- Lifts of homotopic paths are homotopic. -/
theorem htpy_uLiftPath {c : UV X x₀} {q q' : List (X.E × Bool)} {w : X.V}
    (hq : IsPath X.src X.tgt q (endV c) w) (h : Htpy X (endV c) w q q') :
    Htpy (uCover X x₀) c (extendList q c) (uLiftPath q c) (uLiftPath q' c) := by
  have h' : Htpy X (endV c) (endV (extendList q c))
      (mapPath (univProj X x₀) (uLiftPath q c)) q' := by
    rw [endV_extendList hq, show mapPath (univProj X x₀) (uLiftPath q c) = q from map_uLiftPath _ _ _ hq]
    exact h
  obtain ⟨L, hL, hmap, hh⟩ := lift_htpy uniqueLifts_univProj (isPath_uLiftPath _ _ _ hq) h'
  rwa [eq_uLiftPath_of_isPath _ _ _ hL, hmap] at hh

/-- **The universal cover is simply connected.** -/
theorem simplyConnected_univCover : SimplyConnected (uCover X x₀) := by
  let o := UV.base X x₀
  refine simplyConnected_of_base (a := o) isConnected_univCover ?_
  intro L hL
  let q := mapPath (univProj X x₀) L
  have hq : IsPath X.src X.tgt q x₀ x₀ := isPath_mapPath (univProj X x₀) hL
  have he : extendList q o = o := isPath_endpoint_eq (isPath_uLiftPath q o x₀ hq)
    (eq_uLiftPath_of_isPath L o o hL ▸ hL)
  let r : PathFrom X x₀ := ⟨q, by rwa [endpt_eq_of_isPath hq]⟩
  have hr : UV.mk r = o := (extendList_mk (p := ⟨[], rfl⟩) (r := r) hq (List.nil_append _).symm).symm.trans he
  have hnull : Htpy X x₀ x₀ q [] := by
    have h : Htpy X x₀ (endpt X x₀ q) q [] := Quotient.exact hr
    rwa [endpt_eq_of_isPath hq] at h
  obtain ⟨m, _, hm, hh⟩ := lift_htpy uniqueLifts_univProj hL hnull
  rwa [List.map_eq_nil_iff.mp hm] at hh

/-! ### Changing the base vertex of the universal cover -/

section Shift

variable {X : Complex2.{u}} {y₀ w₀ : X.V} {q : List (X.E × Bool)}

/-- Prepending a fixed path to a path issued from its endpoint. -/
def shiftP (hq : IsPath X.src X.tgt q y₀ w₀) (p : PathFrom X w₀) : PathFrom X y₀ :=
  ⟨q ++ p.1, by
    rw [endpt_append, endpt_eq_of_isPath hq]
    exact hq.append p.2⟩

theorem endpt_shiftP (hq : IsPath X.src X.tgt q y₀ w₀) (p : PathFrom X w₀) :
    endpt X y₀ (shiftP hq p).1 = endpt X w₀ p.1 := by
  show endpt X y₀ (q ++ p.1) = endpt X w₀ p.1
  rw [endpt_append, endpt_eq_of_isPath hq]

/-- Changing the base vertex of the universal cover, on vertices. -/
def shiftV (hq : IsPath X.src X.tgt q y₀ w₀) (c : UV X w₀) : UV X y₀ :=
  Quotient.map (shiftP hq) (by
    intro p p' hpp
    show Htpy X y₀ (endpt X y₀ (shiftP hq p).1) (shiftP hq p).1 (shiftP hq p').1
    rw [endpt_shiftP]
    exact Htpy.append_congr hq p.2 (Htpy.refl q) hpp) c


@[simp] theorem endV_shiftV (hq : IsPath X.src X.tgt q y₀ w₀) (c : UV X w₀) :
    endV (shiftV hq c) = endV c := by
  induction c using UV.ind with
  | h p => exact endpt_shiftP hq p

theorem shiftV_base (hq : IsPath X.src X.tgt q y₀ w₀) :
    shiftV hq (UV.base X w₀) = UV.mk ⟨q, by simpa [endpt_eq_of_isPath hq] using hq⟩ := congrArg UV.mk (Subtype.ext (List.append_nil _))

theorem extend_shiftV (hq : IsPath X.src X.tgt q y₀ w₀) (eb : X.E × Bool) (c : UV X w₀) :
    extend eb (shiftV hq c) = shiftV hq (extend eb c) := by
  induction c using UV.ind with
  | h p =>
      have hl : (extendP eb (shiftP hq p)).1 = (shiftP hq (extendP eb p)).1 := by
        by_cases h : endpt X w₀ p.1 = germSrc X.src X.tgt eb
        · have h' : endpt X y₀ (shiftP hq p).1 = germSrc X.src X.tgt eb := by
            simpa [endpt_shiftP] using h
          rw [extendP_pos h']
          show (q ++ p.1) ++ [eb] = q ++ (extendP eb p).1
          rw [extendP_pos h]
          simp
        · have h' : ¬ endpt X y₀ (shiftP hq p).1 = germSrc X.src X.tgt eb := by
            rw [endpt_shiftP]; exact h
          rw [extendP_neg h']
          show (shiftP hq p).1 = q ++ (extendP eb p).1
          rw [extendP_neg h]
          rfl
      exact congrArg UV.mk (Subtype.ext hl)

/-- Changing the base vertex of the universal cover, on edges. -/
def shiftE (hq : IsPath X.src X.tgt q y₀ w₀) (E : UE X w₀) : UE X y₀ :=
  ⟨(shiftV hq E.1.1, E.1.2), by simpa using E.2⟩

/-- Changing the base vertex of the universal cover, on two-cells. -/
def shiftF (hq : IsPath X.src X.tgt q y₀ w₀) (F : UF X w₀) : UF X y₀ :=
  ⟨(shiftV hq F.1.1, F.1.2), by simpa using F.2⟩

theorem uLiftPath_shiftV (hq : IsPath X.src X.tgt q y₀ w₀) :
    ∀ (l : List (X.E × Bool)) (c : UV X w₀) (v : X.V), IsPath X.src X.tgt l (endV c) v →
      uLiftPath l (shiftV hq c) = (uLiftPath l c).map (fun Eb => (shiftE hq Eb.1, Eb.2)) := by
  intro l c v hl
  have he := map_eq_uLiftPath (K := uCover X w₀) (shiftV hq) (shiftE hq)
    (fun _ => rfl) (fun E => extend_shiftV hq (E.1.2, true) E.1.1)
    (isPath_uLiftPath l c v hl)
  change _ = uLiftPath ((uLiftPath l c).map fun d => (d.1.1.2, d.2)) _ at he
  rw [map_uLiftPath _ _ _ hl] at he
  exact he.symm

/-- **Change of base vertex of the universal cover.**  A path from `y₀` to `w₀` induces a
cellular map `Ũ(X, w₀) → Ũ(X, y₀)` over `X`; it sends the base vertex to the class of the
path.  For a loop this is the deck transformation attached to its class. -/
noncomputable def shiftHom (hq : IsPath X.src X.tgt q y₀ w₀) :
    Hom (uCover X w₀) (uCover X y₀) where
  onV := shiftV hq
  onE := shiftE hq
  onF := shiftF hq
  src_onE := fun _ => rfl
  tgt_onE := fun E => extend_shiftV hq (E.1.2, true) E.1.1
  base_onF := fun _ => rfl
  att_onF := by
    intro F
    exact uLiftPath_shiftV hq _ _ _ (F.2 ▸ X.att_isLoop F.1.2)

theorem shiftHom_base (hq : IsPath X.src X.tgt q y₀ w₀) :
    (shiftHom hq).onV (UV.base X w₀) = UV.mk ⟨q, by simpa [endpt_eq_of_isPath hq] using hq⟩ :=
  shiftV_base hq

end Shift

/-! ### The deck action -/

/-- Concatenating a loop at `x₀` in front of a path from `x₀`. -/
def deckP (g : Loop X x₀) : PathFrom X x₀ → PathFrom X x₀ := shiftP g.2

/-- The action of the fundamental group on the vertices of the universal cover. -/
def deckV (γ : Pi1 X x₀) (c : UV X x₀) : UV X x₀ :=
  Quotient.map₂ deckP (by
    intro g g' hg p p' hp
    change Htpy X x₀ (endpt X x₀ (shiftP g.2 p).1) (shiftP g.2 p).1 (shiftP g'.2 p').1
    rw [endpt_shiftP g.2 p]
    exact Htpy.append_congr g.2 p.2 hg hp) γ c


@[simp] theorem endV_deckV (γ : Pi1 X x₀) (c : UV X x₀) : endV (deckV γ c) = endV c := by
  induction γ using Quotient.ind with | _ g => exact endV_shiftV g.2 c

theorem deckV_one (c : UV X x₀) : deckV (1 : Pi1 X x₀) c = c := by
  induction c using UV.ind with | h p => rfl

theorem deckV_mul (γ δ : Pi1 X x₀) (c : UV X x₀) :
    deckV (γ * δ) c = deckV γ (deckV δ c) := by
  induction γ using Quotient.ind with
  | _ g =>
    induction δ using Quotient.ind with
    | _ h =>
      induction c using UV.ind with
      | h p => exact congrArg UV.mk (Subtype.ext (List.append_assoc g.1 h.1 p.1))

theorem extend_deckV (γ : Pi1 X x₀) (eb : X.E × Bool) (c : UV X x₀) :
    extend eb (deckV γ c) = deckV γ (extend eb c) := by
  induction γ using Quotient.ind with | _ g => exact extend_shiftV g.2 eb c

/-- The action of the fundamental group on the edges of the universal cover. -/
def deckE (γ : Pi1 X x₀) (E : UE X x₀) : UE X x₀ :=
  ⟨(deckV γ E.1.1, E.1.2), by simpa using E.2⟩

/-- The action of the fundamental group on the two-cells of the universal cover. -/
def deckF (γ : Pi1 X x₀) (F : UF X x₀) : UF X x₀ :=
  ⟨(deckV γ F.1.1, F.1.2), by simpa using F.2⟩

theorem uLiftPath_deckV (γ : Pi1 X x₀) : ∀ (q : List (X.E × Bool)) (c : UV X x₀) (w : X.V),
    IsPath X.src X.tgt q (endV c) w →
      uLiftPath q (deckV γ c) = (uLiftPath q c).map (fun Eb => (deckE γ Eb.1, Eb.2)) := by
  induction γ using Quotient.ind with | _ g => exact uLiftPath_shiftV g.2

variable (X x₀) in
/-- The deck action of `π₁(X, x₀)` on the universal cover, by concatenation on the left. -/
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
  att_smul := by
    intro γ F
    have hbase  := F.2
    have hatt : IsPath X.src X.tgt (X.att F.1.2) (endV F.1.1) (X.base F.1.2) := by
      rw [hbase]; exact X.att_isLoop F.1.2
    exact uLiftPath_deckV γ (X.att F.1.2) F.1.1 (X.base F.1.2) hatt

/-- **The universal cover is a regular cover with deck group `π₁(X, x₀)`.** -/
theorem isRegular_univProj : IsRegular (univProj X x₀) (univDeck X x₀) := by
  refine ⟨endV_deckV, ?_⟩
  intro c d hcd
  induction c using UV.ind with
  | h p =>
    induction d using UV.ind with
    | h r =>
      have hv : endpt X x₀ p.1 = endpt X x₀ r.1 := hcd
      have hp : IsPath X.src X.tgt p.1 x₀ (endpt X x₀ r.1) := hv ▸ p.2
      have hl := r.2.append (isPath_revPath hp)
      refine ⟨Pi1.mk ⟨_, hl⟩, UV.sound ?_, ?_⟩
      · change Htpy X x₀ (endpt X x₀ ((r.1 ++ revPath p.1) ++ p.1)) ((r.1 ++ revPath p.1) ++ p.1) r.1
        rw [endpt_eq_of_isPath (hl.append hp)]
        simpa only [revPath_revPath] using htpy_remove_backtrack r.2 (isPath_revPath hp)
      · intro γ hγ
        induction γ using Quotient.ind with
        | _ g =>
          apply Quotient.sound
          have h : Htpy X x₀ (endpt X x₀ (g.1 ++ p.1)) (g.1 ++ p.1) r.1 := Quotient.exact hγ
          rw [endpt_eq_of_isPath (g.2.append hp)] at h
          exact h.cancel_tail g.2 hp

end Comb
end FiniteChains
