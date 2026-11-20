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

noncomputable section

namespace FiniteChains
namespace Comb

universe u

variable {X : Complex2.{u}}

/-! ### The endpoint of an edge path -/

/-- The endpoint of a list of oriented edges read from `a`. -/
def endpt (X : Complex2.{u}) : X.V → List (X.E × Bool) → X.V
  | a, [] => a
  | _, eb :: t => endpt X (germTgt X.src X.tgt eb) t

variable (a : X.V)

@[simp] theorem endpt_nil : endpt X a [] = a := rfl

@[simp] theorem endpt_cons (eb : X.E × Bool) (t : List _) :
    endpt X a (eb :: t) = endpt X (germTgt X.src X.tgt eb) t := rfl

theorem endpt_eq_of_isPath {p : List _} {a b : X.V}
    (h : IsPath X.src X.tgt p a b) : endpt X a p = b := by
  induction p generalizing a with
  | nil => exact h
  | cons eb t ih => simp_all

theorem endpt_append (a : X.V) (p q : List _) :
    endpt X a (p ++ q) = endpt X (endpt X a p) q := by
  induction p generalizing a with
  | nil => rfl
  | cons eb t ih => simp_all

/-! ### The vertices of the universal cover -/

variable (X) in
/-- An edge path issued from `x₀`. -/
def PathFrom (x₀ : X.V) :=
  {p : List _ // IsPath X.src X.tgt p x₀ (endpt X x₀ p)}

variable {x₀ : X.V}

/-- Two paths from `x₀` are equivalent when they are homotopic with fixed endpoints. -/
instance pathFromSetoid (X : Complex2.{u}) (x₀ : X.V) : Setoid (PathFrom X x₀) where
  r p q := Htpy X x₀ (endpt X x₀ p.1) p.1 q.1
  iseqv := by
    refine ⟨fun p => Htpy.refl _, ?_, ?_⟩
    · intro p q h
      have he := endpt_eq_of_isPath (h.isPath p.2)
      rw [he]
      exact h.symm
    · intro p q r h h'
      have he := endpt_eq_of_isPath (h.isPath p.2)
      rw [he] at h'
      exact h.trans h'

variable (X) in
/-- The vertices of the universal cover: homotopy classes of edge paths from `x₀`. -/
def UV (x₀ : X.V) := Quotient (pathFromSetoid X x₀)

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
def endV (c : UV X x₀) :=
  Quotient.liftOn c (fun p => endpt X x₀ p.1) (by
    intro p q h
    exact (endpt_eq_of_isPath (h.isPath p.2)).symm)

@[simp] theorem endV_mk (p : PathFrom X x₀) : endV (UV.mk p) = endpt X x₀ p.1 := rfl

@[simp] theorem endV_base : endV (UV.base X x₀) = x₀ := rfl

/-! ### Extending a class by an edge -/

theorem endpt_append_single (a : X.V) (p : List _) (eb : X.E × Bool) :
    endpt X a (p ++ [eb]) = germTgt X.src X.tgt eb := by
  simp [endpt_append]

theorem isPath_append_single {p : List _} {a : X.V}
    (hp : IsPath X.src X.tgt p a (endpt X a p)) (eb : X.E × Bool)
    (h : endpt X a p = germSrc X.src X.tgt eb) :
    IsPath X.src X.tgt (p ++ [eb]) a (endpt X a (p ++ [eb])) := by
  rw [endpt_append_single a p eb]
  exact isPath_append_iff.mpr ⟨germSrc X.src X.tgt eb, h ▸ hp, isPath_single eb⟩

open Classical in
/-- Appending an oriented edge to a path from `x₀` (the path is left unchanged if the edge
does not start at its endpoint). -/
def extendP (eb : X.E × Bool) (p : PathFrom X x₀) :=
  if h : endpt X x₀ p.1 = germSrc X.src X.tgt eb then ⟨p.1 ++ [eb], isPath_append_single p.2 eb h⟩
  else p

variable {p : PathFrom X x₀} {eb : X.E × Bool}

theorem extendP_pos
    (h : endpt X x₀ p.1 = germSrc X.src X.tgt eb) : (extendP eb p).1 = p.1 ++ [eb] := by
  simp_all [extendP, dif_pos]

theorem extendP_neg
    (h : ¬ endpt X x₀ p.1 = germSrc X.src X.tgt eb) : (extendP eb p).1 = p.1 := by
  simp_all [extendP, dif_neg]

/-- Appending an oriented edge to a class of paths. -/
def extend (eb : X.E × Bool) (c : UV X x₀) : UV X x₀ :=
  Quotient.map (extendP eb) (by
    intro p q hpq
    have he := endpt_eq_of_isPath (hpq.isPath p.2)
    by_cases h : endpt X x₀ p.1 = germSrc X.src X.tgt eb
    · show Htpy X x₀ (endpt X x₀ (extendP eb p).1) (extendP eb p).1 (extendP eb q).1
      rw [extendP_pos h, extendP_pos (he.trans h), endpt_append_single x₀ p.1 eb]
      exact Htpy.append_congr (h ▸ p.2) (h ▸ isPath_single eb) hpq (Htpy.refl _)
    · simp_all [extendP, extendP_neg]) c

theorem extend_mk (p : PathFrom X x₀) (eb : X.E × Bool) :
    extend eb (UV.mk p) = UV.mk (extendP eb p) := rfl

section

variable {c : UV X x₀} {eb : X.E × Bool} (h : endV c = germSrc X.src X.tgt eb)
include h

theorem endV_extend :
    endV (extend eb c) = germTgt X.src X.tgt eb := by
  induction c using UV.ind with
  | h p =>
      simp_all [extend_mk, endV_mk, extendP_pos, endpt_append_single]

/-- Extending by an edge and then by its reverse returns the original class. -/
theorem extend_revGerm :
    extend (revGerm eb) (extend eb c) = c := by
  induction c using UV.ind with
  | h p =>
      have h' := h
      have h1 : endpt X x₀ (extendP eb p).1 = germSrc X.src X.tgt (revGerm eb) := by
        rw [extendP_pos h', endpt_append_single x₀ p.1 eb]
        simp
      refine Quotient.sound ?_
      show Htpy X x₀ _
        _ p.1
      rw [extendP_pos h1, extendP_pos h']
      have hp : IsPath X.src X.tgt p.1 x₀ (germSrc X.src X.tgt eb) := h' ▸ p.2
      have hbk : Htpy X (germSrc X.src X.tgt eb) (germSrc X.src X.tgt eb) [eb, revGerm eb] [] := by
        refine Htpy.of_step ⟨?_, rfl, Or.inl ⟨[], [], eb, rfl, rfl⟩⟩
        simp
      have hcongr :=
        Htpy.append_congr hp (by simp) (Htpy.refl _) hbk
      simp_all [endpt_append]

end

/-- Extending a class by a whole path. -/
def extendList (q : List _) (c : UV X x₀) :=
  q.foldl (fun d eb => extend eb d) c

@[simp] theorem extendList_nil (c : UV X x₀) : extendList [] c = c := rfl

@[simp] theorem extendList_cons (eb : X.E × Bool) (q : List _) (c : UV X x₀) :
    extendList (eb :: q) c = extendList q (extend eb c) := rfl

theorem extendList_append (q r : List _) (c : UV X x₀) :
    extendList (q ++ r) c = extendList r (extendList q c) := by
  induction q generalizing c with
  | nil => rfl
  | cons eb t ih => simp_all

/-- Extending the class of `p` by a path `q` issued from its endpoint gives the class of the
concatenation. -/
theorem extendList_mk : ∀ {q : List _} {p r : PathFrom X x₀} {w : X.V},
    IsPath X.src X.tgt q (endpt X x₀ p.1) w → r.1 = p.1 ++ q →
      extendList q (UV.mk p) = UV.mk r := by
  intro q
  induction q with
  | nil =>
      intro p r w _ hr
      refine Quotient.sound ?_
      show Htpy X x₀ _ p.1 r.1
      rw [hr]
      simpa using Htpy.refl p.1
  | cons eb t ih =>
      intro p r w hq hr
      have hend : endpt X x₀ (extendP eb p).1 = germTgt X.src X.tgt eb := by
        simp_all [extendP_pos, endpt_append_single]
      refine ih (w := w) ?_ ?_
      · simp_all
      · simp_all [extendP_pos, hr]

theorem endV_extendList : ∀ {q : List _} {c : UV X x₀} {w : X.V},
    IsPath X.src X.tgt q (endV c) w → endV (extendList q c) = w := by
  intro q
  induction q with
  | nil => simp
  | cons eb t ih =>
      intro c w hq
      refine ih ?_
      simp_all [endV_extend]

/-! ### The universal cover as a complex -/

variable (X x₀) in
/-- The edges of the universal cover: a vertex together with an edge of `X` issued from its
endpoint. -/
def UE := {ce : UV X x₀ × X.E // endV ce.1 = X.src ce.2}

variable (X x₀) in
/-- The two-cells of the universal cover: a vertex together with a two-cell of `X` based at
its endpoint. -/
def UF := {cf : UV X x₀ × X.F // endV cf.1 = X.base cf.2}

variable (ce : UE X x₀)

/-- The initial vertex of an edge of the universal cover. -/
def uSrc := ce.1.1

/-- The terminal vertex of an edge of the universal cover. -/
def uTgt := extend (ce.1.2, true) ce.1.1

/-- The basepoint of a two-cell of the universal cover. -/
def uBase (cf : UF X x₀) := cf.1.1

/-- The lift of an oriented edge at a vertex of the cover. -/
def liftGerm (c : UV X x₀) :
    (eb : X.E × Bool) → endV c = germSrc X.src X.tgt eb → UE X x₀ × Bool
  | (e, true), h => (⟨(c, e), h⟩, true)
  | (e, false), h =>
      (⟨(extend _ c, e), endV_extend h⟩, false)

variable {c : UV X x₀} {e : X.E}

@[simp] theorem liftGerm_true
    (h : endV c = germSrc X.src X.tgt _) :
    liftGerm c (e, true) h = (⟨(c, e), h⟩, true) := rfl

@[simp] theorem liftGerm_false
    (h : endV c = germSrc X.src X.tgt _) :
    liftGerm c _ h =
      (⟨(extend _ c, e), endV_extend (eb := (e, false)) h⟩, false) := rfl

open Classical in
/-- The lift of an edge path at a vertex of the cover. -/
def uLiftPath : List (X.E × Bool) → UV X x₀ → List (UE X x₀ × Bool)
  | [], _ => []
  | eb :: t, c =>
      if h : endV c = germSrc X.src X.tgt eb then
        liftGerm c eb h :: uLiftPath t (extend eb c)
      else []

@[simp] theorem uLiftPath_nil (c : UV X x₀) : uLiftPath [] c = [] := rfl

theorem uLiftPath_cons {eb : X.E × Bool} {t : List _} {c : UV X x₀}
    (h : endV c = germSrc X.src X.tgt eb) :
    uLiftPath (eb :: t) c = liftGerm c eb h :: uLiftPath t (extend eb c) := by
  simp_all [uLiftPath, dif_pos]

/-- The attaching path of a two-cell of the universal cover. -/
def uAtt (cf : UF X x₀) :=
  uLiftPath (X.att cf.1.2) cf.1.1

variable {c : UV X x₀} {eb : X.E × Bool} (h : endV c = germSrc X.src X.tgt eb)

theorem germSrc_liftGerm :
    germSrc uSrc uTgt (liftGerm c eb h) = c := by
  obtain ⟨e, b⟩ := eb
  cases b with
  | true => rfl
  | false =>
      exact extend_revGerm h

theorem germTgt_liftGerm :
    germTgt uSrc uTgt (liftGerm c eb h) = extend eb c := by
  obtain ⟨e, b⟩ := eb
  cases b with
  | true => rfl
  | false => rfl

/-- The lift of a path is a path of the cover, from the given vertex to the extended one. -/
theorem isPath_uLiftPath : ∀ (q : List _) (c : UV X x₀) (w : X.V),
    IsPath X.src X.tgt q (endV c) w → IsPath uSrc uTgt (uLiftPath q c) c (extendList q c) := by
  intro q
  induction q with
  | nil => simp
  | cons eb t ih =>
      intro c w hq
      have h := hq.1
      rw [uLiftPath_cons h, extendList_cons]
      refine ⟨(germSrc_liftGerm h).symm, ?_⟩
      rw [germTgt_liftGerm h]
      refine ih _ w ?_
      simp_all [endV_extend]

/-- Extending a class along the attaching loop of a two-cell based at its endpoint returns
the same class: this is exactly the two-cell cancellation. -/
theorem extendList_att {c : UV X x₀} {f : X.F} (h : endV c = X.base f) :
    extendList (X.att f) c = c := by
  induction c using UV.ind with
  | h p =>
      have h' := h
      have hatt : IsPath X.src X.tgt (X.att f) (endpt X x₀ p.1) (X.base f) := h' ▸ X.att_isLoop f
      have hp :=
        isPath_append_iff.mpr ⟨endpt X x₀ p.1, p.2, hatt⟩
      have hend := endpt_eq_of_isPath hp
      refine (extendList_mk (r := ⟨p.1 ++ X.att f, by simp_all⟩) hatt
        rfl).trans ?_
      refine Quotient.sound ?_
      show Htpy X x₀ _ (p.1 ++ X.att f) p.1
      rw [hend]
      refine Htpy.of_step ⟨hp, h' ▸ p.2, Or.inr ⟨p.1, [], f, ?_, ?_⟩⟩ <;> simp

theorem uAtt_isLoop (cf : UF X x₀) : IsPath uSrc uTgt (uAtt cf) (uBase cf) (uBase cf) := by
  have h := cf.2
  have := isPath_uLiftPath (X.att cf.1.2) cf.1.1 _ (h ▸ X.att_isLoop cf.1.2)
  rwa [extendList_att h] at this

/-- The lift of a path projects back to the path. -/
theorem map_uLiftPath : ∀ (q : List _) (c : UV X x₀) (w : X.V),
    IsPath X.src X.tgt q (endV c) w →
      (uLiftPath q c).map (fun eb => ((eb.1).1.2, eb.2)) = q := by
  intro q
  induction q with
  | nil => simp
  | cons eb t ih =>
      intro c w hq
      rw [uLiftPath_cons hq.1, List.map_cons, ih _ w (by simp_all [endV_extend])]
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
    show X.tgt _ = endV (extend (ce.1.2, true) ce.1.1)
    have h := ce.2
    simp_all [endV_extend]
  base_onF := fun cf => cf.2.symm
  att_onF := by
    intro cf
    have hatt :=
      cf.2 ▸ X.att_isLoop _
    exact (map_uLiftPath _ _ _ hatt).symm

/-! ### The projection is a covering -/

section

variable (hX : IsConnected X)
include hX

theorem endV_surjective : Function.Surjective (endV (X := X) (x₀ := x₀)) := by
  intro v
  obtain ⟨p, hp⟩ := hX x₀ v
  have he := endpt_eq_of_isPath hp
  exact ⟨UV.mk ⟨p, by simp_all⟩, he⟩

omit hX in
theorem univProj_lifts : LocalLifts (univProj X x₀) := by
  constructor
  · intro c
    apply Function.bijective_iff_has_inverse.mpr
    refine ⟨fun g => ⟨liftGerm c g.1 _, germSrc_liftGerm g.2.symm⟩, ?_, ?_⟩
    · rintro ⟨⟨⟨⟨v, e⟩, hv⟩, b⟩, he⟩
      cases b <;> apply Subtype.ext <;> refine Prod.ext (Subtype.ext (Prod.ext ?_ rfl)) rfl
      · subst c
        exact extend_revGerm (eb := (e,true)) hv
      · exact he.symm
    · rintro ⟨⟨e, b⟩, h⟩; cases b <;> rfl
  · exact Function.bijective_iff_has_inverse.mpr
      ⟨fun g => ⟨(g.1.2, g.1.1), g.2.symm⟩, fun _ => rfl, fun _ => rfl⟩

theorem isCovering_univProj : IsCovering (univProj X x₀) :=
  ⟨endV_surjective hX, univProj_lifts⟩

end

theorem isConnected_univCover : IsConnected (uCover X x₀) := by
  -- every vertex is joined to the base vertex
  have key : ∀ c : UV X x₀, ∃ l : List _,
      IsPath (uCover X x₀).src (uCover X x₀).tgt l (UV.base X x₀) c := by
    intro c
    induction c using UV.ind with
    | h p =>
        have hp := p.2
        have hlift := isPath_uLiftPath p.1 (UV.base X x₀) _ hp
        have hext : extendList p.1 (UV.base X x₀) = UV.mk p :=
          extendList_mk hp (by simp)
        aesop
  intro c d
  obtain ⟨l, hl⟩ := key c
  obtain ⟨m, hm⟩ := key d
  refine ⟨revPath l ++ m, ?_⟩
  grind [isPath_append_iff, isPath_revPath]

/-! ### The cover is simply connected -/

/-- Lifting is additive along concatenation. -/
theorem uLiftPath_append : ∀ (l : List _) (m : List _) (c : UV X x₀)
    (w : X.V), IsPath X.src X.tgt l (endV c) w →
      uLiftPath (l ++ m) c = uLiftPath l c ++ uLiftPath m (extendList l c) := by
  intro l
  induction l with
  | nil => simp
  | cons eb t ih =>
      intro m c w hl
      have h := hl.1
      rw [List.cons_append, uLiftPath_cons h, uLiftPath_cons h, extendList_cons,
        ih m _ w (by simp_all [endV_extend])]
      rfl

variable {c : UV X x₀}

variable {l l' : List (X.E × Bool)} {w : X.V}

/-- The explicit lifted word is the unique lift with prescribed source. -/
theorem eq_uLiftPath_of_isPath (L : (uCover X x₀).EdgeWord) (c d : UV X x₀)
    (hL : (uCover X x₀).IsEdgePath L c d) : L = uLiftPath (mapPath (univProj X x₀) L) c := by
  have h := isPath_mapPath (univProj X x₀) hL
  apply liftPath_unique univProj_lifts L _ c d _ hL (isPath_uLiftPath _ c _ h)
  exact (map_uLiftPath _ c _ h).symm

/-- The cover of the component of the base point has local lifts even when
`X` is disconnected. Apply general homotopy lifting and uniqueness there. -/
theorem htpy_uLiftPath (hl : X.IsEdgePath l (endV c) w) (h : Htpy X (endV c) w l l') :
    Htpy (uCover X x₀) c (extendList l c) (uLiftPath l c) (uLiftPath l' c) := by
  obtain ⟨m, hm, he, H⟩ := lift_htpy univProj_lifts (isPath_uLiftPath _ c _ hl) (by
    change Htpy X _ (endV (extendList l c)) _ _
    rw [endV_extendList hl, show mapPath (univProj X x₀) (uLiftPath l c) = l from map_uLiftPath _ c _ hl]
    exact h)
  rwa [eq_uLiftPath_of_isPath m c _ hm, he] at H

theorem extendList_htpy (hl : X.IsEdgePath l (endV c) w) (h : Htpy X (endV c) w l l') :
    extendList l c = extendList l' c :=
  isPath_endpoint_eq ((htpy_uLiftPath hl h).isPath (isPath_uLiftPath _ c _ hl))
    (isPath_uLiftPath _ c _ (h.isPath hl))

/-- **The universal cover is simply connected.** -/
theorem simplyConnected_univCover : SimplyConnected (uCover X x₀) := by
  intro c L hL
  -- `L` is the lift of its projection
  set q := mapPath _ L with hqdef
  have hLq := eq_uLiftPath_of_isPath L c c hL
  have hq := isPath_mapPath (univProj X x₀) hL
  -- the lift of `q` ends where `L` ends, that is at `c`
  have hext : extendList q c = c := by
    have h1 := endpt_eq_of_isPath hL
    have h2 : endpt _ c L = extendList q c := by
      rw [hLq]
      solve_by_elim [endpt_eq_of_isPath, isPath_uLiftPath]
    grind
  -- hence `q` is null-homotopic downstairs
  have hnull : Htpy X (endV c) (endV c) q [] := by
    induction c using UV.ind with
    | h p =>
        have hpq :=
          isPath_append_iff.mpr ⟨endpt X x₀ p.1, p.2, hq⟩
        have hendpq := endpt_eq_of_isPath hpq
        have hclass : UV.mk (⟨p.1 ++ q, by grind⟩) = UV.mk p := by
          rw [← extendList_mk (r := ⟨p.1 ++ q, by grind⟩) hq rfl]
          exact hext
        have h1 : Htpy X x₀ (endpt X x₀ p.1) (p.1 ++ q) p.1 := by
          have := Quotient.exact hclass
          have h' : Htpy X x₀ _ _ p.1 := this; rwa [hendpq] at h'
        set v := endpt X x₀ p.1 with hvdef
        have hrp := isPath_revPath p.2
        have hB := htpy_revPath_append p.2
        have hC : Htpy X v v _ _ :=
          Htpy.append_congr (isPath_append_iff.mpr ⟨x₀, hrp, p.2⟩) hq hB (Htpy.refl _)
        have hqA : Htpy X v v q (revPath p.1 ++ (p.1 ++ q)) := by
          have := hC.symm
          simpa using this
        exact (hqA.trans (Htpy.append_congr hrp hpq (Htpy.refl _) h1)).trans hB
  -- and therefore so is `L` upstairs
  have := htpy_uLiftPath hq hnull
  rw [hext] at this
  rw [hLq]
  assumption

/-! ### The deck action -/

variable (g : Loop X x₀) (p : PathFrom X x₀)

/-- Concatenating a loop at `x₀` in front of a path from `x₀`. -/
def deckP : PathFrom X x₀ :=
  ⟨g.1 ++ p.1, by
    have hend : endpt X x₀ (g.1 ++ p.1) = endpt X x₀ p.1 := by
      grind [endpt_append, endpt_eq_of_isPath]
    rw [hend]
    exact isPath_append_iff.mpr ⟨x₀, g.2, p.2⟩⟩

theorem endpt_deckP :
    endpt X x₀ (deckP g p).1 = endpt X x₀ p.1 := by
  show endpt X x₀ (g.1 ++ p.1) = endpt X x₀ p.1
  grind [endpt_append, endpt_eq_of_isPath]

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

theorem deckV_one (c : UV X x₀) : deckV 1 c = c := by
  induction c using UV.ind with
  | h p =>
      rfl

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
                  _

variable (γ : Pi1 X x₀)

theorem extend_deckV (eb : X.E × Bool) (c : UV X x₀) :
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
              simp_all [extendP_pos]
            · simp_all [endpt_deckP, extendP_neg, extendP]
          refine Quotient.sound ?_
          show Htpy X x₀ _ _
            _
          rw [hl]
          exact Htpy.refl _

/-- The action of the fundamental group on the edges of the universal cover. -/
def deckE (E : UE X x₀) : UE X x₀ :=
  ⟨(deckV γ E.1.1, E.1.2), by rw [endV_deckV]; exact E.2⟩

/-- The action of the fundamental group on the two-cells of the universal cover. -/
def deckF (F : UF X x₀) : UF X x₀ :=
  ⟨(deckV γ F.1.1, F.1.2), by rw [endV_deckV]; exact F.2⟩

theorem liftGerm_deckV {c : UV X x₀} {eb : X.E × Bool} (γ : Pi1 X x₀)
    (h : endV c = germSrc X.src X.tgt eb) (h' : endV _ = germSrc X.src X.tgt eb) :
    liftGerm (deckV γ c) eb h' = (deckE γ (liftGerm c eb h).1, (liftGerm c eb h).2) := by
  obtain ⟨e, b⟩ := eb
  cases b with
  | true => rfl
  | false =>
      refine Prod.ext ?_ rfl
      refine Subtype.ext (Prod.ext ?_ rfl)
      apply extend_deckV

theorem uLiftPath_deckV (γ : Pi1 X x₀) : ∀ (q : List _) (c : UV X x₀) (w : X.V),
    IsPath X.src X.tgt q (endV c) w →
      uLiftPath q (deckV γ c) = (uLiftPath q c).map (fun Eb => (deckE γ Eb.1, Eb.2)) := by
  intro q
  induction q with
  | nil => simp
  | cons eb t ih =>
      intro c w hq
      have h := hq.1
      have h' : endV (deckV γ c) = germSrc X.src X.tgt eb := by rw [endV_deckV]; exact h
      rw [uLiftPath_cons h', uLiftPath_cons h, List.map_cons, liftGerm_deckV γ h h',
        extend_deckV γ eb c,
        ih _ w (by simp_all [endV_extend])]

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
  tgt_smul := fun γ E => extend_deckV γ _ _
  base_smul := fun _ _ => rfl
  att_smul := by
    intro γ F
    have hatt : IsPath X.src X.tgt (X.att F.1.2) (endV F.1.1) (X.base F.1.2) := by
      rw [F.2]; apply X.att_isLoop
    apply uLiftPath_deckV <;> assumption

/-- **The universal cover is a regular cover with deck group `π₁(X, x₀)`.** -/
theorem isRegular_univProj : IsRegular (univProj X x₀) (univDeck X x₀) := by
  constructor
  · apply endV_deckV
  · intro c d hcd
    induction c using UV.ind with
    | h p =>
        induction d using UV.ind with
        | h r =>
            have hv : endpt X x₀ p.1 = endpt X x₀ r.1 := hcd
            have hvp : IsPath X.src X.tgt p.1 x₀ (endpt X x₀ r.1) := by rw [← hv]; exact p.2
            have hrev := isPath_revPath hvp
            have hrp :=
              isPath_append_iff.mpr ⟨endpt X x₀ r.1, r.2, hrev⟩
            refine ⟨Quotient.mk _ ⟨r.1 ++ revPath p.1, hrp⟩, ?_, ?_⟩
            · -- the translate of `p` by this loop is `r`
              refine Quotient.sound ?_
              show Htpy X x₀ (endpt X x₀ ((r.1 ++ revPath p.1) ++ p.1))
                ((r.1 ++ revPath p.1) ++ p.1) r.1
              have hend : endpt X x₀ ((r.1 ++ revPath p.1) ++ p.1) = endpt X x₀ r.1 := by
                rw [endpt_append, endpt_eq_of_isPath hrp]
                exact hv
              have hA :=
                Htpy.append_congr r.2 (isPath_append_iff.mpr ⟨x₀, hrev, hvp⟩) (Htpy.refl _) (htpy_revPath_append hvp)
              simp_all
            · -- uniqueness
              rintro γ hγ
              induction γ using Quotient.ind with
              | _ g =>
                  refine Quotient.sound ?_
                  have hg : Htpy X x₀ (endpt X x₀ (g.1 ++ p.1)) _ r.1 :=
                    Quotient.exact hγ
                  have hgp :=
                    isPath_append_iff.mpr ⟨x₀, g.2, hvp⟩
                  rw [(endpt_eq_of_isPath hgp)] at hg
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
