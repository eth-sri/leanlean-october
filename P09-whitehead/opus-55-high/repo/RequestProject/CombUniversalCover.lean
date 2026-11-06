import RequestProject.CombPi1
import RequestProject.Tac
noncomputable section


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

bwd

namespace FiniteChains.Comb

universe u

variable {X : Complex2.{u}}

/-! ### The endpoint of an edge path -/

/-- The endpoint of a list of oriented edges read from `a`. -/
def endpt (X : Complex2.{u}) : X.V → List (X.E × Bool) → X.V
  | a, [] => a
  | _, eb :: t => endpt X (gTgtX X eb) t

@[simp] theorem endpt_nil a : endpt X a [] = a := rfl

@[simp] theorem endpt_cons a eb t :
    endpt X a (eb :: t) = endpt X (gTgtX X eb) t := rfl

theorem endpt_eq_of_isPath
    (h : IsPathX X p a b) : endpt X a p = b := by
  induction p generalizing a <;> simp_all

theorem endpt_append a p q :
    endpt X a (p ++ q) = endpt X (endpt X a p) q := by
  induction p generalizing a <;> simp_all

/-! ### The vertices of the universal cover -/

variable (X) in
/-- An edge path issued from `x₀`. -/
def PathFrom (x₀ : X.V) : Type u :=
  {p : List (X.E × Bool) // IsPathX X p x₀ (endpt X x₀ p)}

variable {x₀ : X.V}

/-- Two paths from `x₀` are equivalent when they are homotopic with fixed endpoints. -/
instance pathFromSetoid X x₀ : Setoid (PathFrom X x₀) where
  r p q := Htpy X x₀ (endpt X x₀ p.1) p.1 q.1
  iseqv := by
    refine ⟨fun p => Htpy.refl _, ?_, ?_⟩
    · intro p q h
      have hq := h.isPath p.2
      have he := endpt_eq_of_isPath hq
      rw [he]
      exact h.symm
    · intro p q r h h'
      have hq := h.isPath p.2
      have he := endpt_eq_of_isPath hq
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
def UV.base X x₀ : UV X x₀ := UV.mk ⟨[], rfl⟩

/-- The endpoint of (any representative of) a class. -/
def endV (c : UV X x₀) :=
  c.liftOn _ (by
    intro p q h
    have hq := h.isPath p.2
    exact (endpt_eq_of_isPath hq).symm)

@[simp] theorem endV_mk (p : PathFrom X x₀) : endV (UV.mk p) = endpt X x₀ p.1 := rfl

@[simp] theorem endV_base : endV (UV.base X x₀) = x₀ := rfl

/-! ### Extending a class by an edge -/

theorem endpt_append_single a p eb
    (h : endpt X a p = gSrcX X eb) :
    endpt X a (p ++ [eb]) = gTgtX X eb := by
  rw [endpt_append, h]
  rfl

theorem isPath_append_single
    (hp : IsPathX X p a (endpt X a p)) eb
    (h : endpt X a p = gSrcX X eb) :
    IsPathX X (p ++ [eb]) a (endpt X a (p ++ [eb])) := by
  rw [endpt_append_single a p eb h]
  exact isPath_append_iff.mpr (by simp_all)

open Classical in
/-- Appending an oriented edge to a path from `x₀` (the path is left unchanged if the edge
does not start at its endpoint). -/
def extendP (eb : X.E × Bool) (p : PathFrom X x₀) : PathFrom X x₀ :=
  if h : endpt X x₀ p.1 = gSrcX X eb then ⟨p.1 ++ [eb], isPath_append_single p.2 eb h⟩
  else p

theorem extendP_pos {p : PathFrom X x₀} {eb}
    (h : endpt X x₀ p.1 = gSrcX X eb) : (extendP eb p).1 = p.1 ++ [eb] := by
  classical
  simp [extendP, dif_pos h]

theorem extendP_neg {p : PathFrom X x₀} {eb}
    (h : ¬ endpt X x₀ p.1 = gSrcX X eb) : (extendP eb p).1 = p.1 := by
  classical
  simp [extendP, dif_neg h]

/-- Appending an oriented edge to a class of paths. -/
def extend (eb : X.E × Bool) (c : UV X x₀) : UV X x₀ :=
  Quotient.map (extendP eb) (by
    intro p q hpq
    have hq := hpq.isPath p.2
    have he := endpt_eq_of_isPath hq
    by_cases h : endpt X x₀ p.1 = gSrcX X eb
    · show Htpy X x₀ (endpt X x₀ (extendP eb p).1) (extendP eb p).1 (extendP eb q).1
      rw [extendP_pos h, extendP_pos (he.trans h), endpt_append_single x₀ p.1 eb h]
      exact Htpy.append_congr (h ▸ p.2) (h ▸ isPath_single eb) hpq (Htpy.refl _)
    · show Htpy X x₀ (endpt X x₀ (extendP eb p).1) (extendP eb p).1 (extendP eb q).1
      rw [extendP_neg h, extendP_neg (by simp_all)]
      exact hpq) c

theorem extend_mk (p : PathFrom X x₀) eb :
    extend eb (UV.mk p) = UV.mk (extendP eb p) := rfl

theorem endV_extend {c : UV X x₀} {eb} (h : endV c = gSrcX X eb) :
    endV (extend eb c) = gTgtX X eb := by
  induction c using UV.ind with
  | h p =>
      have h' := h
      rw [extend_mk, endV_mk, extendP_pos h', endpt_append_single x₀ p.1 eb h']

/-- Extending by an edge and then by its reverse returns the original class. -/
theorem extend_revGerm {c : UV X x₀} {eb} (h : endV c = gSrcX X eb) :
    extend (revGerm eb) (extend eb c) = c := by
  induction c using UV.ind with
  | h p =>
      have h' : endpt X x₀ p.1 = gSrcX X eb := h
      have h1 : endpt X x₀ (extendP eb p).1 = gSrcX X (revGerm eb) := by
        rw [extendP_pos h', endpt_append_single x₀ p.1 eb h']
        simp
      refine Quotient.sound ?_
      show Htpy X x₀ (endpt X x₀ (extendP (revGerm eb) (extendP eb p)).1)
        (extendP (revGerm eb) (extendP eb p)).1 p.1
      rw [extendP_pos h1, extendP_pos h']
      have hp := h' ▸ p.2
      have hbk : Htpy X (gSrcX X eb) (gSrcX X eb) [eb, revGerm eb] [] := by
        refine Htpy.of_step ⟨?_, rfl, Or.inl ⟨[], [], eb, rfl, rfl⟩⟩
        simp
      have hcongr :=
        Htpy.append_congr hp (by simp) (Htpy.refl _) hbk
      have hend : endpt X x₀ (p.1 ++ [eb] ++ [revGerm eb]) = gSrcX X eb := by
        simp [endpt_append, h']
      simp_all

/-- Extending a class by a whole path. -/
def extendList (q : List (X.E × Bool)) (c : UV X x₀) :=
  q.foldl (fun d eb => extend eb d) c

@[simp] theorem extendList_nil (c : UV X x₀) : extendList [] c = c := rfl

@[simp] theorem extendList_cons eb q (c : UV X x₀) :
    extendList (eb :: q) c = extendList q (extend eb c) := rfl

theorem extendList_append q r (c : UV X x₀) :
    extendList (q ++ r) c = extendList r (extendList q c) := by
  induction q generalizing c <;> simp_all

/-- Extending the class of `p` by a path `q` issued from its endpoint gives the class of the
concatenation. -/
theorem extendList_mk : ∀ {q} {p r : PathFrom X x₀} {w},
    IsPathX X q (endpt X x₀ p.1) w → r.1 = p.1 ++ q →
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
      have h' := hq.1
      have hend : endpt X x₀ (extendP eb p).1 = gTgtX X eb := by
        rw [extendP_pos h', endpt_append_single x₀ p.1 eb h']
      refine ih (p := extendP eb p) (r := r) (w := w) ?_ ?_
      · simp_all
      · rw [extendP_pos h', hr]; simp

theorem endV_extendList : ∀ {q} {c : UV X x₀} {w},
    IsPathX X q (endV c) w → endV (extendList q c) = w := by
  intro q
  induction q with
  | nil => simp
  | cons eb t ih =>
      intro c w hq
      have h := hq.1
      refine ih (c := extend eb c) (w := w) ?_
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
def uSrc (ce : UE X x₀) := ce.1.1

/-- The terminal vertex of an edge of the universal cover. -/
def uTgt (ce : UE X x₀) := extend (ce.1.2, true) ce.1.1

/-- The basepoint of a two-cell of the universal cover. -/
def uBase (cf : UF X x₀) := cf.1.1

/-- The lift of an oriented edge at a vertex of the cover. -/
def liftGerm (c : UV X x₀) :
    (eb : X.E × Bool) → endV c = gSrcX X eb → UE X x₀ × Bool
  | (e, true), h => (⟨(c, e), h⟩, true)
  | (e, false), h =>
      (⟨(extend (e, false) c, e), endV_extend (c := c) (eb := (e, false)) h⟩, false)

@[simp] theorem liftGerm_true {c : UV X x₀} {e}
    h :
    liftGerm c (e, true) h = (⟨(c, e), h⟩, true) := rfl

@[simp] theorem liftGerm_false {c : UV X x₀} {e}
    h :
    liftGerm c (e, false) h =
      (⟨(extend (e, false) c, e), endV_extend (c := c) (eb := (e, false)) h⟩, false) := rfl

open Classical in
/-- The lift of an edge path at a vertex of the cover. -/
def uLiftPath : List (X.E × Bool) → UV X x₀ → List (UE X x₀ × Bool)
  | [], _ => []
  | eb :: t, c =>
      if h : endV c = gSrcX X eb then
        liftGerm c eb h :: uLiftPath t (extend eb c)
      else []

@[simp] theorem uLiftPath_nil (c : UV X x₀) : uLiftPath [] c = [] := rfl

theorem uLiftPath_cons {c : UV X x₀}
    h :
    uLiftPath (eb :: t) c = liftGerm c eb h :: uLiftPath t (extend eb c) := by
  rw [uLiftPath, dif_pos h]

/-- The attaching path of a two-cell of the universal cover. -/
def uAtt (cf : UF X x₀) :=
  uLiftPath (X.att cf.1.2) cf.1.1

theorem germSrc_liftGerm {c : UV X x₀} {eb}
    h :
    germSrc uSrc uTgt (liftGerm c eb h) = c := by
  cases' eb with e b
  cases b with
  | true => rfl
  | false =>
      exact extend_revGerm (eb := (e, false)) h

theorem germTgt_liftGerm {c : UV X x₀} {eb}
    h :
    germTgt uSrc uTgt (liftGerm c eb h) = extend eb c := by
  cases' eb with e b
  cases b <;> aesop

/-- The lift of a path is a path of the cover, from the given vertex to the extended one. -/
theorem isPath_uLiftPath : ∀ q (c : UV X x₀) w,
    IsPathX X q (endV c) w → IsPath uSrc uTgt (uLiftPath q c) c (extendList q c) := by
  intro q
  induction q with
  | nil => simp
  | cons eb t ih =>
      intro c w hq
      have h := hq.1
      rw [uLiftPath_cons h, extendList_cons]
      refine ⟨(germSrc_liftGerm h).symm, ?_⟩
      rw [germTgt_liftGerm h]
      refine ih (extend eb c) w ?_
      rw [endV_extend h]
      exact hq.2

/-- Extending a class along the attaching loop of a two-cell based at its endpoint returns
the same class: this is exactly the two-cell cancellation. -/
theorem extendList_att {c : UV X x₀} {f} (h : endV c = X.base f) :
    extendList (X.att f) c = c := by
  induction c using UV.ind with
  | h p =>
      have h' : endpt X x₀ p.1 = X.base f := h
      have hatt := h' ▸ X.att_isLoop f
      have hp : IsPathX X (p.1 ++ X.att f) x₀ (X.base f) :=
        isPath_append_iff.mpr (by grind)
      have hend := endpt_eq_of_isPath hp
      refine (extendList_mk (p := p) (r := ⟨p.1 ++ X.att f, by simp_all⟩) hatt
        rfl).trans ?_
      refine Quotient.sound ?_
      show Htpy X x₀ (endpt X x₀ (p.1 ++ X.att f)) (p.1 ++ X.att f) p.1
      rw [hend]
      refine Htpy.of_step ⟨hp, h' ▸ p.2, Or.inr ⟨p.1, [], f, ?_, ?_⟩⟩ <;> simp

theorem uAtt_isLoop (cf : UF X x₀) : IsPath uSrc uTgt (uAtt cf) (uBase cf) (uBase cf) := by
  have h := cf.2
  have hatt :=
    h ▸ X.att_isLoop cf.1.2
  have := isPath_uLiftPath _ cf.1.1 _ hatt
  rwa [extendList_att h] at this

/-- The lift of a path projects back to the path. -/
theorem map_uLiftPath : ∀ q c w,
    IsPathX X q (endV c) w →
      (uLiftPath q c).map (fun eb => ((eb.1 : UE X x₀).1.2, eb.2)) = q := by
  intro q
  induction q with
  | nil => simp
  | cons eb t ih =>
      intro c w hq
      have h := hq.1
      rw [uLiftPath_cons h, List.map_cons, ih _ w (by simp_all [endV_extend h])]
      cases' eb with e b
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
    have h := ce.2
    rw [endV_extend h]
    rfl
  base_onF := fun cf => cf.2.symm
  att_onF := by
    intro cf
    have h := cf.2
    have hatt : IsPathX X (X.att cf.1.2) (endV cf.1.1) (X.base cf.1.2) :=
      h ▸ X.att_isLoop cf.1.2
    exact (map_uLiftPath (X.att cf.1.2) cf.1.1 (X.base cf.1.2) hatt).symm

/-! ### The projection is a covering -/

theorem endV_surjective (hX : IsConnected X) : Function.Surjective (endV (X := X) (x₀ := x₀)) := by
  intro v
  cases' hX x₀ v with p hp
  have he := endpt_eq_of_isPath hp
  exact ⟨UV.mk ⟨p, by simp_all⟩, he⟩

theorem isCovering_univProj (hX : IsConnected X) : IsCovering (univProj X x₀) := by
  refine ⟨endV_surjective hX, ?_, ?_⟩
  · intro c
    constructor
    · rintro ⟨⟨E, b⟩, hE⟩ ⟨⟨E', b'⟩, hE'⟩ heq
      have hpair := congrArg Subtype.val heq
      have hb : b = b' := congrArg Prod.snd hpair
      have he : E.1.2 = E'.1.2 := congrArg Prod.fst hpair
      subst hb
      have hEE : E = E' := by
        cases b with
        | true =>
            have h1 : E.1.1 = c := hE
            have h2 : E'.1.1 = c := hE'
            exact Subtype.ext (by grind)
        | false =>
            have h1 := hE
            have h2 := hE'
            have k1 : E.1.1 = extend (E.1.2, false) c := by
              rw [← h1]
              exact (extend_revGerm (eb := (E.1.2, true)) E.2).symm
            have k2 : E'.1.1 = extend (E'.1.2, false) c := by
              rw [← h2]
              exact (extend_revGerm (eb := (E'.1.2, true)) E'.2).symm
            refine Subtype.ext (Prod.ext ?_ he)
            simp_all
      subst hEE
      rfl
    · rintro ⟨⟨e, b⟩, hb⟩
      cases b with
      | true =>
          have hsrc := hb.symm
          refine ⟨⟨(⟨(c, e), hsrc⟩, true), rfl⟩, ?_⟩
          rfl
      | false =>
          have h := hb.symm
          have hend := endV_extend h
          refine ⟨⟨(⟨(extend (e, false) c, e), hend⟩, false), ?_⟩, ?_⟩
          · exact extend_revGerm (eb := (e, false)) h
          rfl
  · constructor
    · rintro ⟨⟨c, f⟩, h⟩ ⟨⟨c', f'⟩, h'⟩ heq
      have hpair : (f, c) = (f', c') := congrArg Subtype.val heq
      simp_all
    · rintro ⟨⟨f, c⟩, h⟩
      exact ⟨⟨(c, f), h.symm⟩, rfl⟩

theorem isConnected_univCover : IsConnected (uCover X x₀) := by
  -- every vertex is joined to the base vertex
  have key : ∀ c : UV X x₀, ∃ l : List ((uCover X x₀).E × Bool),
      IsPathX (uCover X x₀) l (UV.base X x₀) c := by
    intro c
    induction c using UV.ind with
    | h p =>
        have hp := p.2
        have hlift := isPath_uLiftPath p.1 (UV.base X x₀) _ hp
        have hext : extendList p.1 (UV.base X x₀) = UV.mk p :=
          extendList_mk (p := ({ val := [], property := rfl })) (r := p)
            (w := endpt X x₀ p.1) hp (by simp)
        aesop
  intro c d
  cases' key c with l hl
  cases' key d with m hm
  refine ⟨revPath (X := uCover X x₀) l ++ m, ?_⟩
  exact isPath_append_iff (X := uCover X x₀).mpr
    ⟨UV.base X x₀, isPath_revPath (X := uCover X x₀) hl, hm⟩

/-! ### The cover is simply connected -/

/-- Lifting is additive along concatenation. -/
theorem uLiftPath_append : ∀ l m (c : UV X x₀)
    w, IsPathX X l (endV c) w →
      uLiftPath (l ++ m) c = uLiftPath l c ++ uLiftPath m (extendList l c) := by
  intro l
  induction l with
  | nil => simp
  | cons eb t ih =>
      intro m c w hl
      have h := hl.1
      simp [List.cons_append, uLiftPath_cons h, extendList_cons, ih m _ w (by rw [endV_extend h]; exact hl.2)]

/-- Homotopic paths extend a class in the same way. -/
theorem extendList_htpy {c : UV X x₀} {l l'} {w}
    (hl : IsPathX X l (endV c) w) (h : Htpy X (endV c) w l l') :
    extendList l c = extendList l' c := by
  induction c using UV.ind with
  | h p =>
      have hl' : IsPathX X l' (endpt X x₀ p.1) w := h.isPath hl
      have hpl :=
        isPath_append_iff.mpr ⟨endpt X x₀ p.1, p.2, hl⟩
      have hpl' : IsPathX X (p.1 ++ l') x₀ w :=
        isPath_append_iff.mpr (by grind)
      have hend := endpt_eq_of_isPath hpl
      have hend' := endpt_eq_of_isPath hpl'
      rw [extendList_mk (p := p) (r := ⟨p.1 ++ l, by simp_all⟩) hl rfl,
        extendList_mk (p := p) (r := ⟨p.1 ++ l', by simp_all⟩) hl' rfl]
      refine Quotient.sound ?_
      show Htpy X x₀ (endpt X x₀ (p.1 ++ l)) (p.1 ++ l) (p.1 ++ l')
      rw [hend]
      exact Htpy.append_congr p.2 hl (Htpy.refl _) h

/-- Lifting turns an elementary homotopy of the base into a homotopy of the cover. -/
theorem htpy_step_uLiftPath {w}
    (hstep : Step X (endV c) w l l') :
    Htpy (uCover X x₀) c (extendList l c) (uLiftPath l c) (uLiftPath l' c) := by
  obtain ⟨hl, hl', hc⟩ := hstep
  have hext :=
    (extendList_htpy hl (Htpy.of_step (by tauto))).symm
  have hpath := isPath_uLiftPath l c w hl
  have hpath' : IsPathX (uCover X x₀) (uLiftPath l' c) c
      (extendList l c) := by
    rw [← hext]; exact isPath_uLiftPath l' c w hl'
  rcases hc with ⟨p, q, eb, hleq, hl'eq⟩ | ⟨p, q, f, hleq, hl'eq⟩
  · subst hleq; subst hl'eq
    obtain ⟨b₁, hp, hrest⟩ := isPath_append_iff.mp hl
    have hc₁ : endV (extendList p c) = b₁ := endV_extendList hp
    set c₁ := extendList p c with hc₁def
    have h₁ : endV c₁ = gSrcX X eb := by simp_all
    have h₂ : endV (extend eb c₁) = gSrcX X (revGerm eb) := by
      rw [endV_extend h₁]; simp
    have hrev : liftGerm _ _ h₂
        = revGerm (X := uCover X x₀) (liftGerm c₁ eb h₁) := by
      cases' eb with e bb
      cases bb with
      | true =>
          refine Prod.ext ?_ rfl
          refine Subtype.ext (Prod.ext ?_ rfl)
          exact extend_revGerm (eb := (e, true)) h₁
      | false =>
          rfl
    refine Htpy.of_step ⟨hpath, hpath', Or.inl ⟨uLiftPath p c, uLiftPath q c₁,
      liftGerm c₁ eb h₁, ?_, ?_⟩⟩
    · rw [uLiftPath_append p _ c b₁ hp, uLiftPath_cons h₁, uLiftPath_cons h₂, hrev, extend_revGerm h₁]
    · rw [uLiftPath_append p q c b₁ hp]
  · subst hleq; subst hl'eq
    by_cases hnil : X.att f = []
    · -- a two-cell with empty attaching path cancels nothing
      rw [hnil]
      simp [List.append_nil]
      exact Htpy.refl _
    · obtain ⟨g, t, hgt⟩ : ∃ g t, X.att f = g :: t := by
        cases hc : X.att f <;> simp_all
      obtain ⟨b₂, hpa, hq⟩ := isPath_append_iff.mp hl
      obtain ⟨b₁, hp, hatt⟩ := isPath_append_iff.mp hpa
      have hc₁ : endV (extendList p c) = b₁ := endV_extendList hp
      set c₁ := extendList p c with hc₁def
      have hb₁ : b₁ = X.base f := by
        have h2 : X.base f = gSrcX X g := by
          have h := X.att_isLoop f; simp_all
        simp_all
      have hbase : endV c₁ = X.base f := by simp_all
      have hattpath : IsPathX X (X.att f) (endV c₁) (X.base f) := by
        rw [hbase]; exact X.att_isLoop f
      have hpq : IsPathX X (p ++ X.att f) (endV c) (X.base f) :=
        isPath_append_iff.mpr (by simp_all)
      have hextpa : extendList (p ++ X.att f) c = c₁ := by
        rw [extendList_append, extendList_att hbase]
      refine Htpy.of_step ⟨hpath, hpath', Or.inr ⟨uLiftPath p c, uLiftPath q c₁,
        ⟨(c₁, f), hbase⟩, ?_, ?_⟩⟩
      · rw [uLiftPath_append _ q c _ hpq, hextpa,
          uLiftPath_append p _ c b₁ hp]
        rfl
      · rw [uLiftPath_append p q c b₁ hp]

/-- **Lifting is compatible with homotopy**: homotopic paths of the base have homotopic
lifts. -/
theorem htpy_uLiftPath {q q'} {w}
    (hq : IsPathX X q (endV c) w) (h : Htpy X (endV c) w q q') :
    Htpy (uCover X x₀) c (extendList q c) (uLiftPath q c) (uLiftPath q' c) := by
  induction h with
  | refl => exact Htpy.refl _
  | @tail m m' hstep hlast ih =>
      have hextm := (extendList_htpy hq hstep).symm
      refine ih.trans ?_
      rcases hlast with hs | hs
      · have := htpy_step_uLiftPath (c := c) (l := m) (l' := m') (w := w) hs
        simp_all
      · have hm' := hs.1
        have hextm' :=
          (extendList_htpy hm' (Htpy.of_step hs)).trans hextm
        have := htpy_step_uLiftPath (c := c) (l := m') (l' := m) (w := w) hs
        rw [hextm'] at this
        exact this.symm

/-- **Unique path lifting**: a path of the cover is the lift of its projection. -/
theorem eq_uLiftPath_of_isPath : ∀ L (c d : UV X x₀),
    IsPathX (uCover X x₀) L c d →
      L = uLiftPath (mapPath (univProj X x₀) L) c := by
  intro L
  induction L with
  | nil => simp
  | cons Eb T ih =>
      rintro c d ⟨hc, hrest⟩
      cases' Eb with E b
      have hE := E.2
      cases b with
      | true =>
          have hcE : c = E.1.1 := hc
          have h : endV c = gSrcX X (E.1.2, true) := by simp_all
          have hlift : liftGerm c _ h = (E, true) := by
            aesop
          have hnext : extend (E.1.2, true) c
              = gTgtX (uCover X x₀) (E, true) := by
            tauto
          show (E, true) :: T = uLiftPath ((E.1.2, true) :: mapPath (univProj X x₀) T) c
          rw [uLiftPath_cons h, hlift, hnext]
          tauto
      | false =>
          have hcE : c = extend (E.1.2, true) E.1.1 := hc
          have hEc : extend (E.1.2, false) c = E.1.1 := by
            rw [hcE]
            exact extend_revGerm (eb := (E.1.2, true)) hE
          have h : endV c = gSrcX X (E.1.2, false) := by
            rw [hcE, endV_extend (c := E.1.1) (eb := (E.1.2, true)) hE]
            rfl
          have hlift : liftGerm c _ h = (E, false) := by
            simp_all
          have hnext := hEc
          show (E, false) :: T = uLiftPath ((E.1.2, false) :: mapPath (univProj X x₀) T) c
          rw [uLiftPath_cons h, hlift, hnext]
          tauto

/-- **The universal cover is simply connected.** -/
theorem simplyConnected_univCover : SimplyConnected (uCover X x₀) := by
  intro c L hL
  -- `L` is the lift of its projection
  set q := mapPath (univProj X x₀) L with hqdef
  have hLq := eq_uLiftPath_of_isPath L c c hL
  have hq := isPath_mapPath (univProj X x₀) hL
  -- the lift of `q` ends where `L` ends, that is at `c`
  have hext : extendList q c = c := by
    have h1 := endpt_eq_of_isPath hL
    have h2 : endpt _ c L = extendList q c := by
      rw [hLq]
      exact endpt_eq_of_isPath (isPath_uLiftPath q c _ hq)
    grind
  -- hence `q` is null-homotopic downstairs
  have hnull : Htpy X (endV c) (endV c) q [] := by
    induction c using UV.ind with
    | h p =>
        have hpq : IsPathX X (p.1 ++ q) x₀ (endpt X x₀ p.1) :=
          isPath_append_iff.mpr ⟨endpt X x₀ p.1, p.2, hq⟩
        have hendpq := endpt_eq_of_isPath hpq
        have hclass : UV.mk ⟨p.1 ++ q, by grind⟩ = UV.mk p := by
          rw [← extendList_mk (p := p) (r := ⟨p.1 ++ q, by grind⟩) hq rfl]
          exact hext
        have h1 : Htpy X x₀ (endpt X x₀ p.1) (p.1 ++ q) p.1 := by
          have := Quotient.exact hclass
          have h' : Htpy X x₀ (endpt X x₀ (p.1 ++ q)) (p.1 ++ q) p.1 := this
          grind
        set v := endpt X x₀ p.1 with hvdef
        have hrp := isPath_revPath p.2
        have hA :=
          Htpy.append_congr hrp hpq (Htpy.refl _) h1
        have hB := htpy_revPath_append p.2
        have hC : Htpy X v v ((revPath p.1 ++ p.1) ++ q) (([]) ++ q) :=
          Htpy.append_congr (isPath_append_iff.mpr ⟨x₀, hrp, p.2⟩) hq hB (Htpy.refl _)
        have hqA : Htpy X v v q (revPath p.1 ++ (p.1 ++ q)) := by
          have := hC.symm
          grind
        exact (hqA.trans hA).trans hB
  -- and therefore so is `L` upstairs
  have := htpy_uLiftPath (c := c) (q := q) (q' := []) hq hnull
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
    exact isPath_append_iff.mpr (by grind)⟩

theorem endpt_deckP g (p : PathFrom X x₀) :
    endpt X x₀ (deckP g p).1 = endpt X x₀ p.1 := by
  show endpt X x₀ (g.1 ++ p.1) = endpt X x₀ p.1
  rw [endpt_append, endpt_eq_of_isPath g.2]

/-- The action of the fundamental group on the vertices of the universal cover. -/
def deckV (γ : Pi1 X x₀) (c : UV X x₀) : UV X x₀ :=
  Quotient.map₂ deckP (by
    intro g g' hg p p' hp
    show Htpy X x₀ (endpt X x₀ (deckP g p).1) (deckP g p).1 (deckP g' p').1
    rw [endpt_deckP]
    exact Htpy.append_congr g.2 p.2 hg hp) γ c

@[simp] theorem deckV_mk g (p : PathFrom X x₀) :
    deckV (Quotient.mk _ g) (UV.mk p) = UV.mk (deckP g p) := rfl

@[simp] theorem endV_deckV γ (c : UV X x₀) : endV (deckV γ c) = endV c := by
  induction γ using Quotient.ind with
  | _ g =>
      induction c using UV.ind with
      | h p => exact endpt_deckP g p

theorem deckV_one c : deckV (1 : Pi1 X x₀) c = c := by
  induction c using UV.ind <;> aesop

theorem deckV_mul γ δ (c : UV X x₀) :
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
                Htpy.refl (X := X) (a := x₀) (b := endpt X x₀ ((g.1 ++ g'.1) ++ p.1))
                  _

theorem extend_deckV γ eb (c : UV X x₀) :
    extend eb (deckV γ c) = deckV γ (extend eb c) := by
  induction γ using Quotient.ind with
  | _ g =>
      induction c using UV.ind with
      | h p =>
          have hl : (extendP eb (deckP g p)).1 = (deckP g (extendP eb p)).1 := by
            by_cases h : endpt X x₀ p.1 = gSrcX X eb
            · have h' : endpt X x₀ (deckP g p).1 = gSrcX X eb := by
                simp_all [endpt_deckP]
              rw [extendP_pos h']
              show (g.1 ++ p.1) ++ [eb] = g.1 ++ (extendP eb p).1
              rw [extendP_pos h]
              simp
            · have h' : ¬ endpt X x₀ (deckP g p).1 = gSrcX X eb := by
                simp_all [endpt_deckP]
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
  ⟨(deckV γ E.1.1, E.1.2), by grind [endV_deckV]⟩

/-- The action of the fundamental group on the two-cells of the universal cover. -/
def deckF (γ : Pi1 X x₀) (F : UF X x₀) : UF X x₀ :=
  ⟨(deckV γ F.1.1, F.1.2), by grind [endV_deckV]⟩

theorem liftGerm_deckV (γ : Pi1 X x₀)
    h h' :
    liftGerm (deckV γ c) eb h' = (deckE γ (liftGerm c eb h).1, (liftGerm c eb h).2) := by
  cases' eb with e b
  cases b with
  | true => rfl
  | false =>
      refine Prod.ext ?_ rfl
      refine Subtype.ext (Prod.ext ?_ rfl)
      exact extend_deckV γ _ c

theorem uLiftPath_deckV γ : ∀ q (c : UV X x₀) w,
    IsPathX X q (endV c) w →
      uLiftPath q (deckV γ c) = (uLiftPath q c).map (fun Eb => (deckE γ Eb.1, Eb.2)) := by
  intro q
  induction q with
  | nil => simp
  | cons eb t ih =>
      intro c w hq
      have h := hq.1
      have h' : endV (deckV γ c) = gSrcX X eb := by simp_all
      rw [uLiftPath_cons h', uLiftPath_cons h, List.map_cons, liftGerm_deckV γ h h',
        extend_deckV γ eb c,
        ih _ w (by simp_all [endV_extend h])]

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
    have hbase := F.2
    have hatt : IsPathX X (X.att F.1.2) (endV F.1.1) (X.base F.1.2) := by
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
            have hvp : IsPathX X p.1 x₀ (endpt X x₀ r.1) := by grind
            have hrev := isPath_revPath hvp
            have hrp : IsPathX X (r.1 ++ revPath p.1) x₀ x₀ :=
              isPath_append_iff.mpr (by grind)
            refine ⟨Quotient.mk _ ⟨r.1 ++ revPath p.1, hrp⟩, ?_, ?_⟩
            · -- the translate of `p` by this loop is `r`
              refine Quotient.sound ?_
              show Htpy X x₀ (endpt X x₀ ((r.1 ++ revPath p.1) ++ p.1))
                ((r.1 ++ revPath p.1) ++ p.1) r.1
              have hend : endpt X x₀ ((r.1 ++ revPath p.1) ++ p.1) = endpt X x₀ r.1 := by
                grind [endpt_append, endpt_eq_of_isPath hrp]
              have hB :=
                htpy_revPath_append hvp
              have hA :=
                Htpy.append_congr r.2 (isPath_append_iff.mpr (by grind)) (Htpy.refl _) hB
              simp_all
            · -- uniqueness
              rintro γ hγ
              induction γ using Quotient.ind with
              | _ g =>
                  refine Quotient.sound ?_
                  have hg : Htpy X x₀ (endpt X x₀ (g.1 ++ p.1)) (g.1 ++ p.1) r.1 :=
                    Quotient.exact hγ
                  have hgp : IsPathX X (g.1 ++ p.1) x₀ (endpt X x₀ r.1) :=
                    isPath_append_iff.mpr (by grind)
                  have hend :=
                    endpt_eq_of_isPath hgp
                  rw [hend] at hg
                  -- append `revPath p` on the right
                  have h1 :=
                    Htpy.append_congr hgp hrev hg (Htpy.refl _)
                  have h2 :=
                    Htpy.append_congr g.2 (isPath_append_iff.mpr (by grind))
                      (Htpy.refl _) (htpy_append_revPath hvp)
                  have hassoc : (g.1 ++ p.1) ++ revPath p.1 = g.1 ++ (p.1 ++ revPath p.1) := by
                    simp
                  rw [hassoc] at h1
                  have h3 : Htpy X x₀ x₀ g.1 (g.1 ++ (p.1 ++ revPath p.1)) := by
                    simpa using h2.symm
                  exact h3.trans h1
