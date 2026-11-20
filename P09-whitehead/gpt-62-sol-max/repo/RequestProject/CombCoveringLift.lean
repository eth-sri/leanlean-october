module

public import RequestProject.CombPi1

@[expose] public section

/-!
# Lifting of edge paths and homotopies along a combinatorial covering

`RequestProject/CellComplex.lean` defines combinatorial coverings `Comb.IsCovering p`: the
cellular map `p : X → Y` is onto on vertices, bijective on the edge germs at every vertex,
and every two-cell of the base lifts uniquely once a lift of its basepoint is chosen.  This
file develops the elementary covering theory that these axioms are designed for:

* `FiniteChains.Comb.exists_unique_liftGerm` — unique lifting of germs;
* `FiniteChains.Comb.exists_liftPathAt` and `FiniteChains.Comb.liftPath_unique` — existence
  and uniqueness of the lift of an edge path with a prescribed initial vertex;
* `FiniteChains.Comb.lift_cancels`, `FiniteChains.Comb.lift_uncancels` — an elementary
  cancellation downstairs is realised by an elementary cancellation upstairs;
* `FiniteChains.Comb.lift_htpy` — **homotopy lifting**: a homotopy of the projected path is
  covered by a homotopy of the lift, with the same endpoints;
* `FiniteChains.Comb.pi1Map_injective_of_isCovering` — the induced map on fundamental groups
  of a covering is injective.

Only the local bijections are needed for path and homotopy lifting.
In particular, lifting does not require surjectivity on vertices.
-/

namespace FiniteChains
namespace Comb

universe u

/-! ### Endpoints of edge paths -/

theorem isPath_start_eq {V E : Type*} {src tgt : E → V} {l : List (E × Bool)} {a a' b b' : V}
    (h : IsPath src tgt l a b) (h' : IsPath src tgt l a' b') (hl : l ≠ []) : a = a' := by
  cases l with
  | nil => aesop
  | cons eb l => aesop

theorem isPath_endpoint_eq {V E : Type*} {src tgt : E → V} {l : List (E × Bool)} {a b b' : V}
    (h : IsPath src tgt l a b) (h' : IsPath src tgt l a b') : b = b' := by
  induction l generalizing a <;> aesop

variable {X Y : Complex2.{u}} {p : Hom X Y}

/-- The local lifting axioms, without surjectivity on vertices. -/
structure HasUniqueLifts (p : Hom X Y) : Prop where
  germ : ∀ a, Function.Bijective (germMap p a)
  cell : Function.Bijective (cellMap p)

theorem IsCovering.uniqueLifts (h : IsCovering p) : HasUniqueLifts p := ⟨h.germ, h.cell⟩

/-! ### Lifting germs -/

/-- Unique lifting of an oriented edge issued from a vertex of the base. -/
theorem exists_unique_liftGerm (hcov : HasUniqueLifts p) (a : X.V) {eb : Y.E × Bool}
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
theorem liftGerm_unique (hcov : HasUniqueLifts p) {a : X.V} {x y : X.E × Bool}
    (hx : germSrc X.src X.tgt x = a) (hy : germSrc X.src X.tgt y = a)
    (h : (p.onE x.1, x.2) = (p.onE y.1, y.2)) : x = y :=
  congrArg Subtype.val ((hcov.germ a).1 (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) (Subtype.ext h))

/-- A lifted edge is determined by its projection and source. -/
theorem HasUniqueLifts.edge_eq (h : HasUniqueLifts p) {e f : X.E}
    (hs : X.src e = X.src f) (he : p.onE e = p.onE f) : e = f :=
  congrArg Prod.fst (liftGerm_unique h (x := (e, true)) (y := (f, true))
    rfl hs.symm (Prod.ext he rfl))

/-- A lifted face is determined by its projection and base vertex. -/
theorem HasUniqueLifts.face_eq (h : HasUniqueLifts p) {e f : X.F}
    (hs : X.base e = X.base f) (he : p.onF e = p.onF f) : e = f :=
  h.cell.1 (Subtype.ext (Prod.ext he hs))

/-- The projection of the reverse of a germ is the reverse of its projection. -/
theorem onE_revGerm (p : Hom X Y) (x : X.E × Bool) :
    (p.onE (revGerm (X := X) x).1, (revGerm (X := X) x).2)
      = revGerm (X := Y) (p.onE x.1, x.2) := rfl

/-! ### Lifting two-cells -/

/-- Unique lifting of a two-cell with a prescribed lift of its basepoint. -/
theorem exists_unique_liftCell (hcov : HasUniqueLifts p) (f : Y.F) {v : X.V}
    (hv : Y.base f = p.onV v) : ∃! g : X.F, p.onF g = f ∧ X.base g = v := by
  obtain ⟨hinj, hsurj⟩ := hcov.cell
  obtain ⟨g, hg⟩ := hsurj ⟨(f, v), hv⟩
  have hg' : (p.onF g, X.base g) = (f, v) := congrArg Subtype.val hg
  refine ⟨g, ⟨congrArg Prod.fst hg', congrArg Prod.snd hg'⟩, ?_⟩
  aesop

theorem mapPath_att (g : X.F) : mapPath p (X.att g) = Y.att (p.onF g) := (p.att_onF g).symm

/-! ### Lifting paths -/

/-- **Path lifting**: every edge path of the base issued from `p a` lifts to an edge path
issued from `a`. -/
theorem exists_liftPathAt (hcov : HasUniqueLifts p) :
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
theorem liftPath_unique (hcov : HasUniqueLifts p) :
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
      | nil => trivial
      | cons y m' =>
          have hxy : (p.onE x.1, x.2) = (p.onE y.1, y.2) := by
            have h := congrArg List.head? hmap
            simpa [mapPath] using h
          have hx  := liftGerm_unique hcov hm.1.symm hm'.1.symm hxy
          subst hx
          have htail : mapPath p m = mapPath p m' := by
            have h := congrArg List.tail hmap
            assumption
          rw [ih m' (germTgt X.src X.tgt x) b b' hm.2 hm'.2 htail]

/-- The lift of the attaching path of a two-cell issued from a lift of its basepoint is the
attaching path of the lifted two-cell. -/
theorem eq_att_of_lift (hcov : HasUniqueLifts p) {A : List (X.E × Bool)} {v w : X.V} {g : X.F}
    (hA : IsPath X.src X.tgt A v w) (hg : X.base g = v)
    (hmap : mapPath p A = Y.att (p.onF g)) : A = X.att g := by
  refine liftPath_unique hcov A (X.att g) v w (X.base g) hA (hg ▸ X.att_isLoop g) ?_
  rw [hmap, mapPath_att]

/-! ### Lifting elementary cancellations -/

private theorem lift_loopInsertion {a c : X.V} {m : List (X.E × Bool)}
    (hm : IsPath X.src X.tgt m a c) {r s u : List (Y.E × Bool)}
    (hmap : mapPath p m = r ++ s) {b : Y.V} (hu : IsPath Y.src Y.tgt u b b)
    (hp : IsPath Y.src Y.tgt (r ++ u ++ s) (p.onV a) (p.onV c))
    (lift : ∀ v, p.onV v = b → ∃ w, IsPath X.src X.tgt w v v ∧
      mapPath p w = u ∧ Htpy X v v w []) :
    ∃ m', IsPath X.src X.tgt m' a c ∧ mapPath p m' = r ++ u ++ s ∧ Htpy X a c m m' := by
  by_cases he : u = []
  · exact ⟨m, hm, by simpa [he] using hmap, Htpy.refl _⟩
  obtain ⟨r', s', rfl, hr, hs⟩ := List.map_eq_append_iff.mp hmap
  change mapPath p r' = r at hr
  change mapPath p s' = s at hs
  obtain ⟨v, hv, hvs⟩ := isPath_append_iff.mp hm
  obtain ⟨_, hru, _⟩ := isPath_append_iff.mp hp
  obtain ⟨z, hrz, hzu⟩ := isPath_append_iff.mp hru
  have h₁ := isPath_endpoint_eq hrz (hr ▸ isPath_mapPath p hv)
  have h₂ := isPath_start_eq hzu hu he
  obtain ⟨w, hw, hwmap, hW⟩ := lift v (h₁.symm.trans h₂)
  exact ⟨r' ++ w ++ s', (hv.append hw).append hvs,
    by simp [hr, hs, hwmap], by simpa using (hW.congr_append hv hvs).symm⟩

theorem lift_uncancels (hcov : HasUniqueLifts p) {a c : X.V} {m : List (X.E × Bool)}
    (hm : IsPath X.src X.tgt m a c) {l : List (Y.E × Bool)}
    (hpath : IsPath Y.src Y.tgt l (p.onV a) (p.onV c))
    (hc : Cancels Y l (mapPath p m)) :
    ∃ m', IsPath X.src X.tgt m' a c ∧ mapPath p m' = l ∧ Htpy X a c m m' := by
  rcases hc with ⟨r, s, x, rfl, hmap⟩ | ⟨r, s, f, rfl, hmap⟩
  · have hx := (isPath_single x).append (isPath_revPath (isPath_single x))
    have hp : IsPath Y.src Y.tgt (r ++ ([x, revGerm x] : List _) ++ s) (p.onV a) (p.onV c) := by
      simpa [List.append_assoc] using hpath
    have h := lift_loopInsertion hm hmap hx hp fun v hv => by
      obtain ⟨y, ⟨hy, hymap⟩, _⟩ := exists_unique_liftGerm hcov v hv.symm
      have hy' := hy ▸ isPath_single y
      refine ⟨[y, revGerm y], hy'.append (isPath_revPath hy'), ?_, htpy_append_revPath hy'⟩
      change (p.onE y.1, y.2) :: (p.onE (revGerm y).1, (revGerm y).2) :: [] = _
      rw [hymap, onE_revGerm, hymap]
      rfl
    simpa [List.append_assoc] using h
  · refine lift_loopInsertion hm hmap (Y.att_isLoop f) hpath ?_
    intro v hv
    obtain ⟨g, ⟨hg, hvg⟩, _⟩ := exists_unique_liftCell hcov f hv.symm
    have hl := hvg ▸ X.att_isLoop g
    exact ⟨X.att g, hl, by rw [mapPath_att, hg],
      Htpy.of_step ⟨hl, rfl, Or.inr ⟨[], [], g, by simp, rfl⟩⟩⟩

/-- A deletion is lifted by lifting the shorter path and using uniqueness
on the insertion which recovers the original path. -/
theorem lift_cancels (hcov : HasUniqueLifts p) {a c : X.V} {m : List (X.E × Bool)}
    (hm : IsPath X.src X.tgt m a c) {l' : List (Y.E × Bool)}
    (hl' : IsPath Y.src Y.tgt l' (p.onV a) (p.onV c)) (hc : Cancels Y (mapPath p m) l') :
    ∃ m', IsPath X.src X.tgt m' a c ∧ mapPath p m' = l' ∧ Htpy X a c m m' := by
  obtain ⟨m', c', hm', hmap⟩ := exists_liftPathAt hcov l' a (p.onV c) hl'
  have hv := isPath_endpoint_eq (isPath_mapPath p hm') (hmap.symm ▸ hl')
  obtain ⟨L, hL, hLmap, hLhtpy⟩ := lift_uncancels hcov hm' (hv.symm ▸ isPath_mapPath p hm) (hmap.symm ▸ hc)
  have he := liftPath_unique hcov L m a c' c hL hm hLmap
  subst L
  have hv' := isPath_endpoint_eq hm hL
  subst c'
  exact ⟨m', hm', hmap, hLhtpy.symm⟩

/-! ### Homotopy lifting -/

/-- **Homotopy lifting**: a homotopy of the projection of a lifted path is covered by a
homotopy of the lift, with the same endpoints. -/
theorem lift_htpy (hcov : HasUniqueLifts p) {a c : X.V} {m : List (X.E × Bool)}
    (hm : IsPath X.src X.tgt m a c) {l' : List (Y.E × Bool)}
    (h : Htpy Y (p.onV a) (p.onV c) (mapPath p m) l') :
    ∃ m', IsPath X.src X.tgt m' a c ∧ mapPath p m' = l' ∧ Htpy X a c m m' := by
  induction h with
  | refl => tauto
  | tail _ hstep ih =>
      obtain ⟨m₁, hm₁, hmap₁, hhtpy₁⟩ := ih
      rcases hstep with hs | hs
      · obtain ⟨m₂, hm₂, hmap₂, hhtpy₂⟩ :=
          lift_cancels hcov hm₁ hs.2.1 (hmap₁.symm ▸ hs.2.2)
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
  obtain ⟨m', hm', hmap', hhtpy⟩ := lift_htpy hcov.uniqueLifts q.2 hnull
  have hnil  := List.map_eq_nil_iff.mp hmap'
  subst hnil
  exact Quotient.sound hhtpy

end Comb
end FiniteChains
