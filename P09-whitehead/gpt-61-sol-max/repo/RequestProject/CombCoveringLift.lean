import Mathlib.Tactic

import RequestProject.CombPi1

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

Everything is proved from the three axioms of `IsCovering`; no finiteness or connectivity
hypothesis is used.
-/

namespace FiniteChains.Comb



/-! ### Endpoints of edge paths -/

theorem isPath_start_eq {V E : Type*} {src tgt : E → V} {l : List (E × Bool)} {a a' b b' : V}
    (h : IsPath src tgt l a b) (h' : IsPath src tgt l a' b') (hl : l ≠ []) : a = a' := by
  cases l <;> simp_all

theorem isPath_endpoint_eq {V E : Type*} {src tgt : E → V} {l : List (E × Bool)} {a b b' : V}
    (h : IsPath src tgt l a b) (h' : IsPath src tgt l a b') : b = b' := by
  induction l generalizing a <;> aesop

variable {X Y : Complex2.{u}} {p : Hom X Y}

/-! ### Lifting germs -/

variable (hcov : IsCovering p)
include hcov in
/-- Unique lifting of an oriented edge issued from a vertex of the base. -/
theorem exists_unique_liftGerm  (a : X.V) {eb : Y.E × Bool}
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

include hcov in
/-- Two germs at the same vertex with the same image agree. -/
theorem liftGerm_unique  {a : X.V} {x y : X.E × Bool}
    (hx : germSrc X.src X.tgt x = a) (hy : germSrc X.src X.tgt y = a)
    (h : (p.onE x.1, x.2) = (p.onE y.1, y.2)) : x = y := congrArg Subtype.val ((hcov.germ a).1
    (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) (Subtype.ext h))

/-- The projection of the reverse of a germ is the reverse of its projection. -/
theorem onE_revGerm (p : Hom X Y) (x : X.E × Bool) :
    (p.onE (revGerm (X := X) x).1, (revGerm (X := X) x).2)
      = revGerm (X := Y) (p.onE x.1, x.2) := rfl

/-! ### Lifting two-cells -/

include hcov in
/-- Unique lifting of a two-cell with a prescribed lift of its basepoint. -/
theorem exists_unique_liftCell  (f : Y.F) {v : X.V}
    (hv : Y.base f = p.onV v) : ∃! g : X.F, p.onF g = f ∧ X.base g = v := by
  obtain ⟨hinj, hsurj⟩ := hcov.cell
  obtain ⟨g, hg⟩ := hsurj ⟨(f, v), hv⟩
  have hg'  := congrArg Subtype.val hg
  refine ⟨g, ⟨congrArg Prod.fst hg', congrArg Prod.snd hg'⟩, ?_⟩
  aesop

theorem mapPath_att (g : X.F) : mapPath p (X.att g) = Y.att (p.onF g) := (p.att_onF g).symm

/-! ### Lifting paths -/

include hcov in
/-- **Path lifting**: every edge path of the base issued from `p a` lifts to an edge path
issued from `a`. -/
theorem exists_liftPathAt  :
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

include hcov in
/-- **Uniqueness of lifts**: two lifts of the same edge path with the same initial vertex
coincide. -/
theorem liftPath_unique  :
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
            simp_all [mapPath]
          have hx  := liftGerm_unique hcov hm.1.symm hm'.1.symm hxy
          subst hx
          have htail : mapPath p m = mapPath p m' := by
            simp_all [mapPath]
          rw [ih m' (germTgt X.src X.tgt x) b b' hm.2 hm'.2 htail]

include hcov in
/-- The lift of the attaching path of a two-cell issued from a lift of its basepoint is the
attaching path of the lifted two-cell. -/
theorem eq_att_of_lift  {A : List (X.E × Bool)} {v w : X.V} {g : X.F}
    (hA : IsPath X.src X.tgt A v w) (hg : X.base g = v)
    (hmap : mapPath p A = Y.att (p.onF g)) : A = X.att g := by
  grind [FiniteChains.Comb.liftPath_unique, FiniteChains.Comb.Complex2.att_isLoop, FiniteChains.Comb.mapPath_att]

/-! ### Lifting elementary cancellations -/

variable {a c : X.V}
include hcov in
theorem lift_cancels   {m : List (X.E × Bool)}
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
      simp_all [FiniteChains.Comb.isPath_append_iff]
    have hwrev : w = revGerm u := by
      refine liftGerm_unique hcov hw1.symm (by rw [germSrc_revGerm]) ?_
      rw [hw, onE_revGerm, ← hu]
    have hQstart : germTgt X.src X.tgt w = v := by
      rw [hwrev, germTgt_revGerm, ← hu1]
    have hpath'  :=
      isPath_append_iff.mpr ⟨v, hP, by rw [← hQstart]; exact hQpath⟩
    refine ⟨M₁ ++ Q', hpath', ?_, ?_⟩
    · rw [hl', mapPath_append, hM₁', hQ'']
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
    · grind [FiniteChains.Comb.Htpy.refl]
    · have hattne : Y.att f ≠ [] := by
        rw [← hA']
        simpa [mapPath] using hA0
      have himg : IsPath Y.src Y.tgt (Y.att f) (p.onV v) (p.onV w) := by
        have h := isPath_mapPath p hApath
        rwa [hA'] at h
      have hbase  := isPath_start_eq (Y.att_isLoop f) himg hattne
      obtain ⟨g, ⟨hg1, hg2⟩, -⟩ := exists_unique_liftCell hcov f hbase
      have hAg : A = X.att g := by
        grind [eq_att_of_lift]
      have hwv : w = v := by
        grind [FiniteChains.Comb.Complex2.att_isLoop, FiniteChains.Comb.isPath_endpoint_eq]
      subst hwv
      have hpath'  :=
        isPath_append_iff.mpr ⟨w, hM₁path, hQpath⟩
      refine ⟨M₁ ++ Q', hpath', ?_, ?_⟩
      · rw [hl', mapPath_append, hM₁', hQ'']
      · refine Htpy.of_step ⟨hm, hpath', Or.inr ⟨M₁, Q', g, ?_, rfl⟩⟩
        rw [hAg]

include hcov in
theorem lift_uncancels   {m : List (X.E × Bool)}
    (hm : IsPath X.src X.tgt m a c) {l : List (Y.E × Bool)}
    (hpath : IsPath Y.src Y.tgt l (p.onV a) (p.onV c))
    (hc : Cancels Y l (mapPath p m)) :
    ∃ m', IsPath X.src X.tgt m' a c ∧ mapPath p m' = l ∧ Htpy X a c m m' := by
  obtain ⟨m', c', hm', he⟩ := exists_liftPathAt hcov l a _ hpath
  obtain ⟨m'', hm'', he'', H⟩ := lift_cancels hcov hm' (he.symm ▸ hc)
  have hh := liftPath_unique hcov m'' m a c' c hm'' hm he''
  subst m''
  have hh := isPath_endpoint_eq hm'' hm
  subst c'
  exact ⟨m', hm', he, H.symm⟩

/-! ### Homotopy lifting -/

include hcov in
/-- **Homotopy lifting**: a homotopy of the projection of a lifted path is covered by a
homotopy of the lift, with the same endpoints. -/
theorem lift_htpy   {m : List (X.E × Bool)}
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

include hcov in
/-- **A covering is injective on fundamental groups.** -/
theorem pi1Map_injective_of_isCovering  (a : X.V) :
    Function.Injective (pi1Map p a) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨q⟩ hq
  have hnull  := Quotient.exact hq
  obtain ⟨m', hm', hmap', hhtpy⟩ := lift_htpy hcov q.2 hnull
  have hnil  := List.map_eq_nil_iff.mp hmap'
  subst hnil
  exact Quotient.sound hhtpy

end FiniteChains.Comb

