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

universe u

/-! ### Endpoints of edge paths -/

theorem isPath_start_eq {V E} {src tgt} {l : List (E × Bool)} {a a' b b' : V}
    (h : IsPath src tgt l a b) (h' : IsPath src tgt l a' b') (hl : l ≠ []) : a = a' := by
  cases l <;> simp_all

theorem isPath_endpoint_eq {V E} {src tgt} {l : List (E × Bool)} {a b b' : V}
    (h : IsPath src tgt l a b) (h' : IsPath src tgt l a b') : b = b' := by
  induction l generalizing a <;> aesop

variable {X Y : Complex2.{u}} {p : Hom X Y}

/-! ### Lifting germs -/

/-- Unique lifting of an oriented edge issued from a vertex of the base. -/
theorem exists_unique_liftGerm (hcov : IsCovering p) a {eb}
    (h : gSrcX Y eb = p.onV a) :
    ∃! x, gSrcX X x = a ∧ (p.onE x.1, x.2) = eb := by
  cases' hcov.germ a with hinj hsurj
  cases' hsurj ⟨eb, h⟩ with x hx
  refine ⟨x.1, ⟨x.2, congrArg Subtype.val hx⟩, ?_⟩
  rintro y ⟨hy1, hy2⟩
  have hmap : germMap p a ⟨y, hy1⟩ = germMap p a x := by
    aesop
  grind

/-- Two germs at the same vertex with the same image agree. -/
theorem liftGerm_unique (hcov : IsCovering p) {a} {x y}
    (hx : gSrcX X x = a) (hy : gSrcX X y = a)
    (h : (p.onE x.1, x.2) = (p.onE y.1, y.2)) : x = y := by
  have hs : gSrcX Y (p.onE x.1, x.2) = p.onV a := by
    rw [germSrc_onE p x, hx]
  obtain ⟨z, -, hz⟩ := exists_unique_liftGerm hcov a hs
  grind


/-! ### Lifting two-cells -/

/-- Unique lifting of a two-cell with a prescribed lift of its basepoint. -/
theorem exists_unique_liftCell (hcov : IsCovering p) f {v}
    (hv : Y.base f = p.onV v) : ∃! g, p.onF g = f ∧ X.base g = v := by
  cases' hcov.cell with hinj hsurj
  cases' hsurj ⟨(f, v), hv⟩ with g hg
  have hg' : (p.onF g, X.base g) = (f, v) := congrArg Subtype.val hg
  refine ⟨g, by simp_all, ?_⟩
  aesop

theorem mapPath_att g : mapPath p (X.att g) = Y.att (p.onF g) := (p.att_onF g).symm

/-! ### Lifting paths -/

/-- **Path lifting**: every edge path of the base issued from `p a` lifts to an edge path
issued from `a`. -/
theorem exists_liftPathAt (hcov : IsCovering p) :
    ∀ l a b, IsPathX Y l (p.onV a) b →
      ∃ (m : List (X.E × Bool)) (c : X.V), IsPathX X m a c ∧ mapPath p m = l := by
  intro l
  induction l with
  | nil => intro a b _; exact ⟨[], a, rfl, rfl⟩
  | cons eb l ih =>
      intro a b hl
      cases' hl with ha hrest
      obtain ⟨x, ⟨hx1, hx2⟩, -⟩ := exists_unique_liftGerm hcov a ha.symm
      have hstep : p.onV (gTgtX X x) = gTgtX Y eb := by
        rw [← hx2, germTgt_onE p x]
      obtain ⟨m, c, hm, hmap⟩ := ih (gTgtX X x) b (by simp_all)
      refine ⟨x :: m, c, ⟨hx1.symm, hm⟩, ?_⟩
      aesop

/-- **Uniqueness of lifts**: two lifts of the same edge path with the same initial vertex
coincide. -/
theorem liftPath_unique (hcov : IsCovering p) :
    ∀ m m' a b b', IsPathX X m a b →
      IsPathX X m' a b' → mapPath p m = mapPath p m' → m = m' := by
  intro m
  induction m with
  | nil =>
      intro m' _ _ _ _ _ hmap
      exact (List.map_eq_nil_iff.mp hmap.symm).symm
  | cons x m ih =>
      intro m' a b b' hm hm' hmap
      cases m' with
      | nil => tauto
      | cons y m' =>
          have hxy : (p.onE x.1, x.2) = (p.onE y.1, y.2) := by
            simp_all [mapPath]
          have hx := liftGerm_unique hcov hm.1.symm hm'.1.symm hxy
          subst hx
          have htail : mapPath p m = mapPath p m' := by
            have h := congrArg List.tail hmap
            tauto
          aesop

/-- The lift of the attaching path of a two-cell issued from a lift of its basepoint is the
attaching path of the lifted two-cell. -/
theorem eq_att_of_lift (hcov : IsCovering p) {A} {v w} {g}
    (hA : IsPathX X A v w) (hg : X.base g = v)
    (hmap : mapPath p A = Y.att (p.onF g)) : A = X.att g := by
  refine liftPath_unique hcov A (X.att g) v w (X.base g) hA (hg ▸ X.att_isLoop g) ?_
  rw [hmap, mapPath_att]

/-! ### Lifting elementary cancellations -/

theorem lift_cancels (hcov : IsCovering p) {a c} {m}
    (hm : IsPathX X m a c) {l'}
    (hc : Cancels Y (mapPath p m) l') :
    ∃ m', IsPathX X m' a c ∧ mapPath p m' = l' ∧ Htpy X a c m m' := by
  rcases hc with ⟨P, Q, x, hl, hl'⟩ | ⟨P, Q, f, hl, hl'⟩
  · -- deleting a backtrack
    obtain ⟨M₁, M₂, hsplit, hM₁, hM₂⟩ := List.map_eq_append_iff.mp hl
    obtain ⟨u, M₃, hM₂eq, hu, hM₃⟩ := List.map_eq_cons_iff.mp hM₂
    obtain ⟨w, Q', hM₃eq, hw, hQ'⟩ := List.map_eq_cons_iff.mp hM₃
    subst hsplit
    have hM₁' : mapPath p M₁ = P := hM₁
    have hQ'' : mapPath p Q' = Q := hQ'
    obtain ⟨v, hP, hu1, hw1, hQpath⟩ :
        ∃ v, IsPathX X M₁ a v ∧ v = gSrcX X u ∧
          gTgtX X u = gSrcX X w ∧
          IsPathX X Q' (gTgtX X w) c := by
      obtain ⟨v, hP, hrest⟩ := isPath_append_iff.mp hm
      simp_all
    have hwrev : w = revGerm u := by
      refine liftGerm_unique hcov hw1.symm (by simp) ?_
      aesop
    have hpath' :=
      isPath_append_iff.mpr (by aesop)
    refine ⟨M₁ ++ Q', hpath', ?_, ?_⟩
    · simp_all
    · refine Htpy.of_step ⟨hm, hpath', Or.inl ⟨M₁, Q', u, ?_, rfl⟩⟩
      simp_all
  · -- deleting the attaching path of a two-cell
    obtain ⟨W, Q', hsplit, hW, hQ'⟩ := List.map_eq_append_iff.mp hl
    obtain ⟨M₁, A, hWeq, hM₁, hA⟩ := List.map_eq_append_iff.mp hW
    subst hWeq; subst hsplit
    have hM₁' : mapPath p M₁ = P := hM₁
    have hQ'' : mapPath p Q' = Q := hQ'
    obtain ⟨w, hWpath, hQpath⟩ := isPath_append_iff.mp hm
    obtain ⟨v, hM₁path, hApath⟩ := isPath_append_iff.mp hWpath
    rcases eq_or_ne A [] with hA0 | hA0
    · subst hA0
      have hvw := hApath
      subst hvw
      refine ⟨M₁ ++ Q', by simp_all, ?_, ?_⟩
      · simp_all
      · have hmeq : M₁ ++ [] ++ Q' = M₁ ++ Q' := by simp
        rw [hmeq]
        exact Htpy.refl _
    · have hattne : Y.att f ≠ [] := by
        aesop
      have himg : IsPathX Y (Y.att f) (p.onV v) (p.onV w) := by
        have h := isPath_mapPath p hApath
        simp_all
      have hbase := isPath_start_eq (Y.att_isLoop f) himg hattne
      obtain ⟨g, ⟨hg1, hg2⟩, -⟩ := exists_unique_liftCell hcov f hbase
      have hAg : A = X.att g := by
        refine eq_att_of_lift hcov hApath hg2 ?_
        simp_all
      have hwv : w = v := by
        have hloop : IsPathX X A v v := by
          rw [hAg]
          exact hg2 ▸ X.att_isLoop g
        exact (isPath_endpoint_eq hApath hloop)
      subst hwv
      have hpath' : IsPathX X (M₁ ++ Q') a c :=
        isPath_append_iff.mpr (by grind)
      refine ⟨M₁ ++ Q', hpath', ?_, ?_⟩
      · simp_all
      · refine Htpy.of_step ⟨hm, hpath', Or.inr ⟨M₁, Q', g, ?_, rfl⟩⟩
        simp_all

theorem lift_uncancels (hcov : IsCovering p) {a c} {m}
    (hm : IsPathX X m a c) {l}
    (hpath : IsPathX Y l (p.onV a) (p.onV c))
    (hc : Cancels Y l (mapPath p m)) :
    ∃ m', IsPathX X m' a c ∧ mapPath p m' = l ∧ Htpy X a c m m' := by
  rcases hc with ⟨P, Q, x, hl, hl'⟩ | ⟨P, Q, f, hl, hl'⟩
  · -- inserting a backtrack
    obtain ⟨M₁, Q', hsplit, hM₁, hQ'⟩ := List.map_eq_append_iff.mp hl'
    subst hsplit
    have hQ'' : mapPath p Q' = Q := hQ'
    obtain ⟨v, hM₁path, hQpath⟩ := isPath_append_iff.mp hm
    have hPimg : IsPathX Y P (p.onV a) (p.onV v) := by
      have h := isPath_mapPath p hM₁path
      simp_all
    have hxsrc : gSrcX Y x = p.onV v := by
      subst hl
      obtain ⟨b₁, hPpath, hrest⟩ := isPath_append_iff.mp hpath
      have hb₁ : b₁ = p.onV v := isPath_endpoint_eq hPpath hPimg
      simp_all
    obtain ⟨u, ⟨hu1, hu2⟩, -⟩ := exists_unique_liftGerm hcov v hxsrc
    have hpath' : IsPathX X (M₁ ++ u :: revGerm (X := X) u :: Q') a c := by
      refine isPath_append_iff.mpr ⟨v, hM₁path, ?_, ?_, ?_⟩ <;> simp_all
    refine ⟨M₁ ++ u :: revGerm (X := X) u :: Q', hpath', ?_, ?_⟩
    · aesop
    · refine (Htpy.of_step ⟨hpath', hm, Or.inl (by grind)⟩).symm
  · -- inserting the attaching path of a two-cell
    obtain ⟨M₁, Q', hsplit, hM₁, hQ'⟩ := List.map_eq_append_iff.mp hl'
    subst hsplit
    have hM₁' : mapPath p M₁ = P := hM₁
    have hQ'' : mapPath p Q' = Q := hQ'
    obtain ⟨v, hM₁path, hQpath⟩ := isPath_append_iff.mp hm
    have hPimg : IsPathX Y P (p.onV a) (p.onV v) := by
      have h := isPath_mapPath p hM₁path
      simp_all
    rcases eq_or_ne (Y.att f) [] with hA0 | hA0
    · refine ⟨M₁ ++ Q', hm, ?_, Htpy.refl _⟩
      simp_all
    · have hbase : Y.base f = p.onV v := by
        subst hl
        obtain ⟨b₂, hPA, -⟩ := isPath_append_iff.mp hpath
        obtain ⟨b₁, hPpath, hattpath⟩ := isPath_append_iff.mp hPA
        have hb₁ : b₁ = p.onV v := isPath_endpoint_eq hPpath hPimg
        rw [← hb₁]
        exact isPath_start_eq (Y.att_isLoop f) hattpath hA0
      obtain ⟨g, ⟨hg1, hg2⟩, -⟩ := exists_unique_liftCell hcov f hbase
      have hgloop := hg2 ▸ X.att_isLoop g
      have hpath' : IsPathX X (M₁ ++ X.att g ++ Q') a c :=
        isPath_append_iff.mpr ⟨v, isPath_append_iff.mpr (by grind), hQpath⟩
      refine ⟨M₁ ++ X.att g ++ Q', hpath', ?_, ?_⟩
      · rw [hl, mapPath_append, mapPath_append, hM₁', hQ'', mapPath_att, hg1]
      · exact (Htpy.of_step ⟨hpath', hm, by tauto⟩).symm

/-! ### Homotopy lifting -/

/-- **Homotopy lifting**: a homotopy of the projection of a lifted path is covered by a
homotopy of the lift, with the same endpoints. -/
theorem lift_htpy (hcov : IsCovering p) {a c} {m}
    (hm : IsPathX X m a c) {l'}
    (h : Htpy Y (p.onV a) (p.onV c) (mapPath p m) l') :
    ∃ m', IsPathX X m' a c ∧ mapPath p m' = l' ∧ Htpy X a c m m' := by
  induction h with
  | refl => tauto
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
theorem pi1Map_injective_of_isCovering (hcov : IsCovering p) a :
    Function.Injective (pi1Map p a) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨q⟩ hq
  have hnull := Quotient.exact hq
  obtain ⟨m', hm', hmap', hhtpy⟩ := lift_htpy hcov q.2 hnull
  have hnil := List.map_eq_nil_iff.mp hmap'
  subst hnil
  exact Quotient.sound hhtpy
