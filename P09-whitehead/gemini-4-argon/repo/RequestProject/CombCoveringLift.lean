module

public import RequestProject.CombPi1

@[expose] public section

namespace FiniteChains.Comb

universe u

theorem isPath_start_eq {V E : Type*} {src tgt : E → V} {l : List (E × Bool)} {a a' b b' : V}
    (h : IsPath src tgt l a b) (h' : IsPath src tgt l a' b') (hl : l ≠ []) : a = a' := by
  cases l with
  | nil => exact absurd rfl hl
  | cons _ _ => exact h.1.trans h'.1.symm

theorem isPath_endpoint_eq {V E : Type*} {src tgt : E → V} {l : List (E × Bool)} {a b b' : V}
    (h : IsPath src tgt l a b) (h' : IsPath src tgt l a b') : b = b' := by
  induction l generalizing a with
  | nil => exact h.symm.trans h'
  | cons _ _ ih => exact ih h.2 h'.2

variable {X Y : Complex2.{u}} {p : Hom X Y}

theorem exists_unique_liftGerm (hcov : IsCovering p) (a : X.V) {eb : Y.E × Bool}
    (h : germSrc Y.src Y.tgt eb = p.onV a) :
    ∃! x : X.E × Bool, germSrc X.src X.tgt x = a ∧ (p.onE x.1, x.2) = eb := by
  obtain ⟨hinj, hsurj⟩ := hcov.germ a
  obtain ⟨x, hx⟩ := hsurj ⟨eb, h⟩
  refine ⟨x.1, ⟨x.2, congrArg Subtype.val hx⟩, fun y ⟨hy1, hy2⟩ => ?_⟩
  have hmap : germMap p a ⟨y, hy1⟩ = germMap p a x :=
    Subtype.ext (hy2.trans (congrArg Subtype.val hx).symm)
  exact congrArg Subtype.val (hinj hmap)

theorem liftGerm_unique (hcov : IsCovering p) {a : X.V} {x y : X.E × Bool}
    (hx : germSrc X.src X.tgt x = a) (hy : germSrc X.src X.tgt y = a)
    (h : (p.onE x.1, x.2) = (p.onE y.1, y.2)) : x = y := by
  obtain ⟨z, -, hz⟩ := exists_unique_liftGerm hcov a
    (by rw [germSrc_onE p x, hx] : germSrc Y.src Y.tgt (p.onE x.1, x.2) = p.onV a)
  rw [hz x ⟨hx, rfl⟩, hz y ⟨hy, h.symm⟩]

theorem exists_unique_liftCell (hcov : IsCovering p) (f : Y.F) {v : X.V}
    (hv : Y.base f = p.onV v) : ∃! g : X.F, p.onF g = f ∧ X.base g = v := by
  obtain ⟨hinj, hsurj⟩ := hcov.cell
  obtain ⟨g, hg⟩ := hsurj ⟨(f, v), hv⟩
  obtain ⟨hg1, hg2⟩ := Prod.mk.inj (congrArg Subtype.val hg)
  exact ⟨g, ⟨hg1, hg2⟩, fun g' ⟨h1, h2⟩ =>
    hinj (Subtype.ext (Prod.ext (h1.trans hg1.symm) (h2.trans hg2.symm)))⟩

theorem exists_liftPathAt (hcov : IsCovering p) :
    ∀ (l : List (Y.E × Bool)) (a : X.V) (b : Y.V), IsPath Y.src Y.tgt l (p.onV a) b →
      ∃ (m : List (X.E × Bool)) (c : X.V), IsPath X.src X.tgt m a c ∧ mapPath p m = l
  | [], a, _, _ => ⟨[], a, rfl, rfl⟩
  | eb :: l, a, b, ⟨ha, hrest⟩ => by
      obtain ⟨x, ⟨hx1, hx2⟩, -⟩ := exists_unique_liftGerm hcov a ha.symm
      obtain ⟨m, c, hm, hmap⟩ := exists_liftPathAt hcov l (germTgt X.src X.tgt x) b
        (by rwa [← germTgt_onE p x, hx2])
      exact ⟨x :: m, c, ⟨hx1.symm, hm⟩, by show (p.onE x.1, x.2) :: mapPath p m = eb :: l; rw [hx2, hmap]⟩

theorem liftPath_unique (hcov : IsCovering p) :
    ∀ (m m' : List (X.E × Bool)) (a b b' : X.V), IsPath X.src X.tgt m a b →
      IsPath X.src X.tgt m' a b' → mapPath p m = mapPath p m' → m = m'
  | [], m', _, _, _, _, _, hmap => (List.map_eq_nil_iff.mp hmap.symm).symm
  | _ :: _, [], _, _, _, _, _, hmap => nomatch hmap
  | x :: m, y :: m', _, b, b', hm, hm', hmap => by
      obtain ⟨hxy, htail⟩ := List.cons.inj hmap
      have hx : x = y := liftGerm_unique hcov hm.1.symm hm'.1.symm hxy
      subst hx
      exact congrArg (List.cons x) (liftPath_unique hcov m m' _ b b' hm.2 hm'.2 htail)

theorem lift_cancels (hcov : IsCovering p) {a c : X.V} {m : List (X.E × Bool)}
    (hm : IsPath X.src X.tgt m a c) {l' : List (Y.E × Bool)}
    (hc : Cancels Y (mapPath p m) l') :
    ∃ m', IsPath X.src X.tgt m' a c ∧ mapPath p m' = l' ∧ Htpy X a c m m' := by
  rcases hc with ⟨P, Q, x, hl, rfl⟩ | ⟨P, Q, f, hl, rfl⟩
  · obtain ⟨M₁, M₂, rfl, rfl, hM₂⟩ := List.map_eq_append_iff.mp hl
    obtain ⟨u, M₃, rfl, hu, hM₃⟩ := List.map_eq_cons_iff.mp hM₂
    obtain ⟨w, Q', rfl, hw, rfl⟩ := List.map_eq_cons_iff.mp hM₃
    obtain ⟨v, hP, rfl, hw1, hQpath⟩ := isPath_append_iff.mp hm
    have hwrev : w = revGerm u :=
      liftGerm_unique hcov hw1.symm (by rw [germSrc_revGerm]) (by rw [hw, ← hu]; rfl)
    subst hwrev
    have hpath' : IsPath X.src X.tgt (M₁ ++ Q') a c :=
      isPath_append_iff.mpr ⟨_, hP, by rwa [germTgt_revGerm] at hQpath⟩
    exact ⟨M₁ ++ Q', hpath', by rw [mapPath_append]; rfl,
      .of_step ⟨hm, hpath', .inl ⟨M₁, Q', u, rfl, rfl⟩⟩⟩
  · obtain ⟨W, Q', rfl, hW, rfl⟩ := List.map_eq_append_iff.mp hl
    obtain ⟨M₁, A, rfl, rfl, hA⟩ := List.map_eq_append_iff.mp hW
    obtain ⟨w, hWpath, hQpath⟩ := isPath_append_iff.mp hm
    obtain ⟨v, hM₁path, hApath⟩ := isPath_append_iff.mp hWpath
    rcases eq_or_ne A [] with rfl | hA0
    · have hvw : v = w := hApath; subst hvw
      exact ⟨M₁ ++ Q', isPath_append_iff.mpr ⟨v, hM₁path, hQpath⟩,
        by rw [mapPath_append]; rfl, by simp; rfl⟩
    · have himg : IsPath Y.src Y.tgt (Y.att f) (p.onV v) (p.onV w) := hA ▸ isPath_mapPath p hApath
      have hbase : Y.base f = p.onV v :=
        isPath_start_eq (Y.att_isLoop f) himg (by rw [← hA]; simpa [mapPath] using hA0)
      obtain ⟨g, ⟨hg1, hg2⟩, -⟩ := exists_unique_liftCell hcov f hbase
      have hAg : A = X.att g :=
        liftPath_unique hcov A (X.att g) v w (X.base g) hApath (hg2 ▸ X.att_isLoop g)
          (by change List.map _ A = List.map _ (X.att g); rw [hA, ← hg1, p.att_onF])
      have hwv : w = v := isPath_endpoint_eq hApath (hAg.symm ▸ hg2 ▸ X.att_isLoop g)
      subst hwv hAg
      have hpath' := isPath_append_iff.mpr ⟨w, hM₁path, hQpath⟩
      exact ⟨M₁ ++ Q', hpath', by rw [mapPath_append]; rfl,
        .of_step ⟨hm, hpath', .inr ⟨M₁, Q', g, rfl, rfl⟩⟩⟩

theorem lift_uncancels (hcov : IsCovering p) {a c : X.V} {m : List (X.E × Bool)}
    (hm : IsPath X.src X.tgt m a c) {l : List (Y.E × Bool)}
    (hpath : IsPath Y.src Y.tgt l (p.onV a) (p.onV c))
    (hc : Cancels Y l (mapPath p m)) :
    ∃ m', IsPath X.src X.tgt m' a c ∧ mapPath p m' = l ∧ Htpy X a c m m' := by
  rcases hc with ⟨P, Q, x, rfl, hl'⟩ | ⟨P, Q, f, rfl, hl'⟩
  · obtain ⟨M₁, Q', rfl, rfl, rfl⟩ := List.map_eq_append_iff.mp hl'
    obtain ⟨v, hM₁path, hQpath⟩ := isPath_append_iff.mp hm
    obtain ⟨b₁, hPpath, hrest⟩ := isPath_append_iff.mp hpath
    have hxsrc : germSrc Y.src Y.tgt x = p.onV v :=
      isPath_endpoint_eq hPpath (isPath_mapPath p hM₁path) ▸ hrest.1.symm
    obtain ⟨u, ⟨hu1, hu2⟩, -⟩ := exists_unique_liftGerm hcov v hxsrc
    have hpath' : IsPath X.src X.tgt (M₁ ++ u :: revGerm (X := X) u :: Q') a c :=
      isPath_append_iff.mpr ⟨v, hM₁path, hu1.symm, by rw [germSrc_revGerm],
        by rwa [germTgt_revGerm, hu1]⟩
    refine ⟨M₁ ++ u :: revGerm (X := X) u :: Q', hpath', ?_,
      (Htpy.of_step ⟨hpath', hm, .inl ⟨M₁, Q', u, rfl, rfl⟩⟩).symm⟩
    rw [mapPath_append]
    refine congrArg (List.map _ M₁ ++ ·) ?_
    show (p.onE u.1, u.2) :: (p.onE (revGerm (X := X) u).1, (revGerm (X := X) u).2) :: mapPath p Q' = _
    rw [show (p.onE (revGerm (X := X) u).1, (revGerm (X := X) u).2) =
      revGerm (X := Y) (p.onE u.1, u.2) from rfl, hu2]; rfl
  · obtain ⟨M₁, Q', rfl, rfl, rfl⟩ := List.map_eq_append_iff.mp hl'
    obtain ⟨v, hM₁path, hQpath⟩ := isPath_append_iff.mp hm
    rcases eq_or_ne (Y.att f) [] with hA0 | hA0
    · exact ⟨M₁ ++ Q', hm, by rw [hA0, List.append_nil]; exact hl', .refl _⟩
    · obtain ⟨b₂, hPA, -⟩ := isPath_append_iff.mp hpath
      obtain ⟨b₁, hPpath, hattpath⟩ := isPath_append_iff.mp hPA
      have hbase : Y.base f = p.onV v :=
        isPath_endpoint_eq hPpath (isPath_mapPath p hM₁path) ▸ isPath_start_eq (Y.att_isLoop f) hattpath hA0
      obtain ⟨g, ⟨hg1, hg2⟩, -⟩ := exists_unique_liftCell hcov f hbase
      have hpath' : IsPath X.src X.tgt (M₁ ++ X.att g ++ Q') a c :=
        isPath_append_iff.mpr ⟨v, isPath_append_iff.mpr ⟨v, hM₁path, hg2 ▸ X.att_isLoop g⟩, hQpath⟩
      refine ⟨M₁ ++ X.att g ++ Q', hpath', ?_,
        (Htpy.of_step ⟨hpath', hm, .inr ⟨M₁, Q', g, rfl, rfl⟩⟩).symm⟩
      rw [mapPath_append, mapPath_append, show mapPath p (X.att g) = Y.att f by
        rw [← hg1, p.att_onF]; rfl]; rfl

theorem lift_htpy (hcov : IsCovering p) {a c : X.V} {m : List (X.E × Bool)}
    (hm : IsPath X.src X.tgt m a c) {l' : List (Y.E × Bool)}
    (h : Htpy Y (p.onV a) (p.onV c) (mapPath p m) l') :
    ∃ m', IsPath X.src X.tgt m' a c ∧ mapPath p m' = l' ∧ Htpy X a c m m' := by
  induction h with
  | refl => exact ⟨m, hm, rfl, .refl m⟩
  | tail _ hstep ih =>
      obtain ⟨m₁, hm₁, hmap₁, hhtpy₁⟩ := ih
      rcases hstep with hs | hs
      · obtain ⟨m₂, hm₂, hmap₂, hhtpy₂⟩ := lift_cancels hcov hm₁ (hmap₁.symm ▸ hs.2.2)
        exact ⟨m₂, hm₂, hmap₂, hhtpy₁.trans hhtpy₂⟩
      · obtain ⟨m₂, hm₂, hmap₂, hhtpy₂⟩ := lift_uncancels hcov hm₁ hs.1 (hmap₁.symm ▸ hs.2.2)
        exact ⟨m₂, hm₂, hmap₂, hhtpy₁.trans hhtpy₂⟩

theorem pi1Map_injective_of_isCovering (hcov : IsCovering p) (a : X.V) :
    Function.Injective (pi1Map p a) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨q⟩ hq
  obtain ⟨m', hm', hmap', hhtpy⟩ := lift_htpy hcov q.2 (Quotient.exact hq)
  rw [List.map_eq_nil_iff.mp hmap'] at hhtpy
  exact Quotient.sound hhtpy
