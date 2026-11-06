import RequestProject.MirrorSimplyConnected


/-!
# Gluing two subposets along a connected intersection

This file proves the `π₁` half of the gluing lemma of the chamber argument, in the form in which
the chamber induction uses it: everything is stated *inside the ambient order complex*, so that
the conclusion of one step is literally the hypothesis of the next.

* `FiniteChains.Comb.orderCxMap` — a monotone map of preorders induces a cellular map of the
  two-skeletons of the order complexes.
* `FiniteChains.Comb.PathIn A l` — every edge of the edge path `l` has both endpoints in the
  subposet `A`.
* `FiniteChains.Comb.htpy_nil_of_pathIn` — a loop of the ambient order complex all of whose edges
  lie in a *simply connected* subposet is null-homotopic in the ambient complex (the loop is
  lifted to the subposet and its null-homotopy is pushed forward).
* `FiniteChains.Comb.htpy_nil_of_pathIn_union` — **the gluing lemma**: if `U = A ∪ B`, no
  comparability inside `U` is mixed (every comparable pair lies in `A` or lies in `B`), loops
  in `A` and loops in `B` are null-homotopic in the ambient complex, `A` and `B` are connected
  and their intersection `J` is nonempty and connected, then every loop in `U` is
  null-homotopic in the ambient complex.
* `FiniteChains.Comb.isConnectedIn_union` — under the same hypotheses `U` is connected.

The proof of the gluing lemma is the usual van Kampen argument written out combinatorially: a
loop is cut at its returns to `J` into segments lying on one side, each segment is closed up by
the chosen `J`-paths to the base vertex, and each resulting loop is killed on its own side.
-/

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb


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

@[simp] theorem orderCxMap_onV (f : P → Q) hf (p : P) :
    (orderCxMap f hf).onV p = f p := rfl

end Map

/-! ### Paths inside a subposet -/

section PathIn

variable {P : Type u} [Preorder P]

/-- Every edge of the path `l` has both endpoints in `A`. -/
def PathIn (A : P → Prop) (l : List ((orderCx P).E × Bool)) :=
  ∀ e ∈ l, A e.1.1.1 ∧ A e.1.1.2

theorem pathIn_nil A : PathIn A ([] : List ((orderCx P).E × Bool)) := by
  tauto

theorem pathIn_cons
    {l : List ((orderCx P).E × Bool)} (he : A e.1.1.1 ∧ A e.1.1.2) (hl : PathIn A l) :
    PathIn A (e :: l) := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | h
  · exact he
  · exact hl x h

theorem pathIn_of_cons
    {l : List ((orderCx P).E × Bool)} (h : PathIn A (e :: l)) :
    (A e.1.1.1 ∧ A e.1.1.2) ∧ PathIn A l :=
  ⟨h e (by simp), fun x hx => h x (by simp_all)⟩

theorem pathIn_append {l l' : List ((orderCx P).E × Bool)}
    (h : PathIn A l) (h' : PathIn A l') : PathIn A (l ++ l') := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact h x hx
  · exact h' x hx

theorem pathIn_of_append_left {l l' : List ((orderCx P).E × Bool)}
    (h : PathIn A (l ++ l')) : PathIn A l := fun x hx => h x (by simp_all)

theorem pathIn_of_append_right {l l' : List ((orderCx P).E × Bool)}
    (h : PathIn A (l ++ l')) : PathIn A l' := fun x hx => h x (by simp_all)

theorem pathIn_revPath {l : List ((orderCx P).E × Bool)} (h : PathIn A l) :
    PathIn A (revPath l) := by
  intro x hx
  simp only [revPath, List.mem_reverse, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact h y hy

theorem pathIn_mono (hAB : ∀ p, A p → B p)
    {l : List ((orderCx P).E × Bool)} (h : PathIn A l) : PathIn B l :=
  fun x hx => ⟨hAB _ (h x hx).1, hAB _ (h x hx).2⟩

end PathIn

/-! ### Lifting a path to a subposet -/

section Lift

variable {P : Type u} [Preorder P] {A : P → Prop}

/-- The inclusion of a subposet. -/
theorem monotone_subtypeVal : Monotone (fun p : {p : P // A p} => (p : P)) :=
  by tauto

/-- The cellular map induced by the inclusion of a subposet. -/
def subposetHom (A : P → Prop) :=
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
    (hu : A u) (hv : A v), IsPathX (orderCx P) l u v →
    IsPathX (orderCx {p : P // A p}) (liftPathIn l h)
      ⟨u, hu⟩ ⟨v, hv⟩
  | [], _, u, v, hu, hv, hp => by
      aesop
  | e :: t, h, u, v, hu, hv, hp => by
      cases' hp with hstart hrest
      cases' e with e tag
      cases tag with
      | false =>
          refine ⟨Subtype.ext hstart, ?_⟩
          exact isPath_liftPathIn t (pathIn_of_cons h).2 ((pathIn_of_cons h).1).1 hv hrest
      | true =>
          refine ⟨Subtype.ext hstart, ?_⟩
          exact isPath_liftPathIn t (pathIn_of_cons h).2 ((pathIn_of_cons h).1).2 hv hrest

/-- **A loop inside a simply connected subposet is null-homotopic in the ambient complex.** -/
theorem htpy_nil_of_pathIn (hA : SimplyConnected (orderCx {p : P // A p}))
    {v} (hv : A v) {l}
    (hp : IsPathX (orderCx P) l v v) (hl : PathIn A l) :
    Htpy (orderCx P) v v l [] := by
  have hlift := isPath_liftPathIn l hl hv hv hp
  have hnull := hA _ _ hlift
  have := mapPath_htpy (subposetHom A) hnull
  rw [mapPath_liftPathIn l hl] at this
  tauto

end Lift

/-! ### The gluing lemma -/

section VanKampen

variable {P : Type u} [Preorder P]

/-- Every loop of the ambient order complex all of whose edges lie in `A` is null-homotopic in
the ambient complex. -/
def NullIn (A : P → Prop) :=
  ∀ v l, A v →
    IsPathX (orderCx P) l v v → PathIn A l → Htpy _ v v l []

/-- Any two elements of `A` are joined by a path all of whose edges lie in `A`. -/
def ConnectedIn (A : P → Prop) :=
  ∀ u v, A u → A v → ∃ l, IsPathX (orderCx P) l u v ∧ PathIn A l

/-- A simply connected subposet gives `NullIn`. -/
theorem nullIn_of_simplyConnected
    (hA : SimplyConnected (orderCx {p : P // A p})) : NullIn A :=
  fun _ _ hv hp hl => htpy_nil_of_pathIn hA hv hp hl

/-- The image of a path of the subposet complex lies in the subposet. -/
theorem pathIn_mapPath A (l : List ((orderCx {p : P // A p}).E × Bool)) :
    PathIn A (mapPath (subposetHom A) l) := by
  intro e he
  simp only [mapPath, List.mem_map] at he
  obtain ⟨x, _, rfl⟩ := he
  exact ⟨x.1.1.1.2, x.1.1.2.2⟩

/-- A connected subposet gives `ConnectedIn`. -/
theorem connectedIn_of_isConnected (h : IsConnected (orderCx {p : P // A p})) :
    ConnectedIn A := by
  intro u v hu hv
  cases' h ⟨u, hu⟩ ⟨v, hv⟩ with l hl
  exact ⟨mapPath (subposetHom A) l, isPath_mapPath _ hl, pathIn_mapPath A l⟩

theorem pathIn_congr (h : ∀ p, A p ↔ A' p)
    {l : List ((orderCx P).E × Bool)} (hl : PathIn A l) : PathIn A' l :=
  pathIn_mono (by simp_all) hl

theorem nullIn_congr {A A' : P → Prop} (h : ∀ p, A p ↔ A' p) (hA : NullIn A) : NullIn A' :=
  fun v l hv hp hl => hA v l (by simp_all) hp (pathIn_congr (by simp_all) hl)

theorem connectedIn_congr {A A' : P → Prop} (h : ∀ p, A p ↔ A' p) (hA : ConnectedIn A) :
    ConnectedIn A' := by
  intro u v hu hv
  obtain ⟨l, hl, hlin⟩ := hA u v (by simp_all) (by simp_all)
  exact ⟨l, hl, pathIn_congr h hlin⟩

/-- **Cutting a path at its first return to the intersection.**  A path that starts on the `S`
side runs inside `S` until it first meets `S ∩ S'`. -/
theorem split_side {S S' U : P → Prop}
    (hmix : ∀ a b, a ≤ b → U a → U b → (S a ∧ S b) ∨ (S' a ∧ S' b)) :
    ∀ t (w v : P),
      IsPathX (orderCx P) t w v → PathIn U t → (S v ∧ S' v) → S w →
      ∃ (t₁ t₂ : List ((orderCx P).E × Bool)) (z : P), t = t₁ ++ t₂ ∧
        IsPathX (orderCx P) t₁ w z ∧
        IsPathX (orderCx P) t₂ z v ∧ (S z ∧ S' z) ∧ PathIn S t₁ := by
  intro t
  induction t with
  | nil =>
      intro w v hp _ hv _
      have hwv := hp
      subst hwv
      exact ⟨[], [], w, rfl, rfl, rfl, hv, pathIn_nil S⟩
  | cons e t ih =>
      intro w v hp hUl hv hw
      by_cases hJ : S w ∧ S' w
      · exact ⟨[], e :: t, w, rfl, rfl, hp, hJ, pathIn_nil S⟩
      · cases' hp with hstart hrest
        cases' pathIn_of_cons hUl with hUe hUt
        have hS' : ¬ S' w := by simp_all
        have hSe : S e.1.1.1 ∧ S e.1.1.2 := by
          rcases hmix e.1.1.1 e.1.1.2 e.1.2 hUe.1 hUe.2 with h | h
          · exact h
          · exfalso
            cases' e with ee tag
            cases tag with
            | false =>
                exact hS' (by rw [hstart]; exact h.2)
            | true =>
                exact hS' (by rw [hstart]; exact h.1)
        have hSw : S (gTgtX (orderCx P) e) := by
          cases' e with ee tag
          cases tag <;> aesop
        obtain ⟨t₁, t₂, z, hteq, hp1, hp2, hz, hin1⟩ :=
          ih _ v hrest hUt hv hSw
        exact ⟨e :: t₁, t₂, z, by simp_all, ⟨hstart, hp1⟩, hp2, hz, pathIn_cons hSe hin1⟩

/-- **The gluing lemma at the level of `π₁`.**  Let `U` be covered by two subposets `A` and `B`
such that no comparability inside `U` is mixed, let loops inside `A` and inside `B` be
null-homotopic in the ambient order complex, let `A`, `B` and their intersection `J = A ∩ B` be
connected and let `J` be nonempty.  Then every loop inside `U` is null-homotopic in the ambient
order complex.  This is the van Kampen step of the chamber induction, written so that its
conclusion is again a hypothesis of the same shape. -/
theorem htpy_nil_of_pathIn_union {A B U}
    (hU : ∀ p, U p ↔ (A p ∨ B p))
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    (hA : NullIn A) (hB : NullIn B)
    (hAconn : ConnectedIn A) (hBconn : ConnectedIn B)
    (hJconn : ConnectedIn (fun p => A p ∧ B p))
    {j} (hj : A j ∧ B j) :
    NullIn U := by
  classical
  have hex : ∀ u, ∃ g : List ((orderCx P).E × Bool),
      ((A u ∧ B u) → IsPathX (orderCx P) g j u ∧
        PathIn (fun p => A p ∧ B p) g) ∧ (u = j → g = []) := by
    intro u
    by_cases hu : u = j
    · subst hu
      exact ⟨[], fun _ => ⟨rfl, pathIn_nil _⟩, fun _ => rfl⟩
    · by_cases h : A u ∧ B u
      · aesop
      simp_all
  choose γ hγ hγj using hex
  have key : ∀ n l (u v : P), l.length ≤ n →
      IsPathX (orderCx P) l u v → PathIn U l →
      (A u ∧ B u) → (A v ∧ B v) →
      Htpy _ j j (γ u ++ l ++ revPath (γ v)) [] := by
    intro n
    induction n with
    | zero =>
        intro l u v hlen hp _ hu _
        have hl : l = [] := by simp_all
        subst hl
        have huv := hp
        subst huv
        simpa using htpy_append_revPath (hγ u hu).1
    | succ n ih =>
        intro l u v hlen hp hUl hu hv
        cases l with
        | nil =>
            grind
        | cons e t =>
            obtain ⟨hstart, hrest⟩ := hp
            obtain ⟨hUe, hUt⟩ := pathIn_of_cons hUl
            have side : ∀ S S' : P → Prop,
                (∀ a b, a ≤ b → U a → U b → (S a ∧ S b) ∨ (S' a ∧ S' b)) →
                NullIn S →
                (∀ p, S p ∧ S' p → A p ∧ B p) →
                (∀ p, A p ∧ B p → S p ∧ S' p) →
                (S e.1.1.1 ∧ S e.1.1.2) →
                Htpy _ j j (γ u ++ (e :: t) ++ revPath (γ v)) [] := by
              intro S S' hmixS hNullS hJS hJS' hSe
              have hSw : S (gTgtX (orderCx P) e) := by
                cases' e with ee tag
                cases tag with
                | false => exact hSe.1
                | true => exact hSe.2
              obtain ⟨t₁, t₂, z, hteq, hp1, hp2, hz, hin1⟩ :=
                split_side hmixS t _ v hrest hUt (hJS' v hv) hSw
              have hJz : A z ∧ B z := hJS z hz
              have hgu := (hγ u hu).1
              have hgv := (hγ v hv).1
              have hgz := (hγ z hJz).1
              have hSj : S j ∧ S' j := hJS' j hj
              have hpath1 : IsPathX (orderCx P) (γ u ++ (e :: t₁)) j z :=
                isPath_append_iff.mpr ⟨u, hgu, ⟨hstart, hp1⟩⟩
              have hpathY : IsPathX (orderCx P)
                  (t₂ ++ revPath (γ v)) z j :=
                isPath_append_iff.mpr ⟨v, hp2, isPath_revPath hgv⟩
              have hX : IsPathX (orderCx P)
                  ((γ u ++ (e :: t₁)) ++ revPath (γ z)) j j :=
                isPath_append_iff.mpr ⟨z, hpath1, isPath_revPath hgz⟩
              have hY : IsPathX (orderCx P)
                  (γ z ++ (t₂ ++ revPath (γ v))) j j :=
                isPath_append_iff.mpr ⟨z, hgz, hpathY⟩
              have hloop1 : Htpy _ j j ((γ u ++ (e :: t₁)) ++ revPath (γ z)) [] := by
                refine hNullS j _ hSj.1 hX ?_
                refine pathIn_append (pathIn_append ?_ (pathIn_cons hSe hin1)) ?_
                · exact pathIn_mono (fun p h => (hJS' p h).1) (hγ u hu).2
                · exact pathIn_revPath (pathIn_mono (fun p h => (hJS' p h).1) (hγ z hJz).2)
              have hlen2 : t₂.length ≤ n := by
                grind
              have hUt₂ : PathIn U t₂ := by
                have hUt' : PathIn U (t₁ ++ t₂) := by simp_all
                exact pathIn_of_append_right hUt'
              have hloop2 : Htpy _ j j (γ z ++ (t₂ ++ revPath (γ v))) [] := by
                simp_all
              have hcancel : Htpy _ j j
                  ((γ u ++ (e :: t₁)) ++ [] ++ (t₂ ++ revPath (γ v)))
                  ((γ u ++ (e :: t₁)) ++ (revPath (γ z) ++ γ z) ++ (t₂ ++ revPath (γ v))) :=
                (htpy_revPath_append hgz).symm.congr_append hpath1 hpathY
              have hfinal : Htpy _ j j
                  (((γ u ++ (e :: t₁)) ++ revPath (γ z)) ++ (γ z ++ (t₂ ++ revPath (γ v))))
                  ([] ++ []) := Htpy.append_congr hX hY hloop1 hloop2
              have hcomb : Htpy _ j j
                  ((γ u ++ (e :: t₁)) ++ [] ++ (t₂ ++ revPath (γ v))) [] := by
                refine hcancel.trans ?_
                simp_all
              simp_all
            rcases hmix e.1.1.1 e.1.1.2 e.1.2 hUe.1 hUe.2 with hside | hside
            · exact side A B hmix hA (fun _ h => h) (fun _ h => h) hside
            · exact side B A (fun a b hab ha hb => (hmix a b hab ha hb).symm) hB
                (fun _ h => ⟨h.2, h.1⟩) (fun _ h => ⟨h.2, h.1⟩) hside
  intro v l hUv hp hUl
  cases l with
  | nil => exact Htpy.refl _
  | cons e t =>
      have hcase : ∀ S, NullIn S → ConnectedIn S → (∀ p, S p → U p) → S v → S j →
          Htpy _ v v (e :: t) [] := by
        intro S hNullS hconnS hSU hSv hSj
        obtain ⟨d, hd, hdin⟩ := hconnS v j hSv hSj
        have hdU := pathIn_mono hSU hdin
        have hq : IsPathX (orderCx P)
            (revPath d ++ ((e :: t) ++ d)) j j :=
          isPath_append_iff.mpr ⟨v, isPath_revPath hd,
            isPath_append_iff.mpr ⟨v, hp, hd⟩⟩
        have hqU :=
          pathIn_append (pathIn_revPath hdU) (pathIn_append hUl hdU)
        have hkey := key _ _ j j le_rfl hq hqU hj hj
        have hq0 : Htpy _ j j (revPath d ++ ((e :: t) ++ d)) [] := by
          simp_all
        have e1 :=
          hq0.congr_append hd (isPath_revPath hd)
        have e2 : Htpy _ v v (d ++ [] ++ revPath d) [] := by
          simpa using htpy_append_revPath hd
        have hdd : IsPathX (orderCx P) (d ++ revPath d) v v :=
          isPath_append_iff.mpr ⟨j, hd, isPath_revPath hd⟩
        have f1 :=
          Htpy.append_congr hp (isPath_nil' v) (Htpy.refl _) (htpy_append_revPath hd).symm
        have f2 :=
          Htpy.append_congr (isPath_nil' v)
            (isPath_append_iff.mpr ⟨v, hp, hdd⟩) (htpy_append_revPath hd).symm (Htpy.refl _)
        have e3 : Htpy _ v v (e :: t)
            (d ++ (revPath d ++ ((e :: t) ++ d)) ++ revPath d) := by
          simpa using f1.trans f2
        exact (e3.trans e1).trans e2
      grind

/-- Under the hypotheses of the gluing lemma the union is connected. -/
theorem connectedIn_union {A B U} (hU : ∀ p, U p ↔ (A p ∨ B p))
    (hAconn : ConnectedIn A) (hBconn : ConnectedIn B) {j : P} (hj : A j ∧ B j) :
    ConnectedIn U := by
  have hAU : ∀ p, A p → U p := by simp_all
  have hBU : ∀ p, B p → U p := by simp_all
  have hside : ∀ u, U u → ∃ l, IsPathX (orderCx P) l u j ∧ PathIn U l := by
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
