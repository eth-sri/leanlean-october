module

public import RequestProject.MirrorSimplyConnected

@[expose] public section

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

namespace FiniteChains
namespace Comb

universe u

/-! ### Functoriality of the order complex -/

section Map

variable {P Q : Type u} [Preorder P] [Preorder Q]

variable (f : P → Q) (hf : Monotone f)

/-- A monotone map induces a cellular map of order complexes. -/
def orderCxMap : Hom (orderCx P) (orderCx Q) := relSkeletonMap f hf

@[simp] theorem orderCxMap_onV (p : P) :
    (orderCxMap f hf).onV p = f p := rfl

end Map

/-! ### Paths inside a subposet -/

section PathIn

variable {P : Type u} [Preorder P]

variable (A : P → Prop)

/-- Every edge of the path `l` has both endpoints in `A`. -/
def PathIn (l : List ((orderCx P).E × Bool)) :=
  ∀ e ∈ l, A e.1.1.1 ∧ A e.1.1.2

theorem pathIn_nil : PathIn A ([]) := by
  intro e he
  simp_all

variable {A : P → Prop}

variable {e : (orderCx P).E × Bool} {l : List ((orderCx P).E × Bool)}

theorem pathIn_cons (he : A e.1.1.1 ∧ A e.1.1.2) (hl : PathIn A l) :
    PathIn A (e :: l) := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | h
  · exact he
  · exact hl x h

theorem pathIn_of_cons (h : PathIn A (e :: l)) :
    (A e.1.1.1 ∧ A e.1.1.2) ∧ PathIn A l :=
  by grind [PathIn]

variable {l l' : List ((orderCx P).E × Bool)}

theorem pathIn_append
    (h : PathIn A l) (h' : PathIn A l') : PathIn A (l ++ l') := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact h x hx
  · exact h' x hx

section

variable (h : PathIn A (l ++ l'))
include h

theorem pathIn_of_append_left : PathIn A l := fun x hx => h x (by simp [hx])

theorem pathIn_of_append_right : PathIn A l' := fun x hx => h x (by simp [hx])

end

theorem pathIn_revPath {l : List _} (h : PathIn A l) :
    PathIn A (revPath l) := by
  intro x hx
  simp only [revPath, List.mem_reverse, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact h y hy

theorem pathIn_mono {A B : P → Prop} (hAB : ∀ p, A p → B p)
    {l : List _} (h : PathIn A l) : PathIn B l :=
  by grind [PathIn]

end PathIn

/-! ### Lifting a path to a subposet -/

section Lift

variable {P : Type u} [Preorder P] {A : P → Prop}

/-- The inclusion of a subposet. -/
theorem monotone_subtypeVal : Monotone (fun p : {p : P // A p} => (p : P)) :=
  by solve_by_elim

/-- The cellular map induced by the inclusion of a subposet. -/
def subposetHom (A : P → Prop) :=
  orderCxMap (fun p : {p : P // A p} => (p : P)) monotone_subtypeVal

/-- The lift of one oriented edge with endpoints in `A`. -/
def liftGermIn (e : (orderCx P).E × Bool) (h : A e.1.1.1 ∧ A e.1.1.2) :
    (orderCx {p : P // A p}).E × Bool :=
  ((⟨(⟨e.1.1.1, h.1⟩, ⟨e.1.1.2, h.2⟩), e.1.2⟩), e.2)

/-- The lift of a path all of whose edges have endpoints in `A`. -/
def liftPathIn : (l : List _) → PathIn A l →
    List ((orderCx {p : P // A p}).E × Bool)
  | [], _ => []
  | e :: t, h => liftGermIn e (pathIn_of_cons h).1 :: liftPathIn t (pathIn_of_cons h).2

theorem mapPath_liftPathIn : ∀ (l : List _) (h : PathIn A l),
    mapPath (subposetHom A) (liftPathIn l h) = l
  | [], _ => rfl
  | e :: t, h => by
      simp only [liftPathIn, mapPath, List.map_cons]
      rw [show (List.map _ _) = t from mapPath_liftPathIn t _]
      rfl

theorem isPath_liftPathIn : ∀ (l : List _) (h : PathIn A l) {u v : P}
    (hu : A u) (hv : A v), IsPath (orderCx P).src (orderCx P).tgt l u v →
    IsPath (orderCx {p : P // A p}).src (orderCx {p : P // A p}).tgt (liftPathIn l h)
      ⟨u, hu⟩ ⟨v, hv⟩
  | [], _, u, v, hu, hv, hp => by
      aesop
  | e :: t, h, u, v, hu, hv, hp => by
      obtain ⟨hstart, hrest⟩ := hp
      obtain ⟨e, tag⟩ := e
      cases tag with
      | false =>
          refine ⟨Subtype.ext hstart, ?_⟩
          exact isPath_liftPathIn t _ _ hv hrest
      | true =>
          refine ⟨Subtype.ext hstart, ?_⟩
          exact isPath_liftPathIn t _ _ hv hrest

/-- **A loop inside a simply connected subposet is null-homotopic in the ambient complex.** -/
theorem htpy_nil_of_pathIn (hA : SimplyConnected (orderCx {p : P // A p}))
    {v : P} (hv : A v) {l : List _}
    (hp : IsPath (orderCx P).src (orderCx P).tgt l v v) (hl : PathIn A l) :
    Htpy _ v v l [] := by
  have hnull := hA _ _ (isPath_liftPathIn l hl hv hv hp)
  have := mapPath_htpy (subposetHom A) hnull
  rw [mapPath_liftPathIn l hl] at this <;> assumption

end Lift

/-! ### The gluing lemma -/

section VanKampen

variable {P : Type u} [Preorder P]

variable (A : P → Prop)

/-- Every loop of the ambient order complex all of whose edges lie in `A` is null-homotopic in
the ambient complex. -/
def NullIn :=
  ∀ (v : P) (l : List _), A v →
    IsPath (orderCx P).src (orderCx P).tgt l v v → PathIn A l → Htpy _ v v l []

/-- Any two elements of `A` are joined by a path all of whose edges lie in `A`. -/
def ConnectedIn :=
  ∀ u v : P, A u → A v → ∃ l, IsPath (orderCx P).src (orderCx P).tgt l u v ∧ PathIn A l

/-- A simply connected subposet gives `NullIn`. -/
theorem nullIn_of_simplyConnected {A : P → Prop}
    (hA : SimplyConnected (orderCx {p : P // A p})) : NullIn A :=
  fun _ _ hv hp hl => htpy_nil_of_pathIn hA hv hp hl

/-- The image of a path of the subposet complex lies in the subposet. -/
theorem pathIn_mapPath (A : P → Prop) (l : List _) :
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
  exact ⟨mapPath _ l, isPath_mapPath _ hl, pathIn_mapPath A l⟩

section

variable {A A' : P → Prop} (h : ∀ p, A p ↔ A' p)
include h

theorem pathIn_congr
    {l : List _} (hl : PathIn A l) : PathIn A' l :=
  by grind [PathIn]

theorem nullIn_congr (hA : NullIn A) : NullIn A' :=
  fun v l hv hp hl => hA v l ((h v).2 hv) hp (pathIn_congr (fun p => (h p).symm) hl)

theorem connectedIn_congr (hA : ConnectedIn A) :
    ConnectedIn A' := by
  intro u v hu hv
  obtain ⟨l, hl, hlin⟩ := hA u v ((h u).2 hu) ((h v).2 hv)
  grind [pathIn_congr]

end

/-- **Cutting a path at its first return to the intersection.**  A path that starts on the `S`
side runs inside `S` until it first meets `S ∩ S'`. -/
theorem split_side {S S' U : P → Prop}
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (S a ∧ S b) ∨ (S' a ∧ S' b)) :
    ∀ (t : List _) (w v : P),
      IsPath (orderCx P).src (orderCx P).tgt t w v → PathIn U t → (S v ∧ S' v) → S w →
      ∃ (t₁ t₂ : List _) (z : P), t = t₁ ++ t₂ ∧
        IsPath (orderCx P).src (orderCx P).tgt t₁ w z ∧
        IsPath (orderCx P).src (orderCx P).tgt t₂ z v ∧ (S z ∧ S' z) ∧ PathIn S t₁ := by
  intro t
  induction t with
  | nil =>
      simp_all [pathIn_nil]
  | cons e t ih =>
      intro w v hp hUl hv hw
      by_cases hJ : S w ∧ S' w
      · exact ⟨[], e :: t, w, rfl, rfl, hp, hJ, pathIn_nil S⟩
      · obtain ⟨hstart, hrest⟩ := hp
        obtain ⟨hUe, hUt⟩ := pathIn_of_cons hUl
        have hS' := fun h => hJ ⟨hw, h⟩
        have hSe : S e.1.1.1 ∧ S e.1.1.2 := by
          rcases hmix _ _ e.1.2 hUe.1 hUe.2 with h | h
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
          ih _ v hrest hUt hv hSw
        exact ⟨e :: t₁, t₂, z, by simp [hteq], ⟨hstart, hp1⟩, hp2, hz, pathIn_cons hSe hin1⟩

variable {A B U : P → Prop} (hU : ∀ p, U p ↔ (A p ∨ B p))
include hU

/-- **The gluing lemma at the level of `π₁`.**  Let `U` be covered by two subposets `A` and `B`
such that no comparability inside `U` is mixed, let loops inside `A` and inside `B` be
null-homotopic in the ambient order complex, let `A`, `B` and their intersection `J = A ∩ B` be
connected and let `J` be nonempty.  Then every loop inside `U` is null-homotopic in the ambient
order complex.  This is the van Kampen step of the chamber induction, written so that its
conclusion is again a hypothesis of the same shape. -/
theorem htpy_nil_of_pathIn_union
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    (hA : NullIn A) (hB : NullIn B)
    (hAconn : ConnectedIn A) (hBconn : ConnectedIn B)
    (hJconn : ConnectedIn (fun p => A p ∧ B p))
    {j : P} (hj : A j ∧ B j) :
    NullIn U := by
  classical
  have hex : ∀ u : P, ∃ g : List _,
      ((A u ∧ B u) → IsPath (orderCx P).src (orderCx P).tgt g j u ∧
        PathIn (fun p => A p ∧ B p) g) ∧ (u = j → g = []) := by
    intro u
    by_cases hu : u = j
    · simp_all [pathIn_nil]
    · by_cases h : A u ∧ B u
      · obtain ⟨g, hg⟩ := hJconn j u hj h <;> grind
      · simp_all
  choose γ hγ hγj using hex
  have key : ∀ (n : ℕ) (l : List _) (u v : P), l.length ≤ n →
      IsPath (orderCx P).src (orderCx P).tgt l u v → PathIn U l →
      (A u ∧ B u) → (A v ∧ B v) →
      Htpy _ j j (γ u ++ l ++ revPath (γ v)) [] := by
    intro n
    induction n with
    | zero =>
        intro l u v hlen hp _ hu _
        have hl := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hlen)
        subst hl
        have huv : u = v := hp
        grind [htpy_append_revPath]
    | succ n ih =>
        intro l u v hlen hp hUl hu hv
        cases l with
        | nil =>
            grind
        | cons e t =>
            obtain ⟨hstart, hrest⟩ := hp
            obtain ⟨hUe, hUt⟩ := pathIn_of_cons hUl
            have side : ∀ S S' : P → Prop,
                (∀ a b : P, a ≤ b → U a → U b → (S a ∧ S b) ∨ (S' a ∧ S' b)) →
                NullIn S →
                (∀ p : P, S p ∧ S' p → A p ∧ B p) →
                (∀ p : P, A p ∧ B p → S p ∧ S' p) →
                (S e.1.1.1 ∧ S e.1.1.2) →
                Htpy _ j j (γ u ++ (e :: t) ++ revPath (γ v)) [] := by
              intro S S' hmixS hNullS hJS hJS' hSe
              have hSw : S (germTgt (orderCx P).src (orderCx P).tgt e) := by
                obtain ⟨ee, tag⟩ := e
                cases tag with
                | false => exact hSe.1
                | true => exact hSe.2
              obtain ⟨t₁, t₂, z, hteq, hp1, hp2, hz, hin1⟩ :=
                split_side hmixS t _ v hrest hUt (hJS' v hv) hSw
              have hJz := hJS z hz
              have hgz := (hγ z hJz).1
              have hpath1 : IsPath _ _ (γ u ++ (e :: t₁)) j z :=
                isPath_append_iff.mpr ⟨u, (hγ u hu).1, ⟨hstart, hp1⟩⟩
              have hpathY : IsPath _ _
                  (t₂ ++ revPath (γ v)) z j :=
                isPath_append_iff.mpr ⟨v, hp2, isPath_revPath (hγ v hv).1⟩
              have hX : IsPath _ _
                  ((γ u ++ (e :: t₁)) ++ revPath (γ z)) j j :=
                isPath_append_iff.mpr ⟨z, hpath1, isPath_revPath hgz⟩
              have hloop1 : Htpy _ j j ((γ u ++ (e :: t₁)) ++ revPath (γ z)) [] := by
                refine hNullS j _ (hJS' j hj).1 hX ?_
                refine pathIn_append (pathIn_append ?_ (pathIn_cons hSe hin1)) ?_
                · exact pathIn_mono (fun p h => (hJS' p h).1) (hγ u hu).2
                · exact pathIn_revPath (pathIn_mono (fun p h => (hJS' p h).1) (hγ z hJz).2)
              have hlen2 : t₂.length ≤ n := by
                grind
              have hUt₂ : PathIn U t₂ := pathIn_of_append_right (by rw [← hteq]; exact hUt)
              have hloop2 : Htpy _ j j (γ z ++ (t₂ ++ revPath (γ v))) [] := by
                grind
              have hfinal := Htpy.append_congr hX (isPath_append_iff.mpr ⟨z, hgz, hpathY⟩) hloop1 hloop2
              have hcomb : Htpy _ j j
                  ((γ u ++ (e :: t₁)) ++ [] ++ (t₂ ++ revPath (γ v))) [] := by
                refine ((htpy_revPath_append hgz).symm.congr_append hpath1 hpathY).trans ?_
                grind
              grind
            rcases hmix _ _ e.1.2 hUe.1 hUe.2 with hside | hside
            · exact side A B hmix hA (fun _ h => h) (fun _ h => h) hside
            · exact side B A (fun a b hab ha hb => (hmix a b hab ha hb).symm) hB
                (fun _ h => ⟨h.2, h.1⟩) (fun _ h => ⟨h.2, h.1⟩) hside
  intro v l hUv hp hUl
  cases l with
  | nil => exact Htpy.refl _
  | cons e t =>
      have hcase : ∀ S : P → Prop, NullIn S → ConnectedIn S → (∀ p, S p → U p) → S v → S j →
          Htpy _ v v (e :: t) [] := by
        intro S hNullS hconnS hSU hSv hSj
        obtain ⟨d, hd, hdin⟩ := hconnS v j hSv hSj
        have hdU := pathIn_mono hSU hdin
        have hq : IsPath _ _
            (revPath d ++ ((e :: t) ++ d)) j j :=
          isPath_append_iff.mpr ⟨v, isPath_revPath hd,
            isPath_append_iff.mpr ⟨v, hp, hd⟩⟩
        have hkey := key _ _ j j le_rfl hq (pathIn_append (pathIn_revPath hdU) (pathIn_append hUl hdU)) hj hj
        rw [hγj j rfl] at hkey
        have hq0 : Htpy _ j j (revPath d ++ ((e :: t) ++ d)) [] := by
          simpa [revPath] using hkey
        have e2 : Htpy _ v v (d ++ [] ++ revPath d) [] := by
          simpa using htpy_append_revPath hd
        have f2 :=
          Htpy.append_congr (isPath_nil' v)
            (isPath_append_iff.mpr ⟨v, hp, (isPath_append_iff.mpr ⟨j, hd, isPath_revPath hd⟩)⟩) (htpy_append_revPath hd).symm (Htpy.refl _)
        have e3 : Htpy _ v v (e :: t)
            (d ++ (revPath d ++ ((e :: t) ++ d)) ++ revPath d) := by
          simpa [List.append_assoc] using (Htpy.append_congr hp (isPath_nil' v) (Htpy.refl _) (htpy_append_revPath hd).symm).trans f2
        exact (e3.trans (hq0.congr_append hd (isPath_revPath hd))).trans e2
      grind

/-- Under the hypotheses of the gluing lemma the union is connected. -/
theorem connectedIn_union
    (hAconn : ConnectedIn A) (hBconn : ConnectedIn B) {j : P} (hj : A j ∧ B j) :
    ConnectedIn U := by
  have hside : ∀ (u : P), U u → ∃ l, IsPath (orderCx P).src (orderCx P).tgt l u j ∧ PathIn U l := by
    intro u hu
    rcases (hU u).1 hu with h | h
    · obtain ⟨l, hl, hlin⟩ := hAconn u j h hj.1
      grind [pathIn_mono]
    · obtain ⟨l, hl, hlin⟩ := hBconn u j h hj.2
      grind [pathIn_mono]
  intro u v hu hv
  obtain ⟨l, hl, hlin⟩ := hside u hu
  obtain ⟨m, hm, hmin⟩ := hside v hv
  exact ⟨l ++ revPath m, isPath_append_iff.mpr ⟨j, hl, isPath_revPath hm⟩,
    pathIn_append hlin (pathIn_revPath hmin)⟩

end VanKampen

end Comb
end FiniteChains
