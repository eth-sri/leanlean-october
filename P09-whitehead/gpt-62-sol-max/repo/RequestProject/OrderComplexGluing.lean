module

public import RequestProject.MirrorSimplyConnected
public import RequestProject.CombPathSubstitution

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

Choose paths from a common root to each vertex, using the intersection for vertices that
lie on both sides. The resulting closure of each oriented edge is null-homotopic on one
side; the root paths telescope around a loop.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Comb

universe u

/-! ### Functoriality of the order complex -/

abbrev chainCxMap {P Q : Type u} {r : P → P → Prop} {s : Q → Q → Prop}
    {hr : IsTrans P r} {hs : IsTrans Q s} (f : P → Q)
    (hf : ∀ {a b}, r a b → s (f a) (f b)) : Hom (chainCx r hr) (chainCx s hs) where
  onV := f
  onE e := ⟨(f e.1.1, f e.1.2), hf e.2⟩
  onF t := ⟨(f t.1.1, f t.1.2.1, f t.1.2.2), hf t.2.1, hf t.2.2⟩
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF _ := rfl

section Map

variable {P Q : Type u} [Preorder P] [Preorder Q]

/-- A monotone map induces a cellular map of order complexes. -/
def orderCxMap (f : P → Q) (hf : Monotone f) : Hom (orderCx P) (orderCx Q) :=
  chainCxMap (r := (· ≤ ·)) (s := (· ≤ ·))
    (hr := ⟨fun _ _ _ => le_trans⟩) (hs := ⟨fun _ _ _ => le_trans⟩) f (fun h => hf h)

@[simp] theorem orderCxMap_onV (f : P → Q) (hf : Monotone f) (p : P) :
    (orderCxMap f hf).onV p = f p := rfl

theorem orderCxMap_comp {R : Type u} [Preorder R]
    (f : P → Q) (g : Q → R) (hf : Monotone f) (hg : Monotone g) :
    (orderCxMap g hg).comp (orderCxMap f hf) = orderCxMap (g ∘ f) (hg.comp hf) := rfl

theorem orderCxMap_congr {f g : P → Q} (hf : Monotone f) (hg : Monotone g) (h : f = g) :
    orderCxMap f hf = orderCxMap g hg := by cases h; rfl

@[simp] theorem orderCxMap_id : orderCxMap (id : P → P) monotone_id = Hom.id (orderCx P) := rfl

end Map

/-! ### Paths inside a subposet -/

section PathIn

variable {P : Type u} [Preorder P]

/-- Every edge of the path `l` has both endpoints in `A`. -/
def PathIn (A : P → Prop) (l : List ((orderCx P).E × Bool)) : Prop :=
  ∀ e ∈ l, A e.1.1.1 ∧ A e.1.1.2

theorem pathIn_att_iff {A : P → Prop} (f : OrdTri P) :
    PathIn A ((orderCx P).att f) ↔ A f.1.1 ∧ A f.1.2.1 ∧ A f.1.2.2 := by
  simp only [PathIn, orderCx, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  tauto

theorem germ_ends_iff {B : P → Prop} (e : (orderCx P).E × Bool) :
    (B e.1.1.1 ∧ B e.1.1.2) ↔
      (B (germSrc (orderCx P).src (orderCx P).tgt e) ∧
        B (germTgt (orderCx P).src (orderCx P).tgt e)) := by
  obtain ⟨e, b⟩ := e
  cases b <;> simp only [germSrc, germTgt, Bool.false_eq_true, if_false, if_true]
  · exact and_comm
  · rfl

theorem germ_ends {C : P → Prop} {e : (orderCx P).E × Bool} (h : C e.1.1.1 ∧ C e.1.1.2) :
    C (germSrc (orderCx P).src (orderCx P).tgt e) ∧ C (germTgt (orderCx P).src (orderCx P).tgt e) :=
  (germ_ends_iff e).mp h

theorem pathIn_nil (A : P → Prop) : PathIn A ([] : List ((orderCx P).E × Bool)) := by
  tauto

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
  ⟨h e (by simp), fun x hx => h x (by aesop)⟩

theorem pathIn_append {A : P → Prop} {l l' : List ((orderCx P).E × Bool)}
    (h : PathIn A l) (h' : PathIn A l') : PathIn A (l ++ l') := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact h x hx
  · exact h' x hx

theorem pathIn_of_append_left {A : P → Prop} {l l' : List ((orderCx P).E × Bool)}
    (h : PathIn A (l ++ l')) : PathIn A l := fun x hx => h x (by aesop)

theorem pathIn_of_append_right {A : P → Prop} {l l' : List ((orderCx P).E × Bool)}
    (h : PathIn A (l ++ l')) : PathIn A l' := fun x hx => h x (by aesop)

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
  orderCxMap (fun p  => p) monotone_subtypeVal

/-- The lift of one oriented edge with endpoints in `A`. -/
def liftGermIn (e : (orderCx P).E × Bool) (h : A e.1.1.1 ∧ A e.1.1.2) :
    (orderCx {p : P // A p}).E × Bool :=
  (⟨(⟨e.1.1.1, h.1⟩, ⟨e.1.1.2, h.2⟩), e.1.2⟩, e.2)

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
      aesop
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
  assumption

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



theorem connectedIn_congr {A A' : P → Prop} (h : ∀ p, A p ↔ A' p) (hA : ConnectedIn A) :
    ConnectedIn A' := by
  grind +locals

/-- Van Kampen gluing: each edge closes up to a null loop by paths in its own side. -/
theorem htpy_nil_of_pathIn_union {A B U : P → Prop}
    (hU : ∀ p, U p ↔ (A p ∨ B p))
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    (hA : NullIn A) (hB : NullIn B)
    (hAconn : ConnectedIn A) (hBconn : ConnectedIn B)
    (hJconn : ConnectedIn (fun p => A p ∧ B p))
    {j : P} (hj : A j ∧ B j) : NullIn U := by
  classical
  have hex (v : P) : ∃ p : List ((orderCx P).E × Bool),
      (U v → IsPath (orderCx P).src (orderCx P).tgt p j v) ∧
        (A v → PathIn A p) ∧ (B v → PathIn B p) := by
    by_cases ha : A v <;> by_cases hb : B v
    · obtain ⟨p, hp, hpJ⟩ := hJconn j v hj ⟨ha, hb⟩
      exact ⟨p, fun _ => hp, fun _ => pathIn_mono (fun _ h => h.1) hpJ,
        fun _ => pathIn_mono (fun _ h => h.2) hpJ⟩
    · aesop
    · aesop
    · exact ⟨[], fun hu => ((hU v).mp hu).elim (fun h => (ha h).elim) (fun h => (hb h).elim),
        fun _ => pathIn_nil _, fun _ => pathIn_nil _⟩
  choose γ hγ hγA hγB using hex
  intro v l hv hp hl
  have hs (e) (he : e ∈ l) := germ_ends (hl e he)
  have h := htpy_telescope (X := orderCx P) (Y := orderCx P) (f := id) (γ := γ)
    (g := fun e => [e]) hγ (fun e hu hw => ?_) hp hv hv hs
  · simpa using h.trans (htpy_revPath_append (hγ _ hv))
  · let s := germSrc (orderCx P).src (orderCx P).tgt e
    let t := germTgt (orderCx P).src (orderCx P).tgt e
    have hpath := ((hγ s hu).append (isPath_single e)).append (isPath_revPath (hγ t hw))
    apply htpy_of_rooted_null (hγ s hu) (isPath_single e) (hγ t hw)
    have hside {S : P → Prop} (hS : NullIn S) (hjS : S j)
        (hγS : ∀ x, S x → PathIn S (γ x)) (he : S e.1.1.1 ∧ S e.1.1.2)  :=
      hS _ _ hjS hpath (pathIn_append (pathIn_append (hγS s (germ_ends he).1)
        (pathIn_cons he (pathIn_nil _))) (pathIn_revPath (hγS t (germ_ends he).2)))
    obtain ⟨h₁, h₂⟩ := (germ_ends_iff e).mpr ⟨hu, hw⟩
    exact (hmix _ _ e.1.2 h₁ h₂).elim (hside hA hj.1 hγA) (hside hB hj.2 hγB)

/-- Under the hypotheses of the gluing lemma the union is connected. -/
theorem connectedIn_union {A B U : P → Prop} (hU : ∀ p, U p ↔ (A p ∨ B p))
    (hAconn : ConnectedIn A) (hBconn : ConnectedIn B) {j : P} (hj : A j ∧ B j) :
    ConnectedIn U := by
  have hAU  := fun p h => (hU p).2 (Or.inl h)
  have hBU  := fun p h => (hU p).2 (Or.inr h)
  have hside : ∀ (u : P), U u → ∃ l, IsPath (orderCx P).src (orderCx P).tgt l u j ∧ PathIn U l := by
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
