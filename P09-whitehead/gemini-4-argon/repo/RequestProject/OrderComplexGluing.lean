module

public import RequestProject.MirrorSimplyConnected

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb

universe u

section

variable {P Q : Type u} [Preorder P] [Preorder Q]

def orderCxMap (f : P → Q) (hf : Monotone f) : Hom (orderCx P) (orderCx Q) where
  onV := f
  onE e := (⟨(f e.1.1, f e.1.2), hf e.2⟩ : OrdEdge Q)
  onF t := (⟨(f t.1.1, f t.1.2.1, f t.1.2.2), hf t.2.1, hf t.2.2⟩ : OrdTri Q)
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF _ := rfl

@[simp] theorem orderCxMap_onV (f : P → Q) (hf : Monotone f) (p : P) :
    (orderCxMap f hf).onV p = f p := rfl

end

variable {P : Type u} [Preorder P]

def PathIn (A : P → Prop) (l : List ((orderCx P).E × Bool)) : Prop :=
  ∀ e ∈ l, A e.1.1.1 ∧ A e.1.1.2

theorem pathIn_nil (A : P → Prop) : PathIn A ([] : List ((orderCx P).E × Bool)) := by
  intro _ he; cases he

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
  ⟨h e (by simp), fun x hx => h x (by simp [hx])⟩

theorem pathIn_append {A : P → Prop} {l l' : List ((orderCx P).E × Bool)}
    (h : PathIn A l) (h' : PathIn A l') : PathIn A (l ++ l') := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact h x hx
  · exact h' x hx

theorem pathIn_of_append_left {A : P → Prop} {l l' : List ((orderCx P).E × Bool)}
    (h : PathIn A (l ++ l')) : PathIn A l := fun x hx => h x (by simp [hx])

theorem pathIn_of_append_right {A : P → Prop} {l l' : List ((orderCx P).E × Bool)}
    (h : PathIn A (l ++ l')) : PathIn A l' := fun x hx => h x (by simp [hx])

theorem pathIn_revPath {A : P → Prop} {l : List ((orderCx P).E × Bool)} (h : PathIn A l) :
    PathIn A (revPath l) := by
  intro x hx
  simp only [revPath, List.mem_reverse, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact h y hy

theorem pathIn_mono {A B : P → Prop} (hAB : ∀ p, A p → B p)
    {l : List ((orderCx P).E × Bool)} (h : PathIn A l) : PathIn B l :=
  fun x hx => ⟨hAB _ (h x hx).1, hAB _ (h x hx).2⟩

section

variable {A : P → Prop}

theorem monotone_subtypeVal : Monotone (fun p : {p : P // A p} => (p : P)) :=
  fun _ _ h => h

def subposetHom (A : P → Prop) : Hom (orderCx {p : P // A p}) (orderCx P) :=
  orderCxMap Subtype.val monotone_subtypeVal

def liftGermIn (e : (orderCx P).E × Bool) (h : A e.1.1.1 ∧ A e.1.1.2) :
    (orderCx {p : P // A p}).E × Bool :=
  ((⟨(⟨e.1.1.1, h.1⟩, ⟨e.1.1.2, h.2⟩), e.1.2⟩ : OrdEdge {p : P // A p}), e.2)

def liftPathIn : (l : List ((orderCx P).E × Bool)) → PathIn A l →
    List ((orderCx {p : P // A p}).E × Bool)
  | [], _ => []
  | e :: t, h => liftGermIn e (pathIn_of_cons h).1 :: liftPathIn t (pathIn_of_cons h).2

theorem mapPath_liftPathIn : ∀ (l : List ((orderCx P).E × Bool)) (h : PathIn A l),
    mapPath (subposetHom A) (liftPathIn l h) = l
  | [], _ => rfl
  | e :: t, h => by
      simp only [liftPathIn, mapPath, List.map_cons]
      rw [show List.map _ (liftPathIn t (pathIn_of_cons h).2) = t from
        mapPath_liftPathIn t (pathIn_of_cons h).2]
      rfl

theorem isPath_liftPathIn : ∀ (l : List ((orderCx P).E × Bool)) (h : PathIn A l) {u v : P}
    (hu : A u) (hv : A v), IsPath (orderCx P).src (orderCx P).tgt l u v →
    IsPath (orderCx {p : P // A p}).src (orderCx {p : P // A p}).tgt (liftPathIn l h)
      ⟨u, hu⟩ ⟨v, hv⟩
  | [], _, _, _, _, _, rfl => rfl
  | (e, false) :: t, h, _, _, _, hv, ⟨hstart, hrest⟩ =>
      ⟨Subtype.ext hstart, isPath_liftPathIn t (pathIn_of_cons h).2 (pathIn_of_cons h).1.1 hv hrest⟩
  | (e, true) :: t, h, _, _, _, hv, ⟨hstart, hrest⟩ =>
      ⟨Subtype.ext hstart, isPath_liftPathIn t (pathIn_of_cons h).2 (pathIn_of_cons h).1.2 hv hrest⟩

theorem htpy_nil_of_pathIn (hA : SimplyConnected (orderCx {p : P // A p}))
    {v : P} (hv : A v) {l : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt l v v) (hl : PathIn A l) :
    Htpy (orderCx P) v v l [] := by
  have := mapPath_htpy (subposetHom A) (hA ⟨v, hv⟩ (liftPathIn l hl) (isPath_liftPathIn l hl hv hv hp))
  rwa [mapPath_liftPathIn l hl] at this

end

def NullIn (A : P → Prop) : Prop :=
  ∀ (v : P) (l : List ((orderCx P).E × Bool)), A v →
    IsPath (orderCx P).src (orderCx P).tgt l v v → PathIn A l → Htpy (orderCx P) v v l []

def ConnectedIn (A : P → Prop) : Prop :=
  ∀ u v : P, A u → A v → ∃ l, IsPath (orderCx P).src (orderCx P).tgt l u v ∧ PathIn A l

theorem nullIn_of_simplyConnected {A : P → Prop}
    (hA : SimplyConnected (orderCx {p : P // A p})) : NullIn A :=
  fun _ _ hv hp hl => htpy_nil_of_pathIn hA hv hp hl

theorem pathIn_mapPath (A : P → Prop) (l : List ((orderCx {p : P // A p}).E × Bool)) :
    PathIn A (mapPath (subposetHom A) l) := by
  intro e he
  simp only [mapPath, List.mem_map] at he
  obtain ⟨x, _, rfl⟩ := he
  exact ⟨x.1.1.1.2, x.1.1.2.2⟩

theorem connectedIn_of_isConnected {A : P → Prop} (h : IsConnected (orderCx {p : P // A p})) :
    ConnectedIn A := fun u v hu hv =>
  let ⟨l, hl⟩ := h ⟨u, hu⟩ ⟨v, hv⟩
  ⟨mapPath (subposetHom A) l, isPath_mapPath (subposetHom A) hl, pathIn_mapPath A l⟩

theorem pathIn_congr {A A' : P → Prop} (h : ∀ p, A p ↔ A' p)
    {l : List ((orderCx P).E × Bool)} (hl : PathIn A l) : PathIn A' l :=
  pathIn_mono (fun p => (h p).1) hl

theorem nullIn_congr {A A' : P → Prop} (h : ∀ p, A p ↔ A' p) (hA : NullIn A) : NullIn A' :=
  fun v l hv hp hl => hA v l ((h v).2 hv) hp (pathIn_congr (fun p => (h p).symm) hl)

theorem connectedIn_congr {A A' : P → Prop} (h : ∀ p, A p ↔ A' p) (hA : ConnectedIn A) :
    ConnectedIn A' := fun u v hu hv =>
  let ⟨l, hl, hlin⟩ := hA u v ((h u).2 hu) ((h v).2 hv)
  ⟨l, hl, pathIn_congr h hlin⟩

theorem split_side {S S' U : P → Prop}
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (S a ∧ S b) ∨ (S' a ∧ S' b)) :
    ∀ (t : List ((orderCx P).E × Bool)) (w v : P),
      IsPath (orderCx P).src (orderCx P).tgt t w v → PathIn U t → (S v ∧ S' v) → S w →
      ∃ (t₁ t₂ : List ((orderCx P).E × Bool)) (z : P), t = t₁ ++ t₂ ∧
        IsPath (orderCx P).src (orderCx P).tgt t₁ w z ∧
        IsPath (orderCx P).src (orderCx P).tgt t₂ z v ∧ (S z ∧ S' z) ∧ PathIn S t₁
  | [], w, _, rfl, _, hv, _ => ⟨[], [], w, rfl, rfl, rfl, hv, pathIn_nil S⟩
  | e :: t, w, v, ⟨hstart, hrest⟩, hUl, hv, hw => by
      by_cases hJ : S w ∧ S' w
      · exact ⟨[], e :: t, w, rfl, rfl, ⟨hstart, hrest⟩, hJ, pathIn_nil S⟩
      · obtain ⟨hUe, hUt⟩ := pathIn_of_cons hUl
        have hSe : S e.1.1.1 ∧ S e.1.1.2 := (hmix _ _ e.1.2 hUe.1 hUe.2).resolve_right fun h =>
          hJ ⟨hw, by rcases e with ⟨_, _ | _⟩ <;> exact hstart ▸ by tauto⟩
        have hSw : S (germTgt (orderCx P).src (orderCx P).tgt e) := by
          rcases e with ⟨_, _ | _⟩ <;> tauto
        obtain ⟨t₁, t₂, z, hteq, hp1, hp2, hz, hin1⟩ :=
          split_side hmix t _ v hrest hUt hv hSw
        exact ⟨e :: t₁, t₂, z, by simp [hteq], ⟨hstart, hp1⟩, hp2, hz, pathIn_cons hSe hin1⟩

theorem connectedIn_union {A B U : P → Prop} (hU : ∀ p, U p ↔ (A p ∨ B p))
    (hAconn : ConnectedIn A) (hBconn : ConnectedIn B) {j : P} (hj : A j ∧ B j) :
    ConnectedIn U := by
  have hside (u : P) (hu : U u) : ∃ l, IsPath (orderCx P).src (orderCx P).tgt l u j ∧ PathIn U l := by
    rcases (hU u).1 hu with h | h
    · obtain ⟨l, hl, hlin⟩ := hAconn u j h hj.1
      exact ⟨l, hl, pathIn_mono (fun p hp => (hU p).2 (.inl hp)) hlin⟩
    · obtain ⟨l, hl, hlin⟩ := hBconn u j h hj.2
      exact ⟨l, hl, pathIn_mono (fun p hp => (hU p).2 (.inr hp)) hlin⟩
  intro u v hu hv
  obtain ⟨l, hl, hlin⟩ := hside u hu
  obtain ⟨m, hm, hmin⟩ := hside v hv
  exact ⟨l ++ revPath m, hl.append (isPath_revPath hm), pathIn_append hlin (pathIn_revPath hmin)⟩

theorem htpy_nil_of_pathIn_union {A B U : P → Prop}
    (hU : ∀ p, U p ↔ (A p ∨ B p))
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    (hA : NullIn A) (hB : NullIn B)
    (hAconn : ConnectedIn A) (hBconn : ConnectedIn B)
    (hJconn : ConnectedIn (fun p => A p ∧ B p))
    {j : P} (hj : A j ∧ B j) :
    NullIn U := by
  classical
  have hex (u : P) : ∃ g : List ((orderCx P).E × Bool),
      ((A u ∧ B u) → IsPath (orderCx P).src (orderCx P).tgt g j u ∧
        PathIn (fun p => A p ∧ B p) g) ∧ (u = j → g = []) := by
    by_cases hu : u = j
    · subst hu; exact ⟨[], fun _ => ⟨rfl, pathIn_nil _⟩, fun _ => rfl⟩
    · by_cases h : A u ∧ B u
      · obtain ⟨g, hg⟩ := hJconn j u hj h
        exact ⟨g, fun _ => hg, fun hc => absurd hc hu⟩
      · exact ⟨[], fun hc => absurd hc h, fun _ => rfl⟩
  choose γ hγ hγj using hex
  have key : ∀ (n : ℕ) (l : List ((orderCx P).E × Bool)) (u v : P), l.length ≤ n →
      IsPath (orderCx P).src (orderCx P).tgt l u v → PathIn U l →
      (A u ∧ B u) → (A v ∧ B v) →
      Htpy (orderCx P) j j (γ u ++ l ++ revPath (γ v)) [] := by
    intro n
    induction n with
    | zero =>
        intro l u v hlen hp _ hu _
        cases List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hlen)
        cases hp
        simpa using htpy_append_revPath (hγ u hu).1
    | succ n ih =>
        intro l u v hlen hp hUl hu hv
        cases l with
        | nil =>
            cases hp
            simpa using htpy_append_revPath (hγ u hu).1
        | cons e t =>
            obtain ⟨hstart, hrest⟩ := hp
            obtain ⟨hUe, hUt⟩ := pathIn_of_cons hUl
            have side (S S' : P → Prop)
                (hmixS : ∀ a b : P, a ≤ b → U a → U b → (S a ∧ S b) ∨ (S' a ∧ S' b))
                (hNullS : NullIn S)
                (hJS : ∀ p : P, S p ∧ S' p ↔ A p ∧ B p)
                (hSe : S e.1.1.1 ∧ S e.1.1.2) :
                Htpy (orderCx P) j j (γ u ++ (e :: t) ++ revPath (γ v)) [] := by
              have hSw : S (germTgt (orderCx P).src (orderCx P).tgt e) := by
                rcases e with ⟨_, _ | _⟩ <;> tauto
              obtain ⟨t₁, t₂, z, hteq, hp1, hp2, hz, hin1⟩ :=
                split_side hmixS t _ v hrest hUt ((hJS v).2 hv) hSw
              have hJz : A z ∧ B z := (hJS z).1 hz
              have hgu := (hγ u hu).1
              have hgv := (hγ v hv).1
              have hgz := (hγ z hJz).1
              have hpath1 : IsPath (orderCx P).src (orderCx P).tgt (γ u ++ (e :: t₁)) j z :=
                hgu.append ⟨hstart, hp1⟩
              have hpathY : IsPath (orderCx P).src (orderCx P).tgt (t₂ ++ revPath (γ v)) z j :=
                hp2.append (isPath_revPath hgv)
              have hX := hpath1.append (isPath_revPath hgz)
              have hY := hgz.append hpathY
              have hloop1 : Htpy (orderCx P) j j ((γ u ++ (e :: t₁)) ++ revPath (γ z)) [] :=
                hNullS j _ ((hJS j).2 hj).1 hX (pathIn_append
                  (pathIn_append (pathIn_mono (fun p h => ((hJS p).2 h).1) (hγ u hu).2)
                    (pathIn_cons hSe hin1))
                  (pathIn_revPath (pathIn_mono (fun p h => ((hJS p).2 h).1) (hγ z hJz).2)))
              have hlen2 : t₂.length ≤ n := by
                simp only [hteq, List.length_cons, List.length_append] at hlen; omega
              have hloop2 : Htpy (orderCx P) j j (γ z ++ (t₂ ++ revPath (γ v))) [] := by
                simpa [List.append_assoc] using
                  ih t₂ z v hlen2 hp2 (pathIn_of_append_right (hteq ▸ hUt)) hJz hv
              have hcomb : Htpy (orderCx P) j j
                  ((γ u ++ (e :: t₁)) ++ [] ++ (t₂ ++ revPath (γ v))) [] :=
                ((htpy_revPath_append hgz).symm.congr_append hpath1 hpathY).trans
                  (by simpa [List.append_assoc] using Htpy.append_congr hX hY hloop1 hloop2)
              simpa [hteq, List.append_assoc] using hcomb
            rcases hmix _ _ e.1.2 hUe.1 hUe.2 with hside | hside
            · exact side A B hmix hA (fun _ => Iff.rfl) hside
            · exact side B A (fun a b hab ha hb => (hmix a b hab ha hb).symm) hB
                (fun _ => and_comm) hside
  intro v l hUv hp hUl
  obtain ⟨d, hd, hdU⟩ := connectedIn_union hU hAconn hBconn hj v j hUv ((hU j).2 (.inl hj.1))
  have hq : IsPath (orderCx P).src (orderCx P).tgt (revPath d ++ (l ++ d)) j j :=
    (isPath_revPath hd).append (hp.append hd)
  have hkey := key _ _ j j le_rfl hq
    (pathIn_append (pathIn_revPath hdU) (pathIn_append hUl hdU)) hj hj
  rw [hγj j rfl] at hkey
  have hq0 : Htpy (orderCx P) j j (revPath d ++ (l ++ d)) [] := by simpa [revPath] using hkey
  have hdd := hd.append (isPath_revPath hd)
  have f1 := Htpy.append_congr hp (isPath_nil' v) (Htpy.refl _) (htpy_append_revPath hd).symm
  have f2 := Htpy.append_congr (isPath_nil' v) (hp.append hdd) (htpy_append_revPath hd).symm (Htpy.refl _)
  have e3 : Htpy (orderCx P) v v l (d ++ (revPath d ++ (l ++ d)) ++ revPath d) := by
    simpa [List.append_assoc] using f1.trans f2
  exact (e3.trans (hq0.congr_append hd (isPath_revPath hd))).trans
    (by simpa using htpy_append_revPath hd)
