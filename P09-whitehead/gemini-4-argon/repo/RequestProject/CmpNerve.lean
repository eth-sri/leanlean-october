module

public import RequestProject.BlockConnected
public import RequestProject.OrderCxConeNull

@[expose] public section

namespace FiniteChains.Davis

open RACG Mirror Comb

universe u v

section

variable {X : Complex2.{u}}

theorem htpy_of_loop_nil {a b : X.V} {p q : List (X.E × Bool)}
    (hp : IsPath X.src X.tgt p a b) (hq : IsPath X.src X.tgt q a b)
    (h : Htpy X a a (p ++ revPath q) []) : Htpy X a b p q := by
  have h1 : Htpy X a b (p ++ (revPath q ++ q)) q := by
    simpa using h.congr_append (r := ([] : List (X.E × Bool))) (s := q) rfl hq
  have h2 : Htpy X a b (p ++ (revPath q ++ q)) (p ++ []) :=
    Htpy.append_congr hp (isPath_append_iff.mpr ⟨a, isPath_revPath hq, hq⟩) (Htpy.refl p)
      (htpy_revPath_append hq)
  simpa using h2.symm.trans h1

theorem htpy_append_right {a b c : X.V} {p q r : List (X.E × Bool)}
    (hp : IsPath X.src X.tgt p a b) (hr : IsPath X.src X.tgt r b c) (h : Htpy X a b p q) :
    Htpy X a c (p ++ r) (q ++ r) :=
  Htpy.append_congr hp hr h (Htpy.refl r)

theorem htpy_append_left {a b c : X.V} {p q r : List (X.E × Bool)}
    (hr : IsPath X.src X.tgt r a b) (hp : IsPath X.src X.tgt p b c) (h : Htpy X b c p q) :
    Htpy X a c (r ++ p) (r ++ q) :=
  Htpy.append_congr hr hp (Htpy.refl r) h

end

variable {P : Type u} [PartialOrder P] [DecidableEq P]

def cmpRel (P : Type u) [PartialOrder P] : CommRel P where
  rel x y := x ≠ y ∧ (x ≤ y ∨ y ≤ x)
  rel_symm := fun {_ _} h => ⟨h.1.symm, h.2.symm⟩
  rel_irrefl _ h := h.1 rfl

theorem isSimplex_cmpRel_iff {σ : Finset P} :
    IsSimplex (cmpRel P) σ ↔ ∀ x ∈ σ, ∀ y ∈ σ, x ≤ y ∨ y ≤ x := by
  constructor
  · intro h x hx y hy
    exact if hxy : x = y then .inl (le_of_eq hxy) else (h x hx y hy hxy).2
  · intro h x hx y hy hxy
    exact ⟨hxy, h x hx y hy⟩

def spx1 (x : P) : NeSpx (cmpRel P) :=
  ⟨{x}, ⟨x, Finset.mem_singleton_self x⟩, isSimplex_singleton x⟩

omit [DecidableEq P] in
@[simp] theorem spx1_val (x : P) : (spx1 x).1 = {x} := rfl

def spx2 {x y : P} (h : x ≤ y) : NeSpx (cmpRel P) :=
  ⟨{x, y}, ⟨x, by simp⟩, isSimplex_cmpRel_iff.2 fun a ha b hb => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    exacts [.inl le_rfl, .inl h, .inr h, .inl le_rfl]⟩

@[simp] theorem spx2_val {x y : P} (h : x ≤ y) : (spx2 h).1 = {x, y} := rfl

theorem spx1_le_spx2_left {x y : P} (h : x ≤ y) : spx1 x ≤ spx2 h := by
  intro a ha; simp [Finset.mem_singleton.1 ha]

theorem spx1_le_spx2_right {x y : P} (h : x ≤ y) : spx1 y ≤ spx2 h := by
  intro a ha; simp [Finset.mem_singleton.1 ha]

def hop {a b c : NeSpx (cmpRel P)} (ha : a ≤ c) (hb : b ≤ c) :
    List ((orderCx (NeSpx (cmpRel P))).E × Bool) :=
  [ordPos ha, ordNeg hb]

def edgeHop {x y : P} (h : x ≤ y) : List ((orderCx (NeSpx (cmpRel P))).E × Bool) :=
  hop (spx1_le_spx2_left h) (spx1_le_spx2_right h)

theorem isPath_edgeHop {x y : P} (h : x ≤ y) :
    IsPath (orderCx (NeSpx (cmpRel P))).src (orderCx (NeSpx (cmpRel P))).tgt (edgeHop h)
      (spx1 x) (spx1 y) :=
  ⟨rfl, rfl, rfl⟩

def edgeHopRev {x y : P} (h : x ≤ y) : List ((orderCx (NeSpx (cmpRel P))).E × Bool) :=
  hop (spx1_le_spx2_right h) (spx1_le_spx2_left h)

theorem isPath_edgeHopRev {x y : P} (h : x ≤ y) :
    IsPath (orderCx (NeSpx (cmpRel P))).src (orderCx (NeSpx (cmpRel P))).tgt (edgeHopRev h)
      (spx1 y) (spx1 x) :=
  ⟨rfl, rfl, rfl⟩

theorem revPath_edgeHop {x y : P} (h : x ≤ y) : revPath (edgeHop h) = edgeHopRev h := rfl

theorem revPath_edgeHopRev {x y : P} (h : x ≤ y) : revPath (edgeHopRev h) = edgeHop h := rfl

def StarCh (t : P) (σ : NeSpx (cmpRel P)) : Prop := ∀ x ∈ σ.1, x ≤ t

omit [DecidableEq P] in
theorem starCh_spx1 {t x : P} (h : x ≤ t) : StarCh t (spx1 x) := by
  intro a ha; exact Finset.mem_singleton.1 ha ▸ h

theorem htpy_nil_of_star (t : P) {v : NeSpx (cmpRel P)} (hv : StarCh t v)
    {l : List ((orderCx (NeSpx (cmpRel P))).E × Bool)}
    (hp : IsPath (orderCx (NeSpx (cmpRel P))).src (orderCx (NeSpx (cmpRel P))).tgt l v v)
    (hl : PathIn (StarCh t) l) :
    Htpy (orderCx (NeSpx (cmpRel P))) v v l [] := by
  refine htpy_nil_of_pathIn_cone (fun σ => ⟨insert t σ.1.1, ⟨t, Finset.mem_insert_self _ _⟩,
      isSimplex_cmpRel_iff.2 fun a ha b hb => by
        simp only [Finset.mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        exacts [.inl le_rfl, .inr (σ.2 b hb), .inl (σ.2 a ha), isSimplex_cmpRel_iff.1 σ.1.2.2 a ha b hb]⟩)
    ?_ (fun σ => Finset.subset_insert t σ.1.1) (spx1 t) ?_ hv hp hl
  · rintro ⟨σ, _⟩ ⟨τ, _⟩ (h : σ.1 ⊆ τ.1)
    exact Finset.insert_subset_insert _ h
  · rintro ⟨σ, _⟩ a ha
    exact (Finset.mem_singleton.1 ha : a = t) ▸ Finset.mem_insert_self t σ.1

omit [DecidableEq P] in
theorem pathIn_hop {t : P} {a b c : NeSpx (cmpRel P)} (ha : a ≤ c) (hb : b ≤ c)
    (hc : StarCh t c) : PathIn (StarCh t) (hop ha hb) := by
  intro e he
  simp only [hop, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> exact ⟨fun x hx => hc x (by first | exact ha hx | exact hb hx), hc⟩

theorem pathIn_edgeHop {t x y : P} (hxy : x ≤ y) (hx : x ≤ t) (hy : y ≤ t) :
    PathIn (StarCh t) (edgeHop hxy) :=
  pathIn_hop _ _ fun a ha => by
    rcases Finset.mem_insert.1 ha with rfl | ha
    exacts [hx, Finset.mem_singleton.1 ha ▸ hy]

theorem pathIn_edgeHopRev {t x y : P} (hxy : x ≤ y) (hx : x ≤ t) (hy : y ≤ t) :
    PathIn (StarCh t) (edgeHopRev hxy) :=
  pathIn_hop _ _ fun a ha => by
    rcases Finset.mem_insert.1 ha with rfl | ha
    exacts [hx, Finset.mem_singleton.1 ha ▸ hy]

omit [DecidableEq P] in
theorem pathIn_append' {A : NeSpx (cmpRel P) → Prop} {l l' : List ((orderCx (NeSpx (cmpRel P))).E × Bool)}
    (h : PathIn A l) (h' : PathIn A l') : PathIn A (l ++ l') :=
  pathIn_append h h'

theorem exists_greatest_chain {σ : Finset P} (hne : σ.Nonempty)
    (hch : ∀ x ∈ σ, ∀ y ∈ σ, x ≤ y ∨ y ≤ x) : ∃ m, m ∈ σ ∧ ∀ x ∈ σ, x ≤ m := by
  classical
  induction σ using Finset.induction_on with
  | empty => exact absurd hne (by simp)
  | insert a s ha ih =>
      by_cases hs : s.Nonempty
      · obtain ⟨m, hm, hmax⟩ := ih hs fun x hx y hy =>
          hch x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy)
        rcases hch a (Finset.mem_insert_self _ _) m (Finset.mem_insert_of_mem hm) with h | h
        · exact ⟨m, Finset.mem_insert_of_mem hm, fun x hx =>
            (Finset.mem_insert.1 hx).elim (· ▸ h) (hmax x)⟩
        · exact ⟨a, Finset.mem_insert_self _ _, fun x hx =>
            (Finset.mem_insert.1 hx).elim (· ▸ le_rfl) fun hx => (hmax x hx).trans h⟩
      · exact ⟨a, Finset.mem_insert_self _ _, fun x hx =>
          (Finset.mem_insert.1 hx).elim (· ▸ le_rfl) fun hx => (hs ⟨x, hx⟩).elim⟩

noncomputable def chainMax (σ : NeSpx (cmpRel P)) : P :=
  Classical.choose (exists_greatest_chain σ.2.1 (isSimplex_cmpRel_iff.1 σ.2.2))

theorem chainMax_mem (σ : NeSpx (cmpRel P)) : chainMax σ ∈ σ.1 :=
  (Classical.choose_spec (exists_greatest_chain σ.2.1 (isSimplex_cmpRel_iff.1 σ.2.2))).1

theorem le_chainMax (σ : NeSpx (cmpRel P)) {x : P} (hx : x ∈ σ.1) : x ≤ chainMax σ :=
  (Classical.choose_spec (exists_greatest_chain σ.2.1 (isSimplex_cmpRel_iff.1 σ.2.2))).2 x hx

theorem chainMax_monotone : Monotone (chainMax (P := P)) :=
  fun σ τ h => le_chainMax τ (h (chainMax_mem σ))

@[simp] theorem chainMax_spx1 (x : P) : chainMax (spx1 x) = x := by
  simpa using chainMax_mem (spx1 x)

@[simp] theorem chainMax_spx2 {x y : P} (h : x ≤ y) : chainMax (spx2 h) = y := by
  refine le_antisymm ?_ (le_chainMax (spx2 h) (by simp))
  have hmem := chainMax_mem (spx2 h)
  simp only [spx2_val, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hx | hy'
  exacts [(le_of_eq hx).trans h, le_of_eq hy']

noncomputable def nerveAtt {X : Type v} [Preorder X] (g : P →o X) : NeSpx (cmpRel P) →o X :=
  ⟨fun σ => g (chainMax σ), g.monotone.comp chainMax_monotone⟩

@[simp] theorem nerveAtt_spx1 {X : Type v} [Preorder X] (g : P →o X) (x : P) :
    nerveAtt g (spx1 x) = g x := by simp [nerveAtt]

@[simp] theorem nerveAtt_spx2 {X : Type v} [Preorder X] (g : P →o X) {x y : P} (h : x ≤ y) :
    nerveAtt g (spx2 h) = g y := by simp [nerveAtt]

end FiniteChains.Davis
