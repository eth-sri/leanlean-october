import Mathlib.Tactic

import RequestProject.BlockConnected
import RequestProject.OrderCxConeNull

/-!
# The nerve of a partial order: the comparability graph and its flag complex

The nerve of the chamber construction is a *commutation graph* `A : CommRel V`, and the simplices
of the construction are the cliques of that graph — the complex is flag by construction.  The
triangulations of surfaces which are used as nerves in the article are produced here in the only
way which makes flagness automatic: as the **comparability graph of the face poset** of a regular
cell structure.  Its cliques are exactly the nonempty chains of the poset, so the resulting
simplicial complex is the barycentric subdivision of the cell structure.

* `FiniteChains.Davis.cmpRel P` — the comparability graph of a partial order `P`;
* `FiniteChains.Davis.isSimplex_cmpRel_iff` — its simplices are the chains of `P`;
* `FiniteChains.Davis.spx1`, `FiniteChains.Davis.spx2` — the chains with one and with two
  elements, the vertices and the edges of the subdivision;
* `FiniteChains.Davis.hop` — the two-edge path of `orderCx (NeSpx (cmpRel P))` which crosses a
  chain from one face to another;
* `FiniteChains.Davis.chainMax` — the largest element of a nonempty chain, and
  `FiniteChains.Davis.nerveAtt` — the attaching map induced by a monotone labelling of the cells;
* `FiniteChains.Davis.htpy_nil_of_star` — **the filling tool**: a loop all of whose chains
  consist of faces of one fixed cell `t` is null-homotopic.  This is the combinatorial form of
  "a loop inside the closed star of a cell bounds", and it is what fills the polygon of the
  surface, one cell at a time.
-/

namespace FiniteChains.Davis


open RACG Mirror Comb


/-! ### A cancellation rule for homotopies -/

section

variable {X : Complex2.{u}}

/-- Two paths with the same endpoints are homotopic as soon as the loop obtained by following
the first and coming back along the second is null-homotopic. -/
theorem htpy_of_loop_nil {a b : X.V} {p q : List (X.E × Bool)}
    (hp : IsPath X.src X.tgt p a b) (hq : IsPath X.src X.tgt q a b)
    (h : Htpy X a a (p ++ revPath q) []) : Htpy X a b p q := by
  have hrq  := isPath_revPath hq
  have h1 : Htpy X a b (p ++ (revPath q ++ q)) q := by
    have hh := h.congr_append (r := ([] : List (X.E × Bool))) (s := q) rfl hq
    simpa using hh
  have h2  :=
    Htpy.append_congr hp (isPath_append_iff.mpr ⟨a, hrq, hq⟩) (Htpy.refl p)
      (htpy_revPath_append hq)
  have h3 := h2.symm.trans h1
  simpa using h3

variable {a b c : X.V}
/-- Appending a fixed path on the right of a homotopy. -/
abbrev htpy_append_right  {p q r : List (X.E × Bool)}
    (hp : IsPath X.src X.tgt p a b) (hr : IsPath X.src X.tgt r b c) (h : Htpy X a b p q)  :=
  FiniteChains.Comb.Htpy.append_congr hp hr h (FiniteChains.Comb.Htpy.refl r)

/-- Appending a fixed path on the left of a homotopy. -/
abbrev htpy_append_left  {p q r : List (X.E × Bool)}
    (hr : IsPath X.src X.tgt r a b) (hp : IsPath X.src X.tgt p b c) (h : Htpy X b c p q)  :=
  FiniteChains.Comb.Htpy.append_congr hr hp (FiniteChains.Comb.Htpy.refl r) h

end

section

variable {P : Type u} [PartialOrder P] [DecidableEq P]

/-- **The comparability graph of a partial order**: two distinct comparable cells are joined. -/
def cmpRel (P : Type u) [PartialOrder P] : CommRel P where
  rel x y := x ≠ y ∧ (x ≤ y ∨ y ≤ x)
  rel_symm := by
    aesop
  rel_irrefl := by
    rintro a ⟨h, -⟩
    exact h rfl

/-- **The simplices of the comparability graph are the chains.** -/
theorem isSimplex_cmpRel_iff {σ : Finset P} :
    IsSimplex (cmpRel P) σ ↔ ∀ x ∈ σ, ∀ y ∈ σ, x ≤ y ∨ y ≤ x := by
  constructor
  · intro h x hx y hy
    by_cases hxy : x = y
    · exact Or.inl (le_of_eq hxy)
    · exact (h x hx y hy hxy).2
  · intro h x hx y hy hxy
    exact ⟨hxy, h x hx y hy⟩

variable (x : P)
/-- The chain with one element: a vertex of the barycentric subdivision. -/
def spx1  : NeSpx (cmpRel P) :=
  ⟨{x}, ⟨x, Finset.mem_singleton_self x⟩, isSimplex_singleton x⟩

omit [DecidableEq P] in
@[simp] theorem spx1_val  : (spx1 x).1 = {x} := rfl

variable {x y : P}
  (h : x ≤ y)
/-- The chain with (at most) two elements: an edge of the barycentric subdivision. -/
def spx2   : NeSpx (cmpRel P) :=
  ⟨{x, y}, ⟨x, by simp⟩, by
    refine isSimplex_cmpRel_iff.2 ?_
    simp_all⟩

@[simp] theorem spx2_val   : (spx2 h).1 = {x, y} := rfl

theorem spx1_le_spx2_left   : spx1 x ≤ spx2 h := by
  intro a ha
  simp  at ha
  simp [*]

theorem spx1_le_spx2_right   : spx1 y ≤ spx2 h := by
  intro a ha
  simp  at ha
  simp [*]

/-! ### Paths crossing a chain -/

/-- The two-edge path of the order complex of the chains which goes from the face `a` of the
chain `c` up to `c` and down to its face `b`. -/
def hop {a b c : NeSpx (cmpRel P)} (ha : a ≤ c) (hb : b ≤ c)  :=
  [ordPos ha, ordNeg hb]

omit [DecidableEq P] in
theorem isPath_hop {a b c : NeSpx (cmpRel P)} (ha : a ≤ c) (hb : b ≤ c) :
    IsPath (orderCx (NeSpx (cmpRel P))).src (orderCx (NeSpx (cmpRel P))).tgt (hop ha hb) a b :=
  ⟨rfl, rfl, rfl⟩

/-- The two-edge path which crosses the edge `{x, y}` of the subdivision from `x` to `y`. -/
def edgeHop    :=
  hop (spx1_le_spx2_left h) (spx1_le_spx2_right h)

abbrev isPath_edgeHop    :=
  FiniteChains.Davis.isPath_hop (FiniteChains.Davis.spx1_le_spx2_left h) (FiniteChains.Davis.spx1_le_spx2_right h)

/-- The same edge crossed from `y` to `x`. -/
def edgeHopRev    :=
  hop (spx1_le_spx2_right h) (spx1_le_spx2_left h)

abbrev isPath_edgeHopRev    :=
  FiniteChains.Davis.isPath_hop (FiniteChains.Davis.spx1_le_spx2_right h) (FiniteChains.Davis.spx1_le_spx2_left h)

theorem revPath_edgeHop   : revPath (edgeHop h) = edgeHopRev h := rfl



/-! ### The star of a cell -/

variable (t : P)
variable (σ : NeSpx (cmpRel P))
/-- The chains all of whose elements are faces of the cell `t`: the closed star of `t` in the
barycentric subdivision. -/
def StarCh    := ∀ x ∈ σ.1, x ≤ t

omit [DecidableEq P] in
theorem starCh_spx1 {t x : P} (h : x ≤ t) : StarCh t (spx1 x) := by
  simp_all [FiniteChains.Davis.StarCh]

theorem starCh_spx2 {t x y : P} (hxy : x ≤ y) (hx : x ≤ t) (hy : y ≤ t) :
    StarCh t (spx2 hxy) := by
  simp_all [FiniteChains.Davis.StarCh]

/-- The chain obtained by adding the cell `t` to a chain of its star. -/
def insCh   (hσ : StarCh t σ) : NeSpx (cmpRel P) :=
  ⟨insert t σ.1, ⟨t, Finset.mem_insert_self _ _⟩, by
    refine isSimplex_cmpRel_iff.2 ?_
    intro a ha b hb
    simp  at ha hb
    rcases ha with rfl | ha
    · aesop
    · rcases hb with rfl | hb
      · exact Or.inl (hσ a ha)
      · exact isSimplex_cmpRel_iff.1 σ.2.2 a ha b hb⟩



/-- **The filling tool.**  A loop of the subdivision all of whose chains consist of faces of one
fixed cell `t` is null-homotopic: the closed star of a cell is a cone. -/
theorem htpy_nil_of_star  {v : NeSpx (cmpRel P)} (hv : StarCh t v)
    {l : List ((orderCx (NeSpx (cmpRel P))).E × Bool)}
    (hp : IsPath (orderCx (NeSpx (cmpRel P))).src (orderCx (NeSpx (cmpRel P))).tgt l v v)
    (hl : PathIn (StarCh t) l) :
    Htpy (orderCx (NeSpx (cmpRel P))) v v l [] := by
  refine htpy_nil_of_pathIn_cone (fun σ => insCh t σ.1 σ.2) ?_ ?_ (spx1 t) ?_ hv hp hl
  · classical solve_by_elim (transparency := .default) [Finset.insert_subset_insert]
  · rintro ⟨σ, hσ⟩
    exact Finset.subset_insert t σ.1
  · rintro ⟨σ, hσ⟩ a ha
    simp only [spx1_val, Finset.mem_singleton] at ha
    subst ha
    exact Finset.mem_insert_self _ _

omit [DecidableEq P] in
/-- A two-edge path inside the star of `t`. -/
theorem pathIn_hop {t : P} {a b c : NeSpx (cmpRel P)} (ha : a ≤ c) (hb : b ≤ c)
    (hc : StarCh t c) : PathIn (StarCh t) (hop ha hb) := by
  have hA  := fun x hx => hc x (ha hx)
  have hB  := fun x hx => hc x (hb hx)
  intro e he
  simp only [hop, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  exacts [⟨hA, hc⟩, ⟨hB, hc⟩]

/-- The path crossing an edge of the subdivision stays in the star of any cell dominating the
two endpoints. -/
abbrev pathIn_edgeHop {t x y : P} (hxy : x ≤ y) (hx : x ≤ t) (hy : y ≤ t)  :=
  FiniteChains.Davis.pathIn_hop (FiniteChains.Davis.spx1_le_spx2_left hxy) (FiniteChains.Davis.spx1_le_spx2_right hxy)
    (FiniteChains.Davis.starCh_spx2 hxy hx hy)

abbrev pathIn_edgeHopRev {t x y : P} (hxy : x ≤ y) (hx : x ≤ t) (hy : y ≤ t)  :=
  FiniteChains.Davis.pathIn_hop (FiniteChains.Davis.spx1_le_spx2_right hxy) (FiniteChains.Davis.spx1_le_spx2_left hxy)
    (FiniteChains.Davis.starCh_spx2 hxy hx hy)

omit [DecidableEq P] in
theorem pathIn_append' {A : NeSpx (cmpRel P) → Prop} {l l' : List ((orderCx (NeSpx (cmpRel P))).E × Bool)}
    (h : PathIn A l) (h' : PathIn A l') : PathIn A (l ++ l') := by
  grind [FiniteChains.Comb.PathIn]

/-! ### The largest element of a chain -/

theorem exists_greatest_chain {σ : Finset P} (hne : σ.Nonempty)
    (hch : ∀ x ∈ σ, ∀ y ∈ σ, x ≤ y ∨ y ≤ x) : ∃ m, m ∈ σ ∧ ∀ x ∈ σ, x ≤ m := by
  classical
  induction σ using Finset.induction_on with
  | empty => exact absurd hne (by simp)
  | insert a s ha ih =>
      by_cases hs : s.Nonempty
      · grind
      simp_all

variable (σ : NeSpx (cmpRel P))
/-- **The largest cell of a nonempty chain.** -/
noncomputable def chainMax   :=
  Classical.choose (exists_greatest_chain σ.2.1 (isSimplex_cmpRel_iff.1 σ.2.2))

theorem chainMax_mem  : chainMax σ ∈ σ.1 :=
  (Classical.choose_spec (exists_greatest_chain σ.2.1 (isSimplex_cmpRel_iff.1 σ.2.2))).1

theorem le_chainMax  {x : P} (hx : x ∈ σ.1) : x ≤ chainMax σ :=
  (Classical.choose_spec (exists_greatest_chain σ.2.1 (isSimplex_cmpRel_iff.1 σ.2.2))).2 x hx

theorem chainMax_monotone : Monotone (chainMax (P := P)) := by
  intro σ τ h
  exact le_chainMax τ (h (chainMax_mem σ))

@[simp] abbrev chainMax_spx1   :=
  have h := FiniteChains.Davis.chainMax_mem (FiniteChains.Davis.spx1 x);
  Eq.mp Finset.mem_singleton._simp_1 h

@[simp] theorem chainMax_spx2   : chainMax (spx2 h) = y := by
  classical grind [FiniteChains.Davis.chainMax_mem, FiniteChains.Davis.le_chainMax, FiniteChains.Davis.spx2_val, Finset.mem_insert, Finset.mem_singleton, le_antisymm]

variable {X : Type v}
/-- **The attaching map induced by a monotone labelling of the cells.** -/
noncomputable def nerveAtt  [Preorder X] (g : P →o X) : NeSpx (cmpRel P) →o X :=
  ⟨fun σ => g (chainMax σ), g.monotone.comp chainMax_monotone⟩

@[simp] theorem nerveAtt_spx1  [Preorder X] (g : P →o X) (x : P) :
    nerveAtt g (spx1 x) = g x := by simp [nerveAtt]

@[simp] theorem nerveAtt_spx2  [Preorder X] (g : P →o X) {x y : P} (h : x ≤ y) :
    nerveAtt g (spx2 h) = g y := by simp [nerveAtt]

end

end FiniteChains.Davis

