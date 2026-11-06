module

public import Chazelle.Core.OracleBridge

/-!
# Lemma 3.6 (WP-H), part 7: the graph of the preprocessing

The preprocessing builds a two-page book map (`OracleBook.BookData`) on the spine of the arcs of
the normal form (spine position `p < A` is the arc `seq[p]`; positions `A ≤ p < N` are padding),
with
* inner chords from the first arc of each region to its other arcs (`StarOK`, complete:
  `StarComplete`);
* outer chords between arcs meeting at a point of the chain (`ZipOK`, complete: `ZipComplete`).

This file proves that such data is a valid book (hence planar, `OracleBook.BookData.planar`), and
that its graph satisfies the hypotheses of the node-level cluster argument
(`OracleQ.cluster_query_nodes`): the nodes of a region are connected inside the region, and
regions facing each other across the chain have adjacent nodes.  The main result,
`book_query_firstHit`, is the correctness of the query of Lemma 3.6 for this graph.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (sideInArc sidePt regionsIn)
open Chazelle.Visibility (rayPt)
open OracleBook

namespace OracleQ

/-! ## The graph of a book -/

/-- A dart of the book goes from `u` to `v`. -/
def BookAdj (B : BookData) (u v : ℕ) : Prop :=
  ∃ d, d < 2 * B.E ∧ View.tail B.N (B.view d) = u ∧ View.head B.N (B.view d) = v

/-- **The graph of the book map** on its spine vertices. -/
def bookGraph (B : BookData) : SimpleGraph (Fin B.N) where
  Adj u v := u ≠ v ∧ (BookAdj B u v ∨ BookAdj B v u)
  symm := ⟨by
    rintro u v ⟨hne, h⟩
    exact ⟨hne.symm, h.symm⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

/-- Spine-adjacent positions (the pair `u < v` is a spine edge). -/
def SpineAdj (N u v : ℕ) : Prop := v = u + 1 ∨ (u = 0 ∧ v + 1 = N)

theorem bookAdj_view {B : BookData} {v : View} (hv : B.ViewOK v) :
    BookAdj B (View.tail B.N v) (View.head B.N v) := by
  obtain ⟨d, hd, hdv⟩ := BookData.exists_view hv
  exact ⟨d, hd, by rw [hdv], by rw [hdv]⟩

theorem bookAdj_spineAdj {B : BookData} {u v : ℕ} (huv : u < v) (hv : v < B.N)
    (h : SpineAdj B.N u v) : BookAdj B u v ∨ BookAdj B v u := by
  rcases h with rfl | ⟨rfl, hN⟩
  · left
    have := bookAdj_view (B := B) (v := .spF u) (by show u < B.N; omega)
    simp only [View.tail, View.head] at this
    rwa [Nat.mod_eq_of_lt hv] at this
  · right
    have := bookAdj_view (B := B) (v := .spF v) (by show v < B.N; omega)
    simp only [View.tail, View.head] at this
    rwa [show v + 1 = B.N by omega, Nat.mod_self] at this

theorem bookGraph_adj_of_mem {B : BookData} {c : ℕ × ℕ} (hc : c ∈ B.I ∨ c ∈ B.O)
    (h12 : c.1 < c.2) (h2 : c.2 < B.N) :
    (bookGraph B).Adj ⟨c.1, by omega⟩ ⟨c.2, h2⟩ := by
  refine ⟨fun h => by simp [Fin.ext_iff] at h; omega, Or.inl ?_⟩
  rcases hc with hc | hc
  · exact bookAdj_view (B := B) (v := .inP c) hc
  · exact bookAdj_view (B := B) (v := .outP c) hc

theorem bookGraph_adj_of_spine {B : BookData} {u v : ℕ} (huv : u < v) (hv : v < B.N)
    (h : SpineAdj B.N u v) : (bookGraph B).Adj ⟨u, by omega⟩ ⟨v, hv⟩ :=
  ⟨fun h => by simp [Fin.ext_iff] at h; omega, bookAdj_spineAdj huv hv h⟩

/-- A reflexive-transitive closure of a symmetric relation is symmetric. -/
theorem rtg_symm {α : Type*} {r : α → α → Prop} (hr : ∀ a b, r a b → r b a) {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact (Relation.ReflTransGen.single (hr _ _ hbc)).trans ih

/-! ## The book data of a normal form -/

variable (C : Chain) (Q : Polygon) (N : NF)

/-- **Completeness of the inner page**: every arc is joined to the first arc of its region (by a
star chord or a spine edge). -/
def StarComplete (B : BookData) : Prop :=
  ∀ p, p < N.arcs.length → ∃ m, m < N.arcs.length ∧ rgi N m = rgi N p ∧
    (∀ q, q < N.arcs.length → rgi N q = rgi N p → m ≤ q) ∧
    (m = p ∨ (m, p) ∈ B.I ∨ SpineAdj B.N m p)

/-- **Completeness of the outer page**: arcs meeting at a point of the chain are joined (by a
zipper chord or a spine edge). -/
def ZipComplete (B : BookData) : Prop :=
  ∀ p q, p < q → q < N.arcs.length → ZipRel C Q N p q → (p, q) ∈ B.O ∨ SpineAdj B.N p q

/-- **The requirements on the book data built by the preprocessing.** -/
structure GraphOK (B : BookData) : Prop where
  three_le : 3 ≤ B.N
  arcs_le : N.arcs.length ≤ B.N
  I_nodup : B.I.Nodup
  O_nodup : B.O.Nodup
  I_ok : ∀ c ∈ B.I, ChordOK B.N c
  O_ok : ∀ c ∈ B.O, ChordOK B.N c
  I_star : ∀ c ∈ B.I, StarOK N c
  O_zip : ∀ c ∈ B.O, ZipOK C Q N c
  I_complete : StarComplete N B
  O_complete : ZipComplete C Q N B

variable {C Q N}

/-- **The book data of the preprocessing is valid**, hence planar. -/
theorem valid_of_graphOK (hP : C.P.Simple) (hN : IsNF (chainModel C) Q N)
    (hne : (N.F (chainModel C) Q).Nonempty) {B : BookData} (hB : GraphOK C Q N B) : B.Valid :=
  ⟨hB.three_le, hB.I_nodup, hB.O_nodup, hB.I_ok, hB.O_ok,
    stars_nonCross hN (Or.inl ⟨C, hP, rfl⟩) hne hB.I_star, zips_nonCross C hP hN hne hB.O_zip⟩

/-- The region of a node: the region of its arc, or `∅` for padding. -/
noncomputable def rgNode (reg : ℕ → Set Point) (N : NF) (B : BookData) (v : Fin B.N) :
    Set Point :=
  if v.1 < N.arcs.length then reg (rgi N v.1) else ∅

/-- **The nodes of a region are connected inside the region.** -/
theorem conn_of_graphOK (hN : IsNF (chainModel C) Q N) {reg : ℕ → Set Point}
    (hR : RegionCorr (chainModel C) Q N reg) (hA : ArcsOK (chainModel C) Q N reg)
    {B : BookData} (hB : GraphOK C Q N B) (a b : Fin B.N)
    (hab : rgNode reg N B a = rgNode reg N B b) :
    Relation.ReflTransGen (fun u v => (bookGraph B).Adj u v ∧ rgNode reg N B u = rgNode reg N B a ∧
      rgNode reg N B v = rgNode reg N B a) a b := by
  set A := N.arcs.length
  have hnemp : ∀ p, p < A → reg (rgi N p) ≠ ∅ := by
    intro p hp h
    have hU : reg (rgi N p) ∈ (chainModel C).regions (N.F (chainModel C) Q) :=
      hR.1 _ (hA.1 _ (NFLoc.seq_lt hN hp)).1
    have hne' : (reg (rgi N p)).Nonempty := Chazelle.Chain.regionsIn_nonempty (D := (chainModel C).D) hU
    rw [h] at hne'
    exact Set.not_nonempty_empty hne'
  by_cases ha : a.1 < A <;> by_cases hb : b.1 < A
  · -- both arcs: through the first arc of the region
    have hr : rgi N a.1 = rgi N b.1 := by
      have h' : reg (rgi N a.1) = reg (rgi N b.1) := by
        unfold rgNode at hab; rwa [BookData.ite_t ha, BookData.ite_t hb] at hab
      exact hR.2.1 _ _ (hA.1 _ (NFLoc.seq_lt hN ha)).1 (hA.1 _ (NFLoc.seq_lt hN hb)).1 h'
    obtain ⟨m, hm, hmr, hmin, hlink⟩ := hB.I_complete a.1 ha
    obtain ⟨m', hm', hm'r, hmin', hlink'⟩ := hB.I_complete b.1 hb
    have hmm : m = m' := le_antisymm (hmin m' hm' (hm'r.trans hr.symm))
      (hmin' m hm (hmr.trans hr))
    subst hmm
    have hmN : m < B.N := lt_of_lt_of_le hm hB.arcs_le
    let mv : Fin B.N := ⟨m, hmN⟩
    have hrg : ∀ v : Fin B.N, v.1 < A → rgi N v.1 = rgi N a.1 →
        rgNode reg N B v = rgNode reg N B a := by
      intro v hv h
      unfold rgNode; rw [BookData.ite_t hv, BookData.ite_t ha, h]
    have hmv : rgNode reg N B mv = rgNode reg N B a := hrg mv hm hmr
    -- a node of the region is joined to `mv` by one edge (or equals it)
    have link : ∀ v : Fin B.N, v.1 < A → rgi N v.1 = rgi N a.1 →
        (m = v.1 ∨ (m, v.1) ∈ B.I ∨ SpineAdj B.N m v.1) → m ≤ v.1 →
        mv = v ∨ ((bookGraph B).Adj mv v ∧ rgNode reg N B mv = rgNode reg N B a ∧
          rgNode reg N B v = rgNode reg N B a) := by
      intro v hv hvr hl hle
      rcases hl with h | h | h
      · left; exact Fin.ext h
      · right
        have hc := hB.I_star _ h
        refine ⟨?_, hmv, hrg v hv hvr⟩
        exact bookGraph_adj_of_mem (c := (m, v.1)) (Or.inl h) hc.1 v.2
      · right
        have h3 := hB.three_le
        have hlt : m < v.1 := by rcases h with h | h <;> omega
        exact ⟨bookGraph_adj_of_spine hlt v.2 h, hmv, hrg v hv hvr⟩
    have la := link a ha rfl hlink (hmin a.1 ha rfl)
    have lb := link b hb hr.symm hlink' (hmin' b.1 hb rfl)
    have hsym : ∀ u v, (bookGraph B).Adj u v ∧ rgNode reg N B u = rgNode reg N B a ∧
        rgNode reg N B v = rgNode reg N B a → (bookGraph B).Adj v u ∧
        rgNode reg N B v = rgNode reg N B a ∧ rgNode reg N B u = rgNode reg N B a :=
      fun u v ⟨h1, h2, h3⟩ => ⟨h1.symm, h3, h2⟩
    have p1 : Relation.ReflTransGen (fun u v => (bookGraph B).Adj u v ∧ rgNode reg N B u = rgNode reg N B a ∧
        rgNode reg N B v = rgNode reg N B a) a mv := by
      rcases la with e | e
      · rw [e]
      · exact Relation.ReflTransGen.single (hsym _ _ e)
    have p2 : Relation.ReflTransGen (fun u v => (bookGraph B).Adj u v ∧ rgNode reg N B u = rgNode reg N B a ∧
        rgNode reg N B v = rgNode reg N B a) mv b := by
      rcases lb with e | e
      · rw [e]
      · exact Relation.ReflTransGen.single e
    exact p1.trans p2
  · exfalso
    unfold rgNode at hab
    rw [BookData.ite_t ha, BookData.ite_f hb] at hab
    exact hnemp _ ha hab
  · exfalso
    unfold rgNode at hab
    rw [BookData.ite_f ha, BookData.ite_t hb] at hab
    exact hnemp _ hb hab.symm
  · -- both padding: along the spine
    have hpad : ∀ v : Fin B.N, ¬ v.1 < A → rgNode reg N B v = rgNode reg N B a := by
      intro v hv; unfold rgNode; rw [BookData.ite_f hv, BookData.ite_f ha]
    have step : ∀ k, ∀ u : Fin B.N, ¬ u.1 < A → ∀ v : Fin B.N, v.1 = u.1 + k →
        Relation.ReflTransGen (fun u v => (bookGraph B).Adj u v ∧
          rgNode reg N B u = rgNode reg N B a ∧ rgNode reg N B v = rgNode reg N B a) u v := by
      intro k
      induction k with
      | zero => intro u _ v hv; rw [Fin.ext (show v.1 = u.1 by omega)]
      | succ k ih =>
        intro u hu v hv
        have hwN : u.1 + k < B.N := by omega
        let w : Fin B.N := ⟨u.1 + k, hwN⟩
        refine (ih u hu w rfl).tail ⟨?_, hpad w (by show ¬ u.1 + k < A; omega),
          hpad v (by omega)⟩
        have hv' : v.1 = w.1 + 1 := by show v.1 = u.1 + k + 1; omega
        have := bookGraph_adj_of_spine (B := B) (u := w.1) (v := v.1) (by omega) v.2 (Or.inl hv')
        exact this
    rcases le_total a.1 b.1 with hle | hle
    · exact step (b.1 - a.1) a ha b (by omega)
    · have := step (a.1 - b.1) b hb a (by omega)
      exact rtg_symm (fun u v ⟨h1, h2, h3⟩ => ⟨h1.symm, h3, h2⟩) this

/-- **Regions facing each other across the chain have adjacent nodes.** -/
theorem cross_of_graphOK (hP : C.P.Simple) (hN : IsNF (chainModel C) Q N) {reg : ℕ → Set Point}
    (hR : RegionCorr (chainModel C) Q N reg) (hA : ArcsOK (chainModel C) Q N reg)
    {B : BookData} (hB : GraphOK C Q N B) (U V : Set Point)
    (hU : U ∈ (chainModel C).regions (N.F (chainModel C) Q))
    (hV : V ∈ (chainModel C).regions (N.F (chainModel C) Q)) (hUV : U ≠ V)
    (hcr : CrossAdj C U V) :
    ∃ a b : Fin B.N, rgNode reg N B a = U ∧ rgNode reg N B b = V ∧ (bookGraph B).Adj a b := by
  obtain ⟨p, q, hp, hq, hpU, hqV, hz⟩ := cross_zip C hP hN hR hA hU hV hUV hcr
  have hpN : p < B.N := lt_of_lt_of_le hp hB.arcs_le
  have hqN : q < B.N := lt_of_lt_of_le hq hB.arcs_le
  refine ⟨⟨p, hpN⟩, ⟨q, hqN⟩, by unfold rgNode; rwa [BookData.ite_t hp],
    by unfold rgNode; rwa [BookData.ite_t hq], ?_⟩
  have hpq : p ≠ q := fun h => hUV (by rw [← hpU, ← hqV, h])
  rcases lt_or_gt_of_ne hpq with hlt | hlt
  · rcases hB.O_complete p q hlt hq hz with h | h
    · exact bookGraph_adj_of_mem (c := (p, q)) (Or.inr h) hlt hqN
    · exact bookGraph_adj_of_spine hlt hqN h
  · have hz' := hz.symm
    have : (bookGraph B).Adj ⟨q, hqN⟩ ⟨p, hpN⟩ := by
      rcases hB.O_complete q p hlt hp hz' with h | h
      · exact bookGraph_adj_of_mem (c := (q, p)) (Or.inr h) hlt hpN
      · exact bookGraph_adj_of_spine hlt hpN h
    exact this.symm

/-! ## The map in memory -/

/-! ## From the arcs to the scanned edges -/

end OracleQ

end

end Chazelle.Core
