module

public import PottsDiscontinuity.FK.Graph
public import PottsDiscontinuity.TorusCrossing.Lattice

/-!
# Graphs given by their edge-end maps

Both the primal board graph and the dual board graph are of the form: vertex set `P`
(a finite set of cells) and one edge `ends m` for each medial vertex `m` of a finite set `M`.
This file builds the corresponding simple graph, the bijection between `M` and its edge set,
the translation between `FK.Configuration` and finite sets of medial vertices, and relates
actual connectivity to a cell-level reflexive-transitive closure.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity

section EndGraph

variable (ends : Cell → Cell × Cell) (P M : Finset Cell)

/-- The graph on `P` with an edge `ends m` for each `m ∈ M`. -/
def endGraph : SimpleGraph P :=
  SimpleGraph.fromRel (fun c d => ∃ m ∈ M, ends m = (c.1, d.1))

variable {ends P M}

theorem endGraph_adj (c d : P) :
    (endGraph ends P M).Adj c d ↔
      c ≠ d ∧ ((∃ m ∈ M, ends m = (c.1, d.1)) ∨ (∃ m ∈ M, ends m = (d.1, c.1))) := by
  unfold endGraph; rw [SimpleGraph.fromRel_adj]

/-- Structural hypotheses making `m ↦ ends m` an honest edge indexing. -/
structure EndData (ends : Cell → Cell × Cell) (P M : Finset Cell) : Prop where
  mem : ∀ m ∈ M, (ends m).1 ∈ P ∧ (ends m).2 ∈ P
  ne : ∀ m, (ends m).1 ≠ (ends m).2
  inj : ∀ m m', ends m = ends m' ∨ ends m = (ends m').swap → m = m'

variable (hD : EndData ends P M)
include hD

/-- The edge of `endGraph` carried by a medial vertex. -/
def endEdge (m : M) : (endGraph ends P M).edgeSet :=
  ⟨s((⟨(ends m.1).1, (hD.mem m.1 m.2).1⟩ : P), (⟨(ends m.1).2, (hD.mem m.1 m.2).2⟩ : P)), by
    rw [SimpleGraph.mem_edgeSet, endGraph_adj]
    refine ⟨fun h => hD.ne m.1 (congrArg Subtype.val h), Or.inl ⟨m.1, m.2, rfl⟩⟩⟩

theorem endEdge_injective : Function.Injective (endEdge hD) := fun m m' h => by
  have h' := congrArg Subtype.val h
  simp only [endEdge, Sym2.eq_iff] at h'
  exact Subtype.ext (hD.inj m.1 m'.1 (h'.imp
    (fun ⟨h1, h2⟩ => Prod.ext (congrArg Subtype.val h1) (congrArg Subtype.val h2))
    (fun ⟨h1, h2⟩ => Prod.ext (congrArg Subtype.val h1) (congrArg Subtype.val h2))))

theorem endEdge_surjective : Function.Surjective (endEdge hD) := by
  rintro ⟨e, he⟩
  induction e using Sym2.ind with
  | _ c d =>
    rw [SimpleGraph.mem_edgeSet, endGraph_adj] at he
    rcases he.2 with ⟨m, hm, h⟩ | ⟨m, hm, h⟩ <;> refine ⟨⟨m, hm⟩, Subtype.ext ?_⟩ <;>
      simp only [endEdge, Sym2.eq_iff] <;>
      [exact Or.inl ⟨Subtype.ext (congrArg Prod.fst h), Subtype.ext (congrArg Prod.snd h)⟩;
       exact Or.inr ⟨Subtype.ext (congrArg Prod.fst h), Subtype.ext (congrArg Prod.snd h)⟩]

noncomputable def endEdgeEquiv : M ≃ (endGraph ends P M).edgeSet :=
  Equiv.ofBijective (endEdge hD) ⟨endEdge_injective hD, endEdge_surjective hD⟩

noncomputable def cfgOf (A : Finset Cell) : FK.Configuration (endGraph ends P M) :=
  (A.subtype (· ∈ M)).map (endEdgeEquiv hD).toEmbedding

noncomputable def openMedials (C : FK.Configuration (endGraph ends P M)) : Finset Cell :=
  (C.map (endEdgeEquiv hD).symm.toEmbedding).map ⟨Subtype.val, Subtype.val_injective⟩

theorem mem_openMedials (C : FK.Configuration (endGraph ends P M)) (m : Cell) :
    m ∈ openMedials hD C ↔ ∃ hm : m ∈ M, endEdgeEquiv hD ⟨m, hm⟩ ∈ C := by
  unfold openMedials
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
  exact ⟨by rintro ⟨x, ⟨e, he, rfl⟩, rfl⟩; exact ⟨((endEdgeEquiv hD).symm e).2, by simpa using he⟩,
    fun ⟨hm, h⟩ => ⟨_, ⟨_, h, rfl⟩, by simp⟩⟩

theorem openMedials_subset (C : FK.Configuration (endGraph ends P M)) :
    openMedials hD C ⊆ M := fun m hm => ((mem_openMedials hD C m).1 hm).1

theorem mem_cfgOf (A : Finset Cell) (m : M) :
    endEdgeEquiv hD m ∈ cfgOf hD A ↔ m.1 ∈ A := by
  unfold cfgOf; simp

theorem openMedials_cfgOf (A : Finset Cell) (hA : A ⊆ M) : openMedials hD (cfgOf hD A) = A := by
  ext m
  rw [mem_openMedials]
  exact ⟨fun ⟨hm, h⟩ => (mem_cfgOf hD A ⟨m, hm⟩).1 h,
    fun h => ⟨hA h, (mem_cfgOf hD A ⟨m, hA h⟩).2 h⟩⟩

theorem cfgOf_openMedials (C : FK.Configuration (endGraph ends P M)) :
    cfgOf hD (openMedials hD C) = C := by
  ext e
  obtain ⟨m, rfl⟩ := (endEdgeEquiv hD).surjective e
  rw [mem_cfgOf, mem_openMedials]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨m.2, h⟩⟩

theorem card_cfgOf (A : Finset Cell) (hA : A ⊆ M) : (cfgOf hD A).card = A.card := by
  have := congrArg Finset.card (openMedials_cfgOf hD A hA)
  rw [← this]; unfold openMedials; simp

def StepRel (ends : Cell → Cell × Cell) (A : Finset Cell) (x y : Cell) : Prop :=
  ∃ m ∈ A, ends m = (x, y) ∨ ends m = (y, x)

theorem endEdgeEquiv_val (m : M) :
    ((endEdgeEquiv hD m : (endGraph ends P M).edgeSet) : Sym2 P) =
      s((⟨(ends m.1).1, (hD.mem m.1 m.2).1⟩ : P), (⟨(ends m.1).2, (hD.mem m.1 m.2).2⟩ : P)) := rfl

theorem openGraph_adj_iff (C : FK.Configuration (endGraph ends P M)) (c d : P) :
    (FK.openGraph (endGraph ends P M) C).Adj c d ↔ StepRel ends (openMedials hD C) c.1 d.1 := by
  rw [FK.openGraph_adj, FK.openEdges]
  refine ⟨?_, ?_⟩
  · rintro ⟨e, he, heq⟩
    obtain ⟨m, rfl⟩ := (endEdgeEquiv hD).surjective e
    rw [endEdgeEquiv_val, Sym2.eq_iff] at heq
    exact ⟨m.1, (mem_openMedials hD C _).2 ⟨m.2, he⟩, heq.imp
      (fun ⟨h1, h2⟩ => Prod.ext (congrArg Subtype.val h1) (congrArg Subtype.val h2))
      (fun ⟨h1, h2⟩ => Prod.ext (congrArg Subtype.val h1) (congrArg Subtype.val h2))⟩
  · rintro ⟨m, hm, h⟩
    obtain ⟨hmM, hmC⟩ := (mem_openMedials hD C m).1 hm
    refine ⟨endEdgeEquiv hD ⟨m, hmM⟩, hmC, ?_⟩
    rw [endEdgeEquiv_val, Sym2.eq_iff]
    exact h.imp
      (fun h => ⟨Subtype.ext (congrArg Prod.fst h), Subtype.ext (congrArg Prod.snd h)⟩)
      (fun h => ⟨Subtype.ext (congrArg Prod.fst h), Subtype.ext (congrArg Prod.snd h)⟩)

omit hD in
theorem stepRel_symm {A : Finset Cell} {x y : Cell} (h : StepRel ends A x y) : StepRel ends A y x := by
  obtain ⟨m, hm, h⟩ := h; exact ⟨m, hm, h.symm⟩

theorem actualConnected_iff (C : FK.Configuration (endGraph ends P M)) (c d : P) :
    FK.ActualConnected (endGraph ends P M) C c d ↔
      Relation.ReflTransGen (StepRel ends (openMedials hD C)) c.1 d.1 := by
  unfold FK.ActualConnected
  rw [SimpleGraph.reachable_iff_reflTransGen]
  refine ⟨Relation.ReflTransGen.lift Subtype.val (fun a b => (openGraph_adj_iff hD C a b).1) c d,
    fun h => ?_⟩
  have key : ∀ y : Cell, Relation.ReflTransGen (StepRel ends (openMedials hD C)) c.1 y →
      ∃ y' : P, y'.1 = y ∧ Relation.ReflTransGen (FK.openGraph (endGraph ends P M) C).Adj c y' := by
    intro y hy
    induction hy with
    | refl => exact ⟨c, rfl, Relation.ReflTransGen.refl⟩
    | @tail b z _ hstep ih =>
      obtain ⟨y', rfl, hy'⟩ := ih
      obtain ⟨m, hm, hmz⟩ := hstep
      have hmM := openMedials_subset hD C hm
      have hz : z ∈ P := by
        rcases hmz with hmz | hmz
        · simpa [hmz] using (hD.mem m hmM).2
        · simpa [hmz] using (hD.mem m hmM).1
      exact ⟨⟨z, hz⟩, rfl, hy'.tail ((openGraph_adj_iff hD C y' ⟨z, hz⟩).2 ⟨m, hm, hmz⟩)⟩
  obtain ⟨y', hy', hr⟩ := key d.1 h
  rwa [Subtype.ext hy'] at hr

def otherEnd (ends : Cell → Cell × Cell) (z m : Cell) : Cell :=
  if (ends m).1 = z then (ends m).2 else (ends m).1

omit hD in
theorem ends_eq_of_mem {m z : Cell} (hne : (ends m).1 ≠ (ends m).2) (hz : z = (ends m).1 ∨ z = (ends m).2) :
    ends m = (z, otherEnd ends z m) ∨ ends m = (otherEnd ends z m, z) := by
  unfold otherEnd
  rcases hz with hz | hz
  · exact Or.inl (by simp only [hz.symm, ite_true]; exact Prod.ext hz.symm rfl)
  · exact Or.inr (by simp only [show ¬ (ends m).1 = z from fun e => hne (e.trans hz), ite_false]; exact Prod.ext rfl hz.symm)

omit hD in
theorem otherEnd_ne {m z : Cell} (hne : (ends m).1 ≠ (ends m).2) (hz : z = (ends m).1 ∨ z = (ends m).2) :
    otherEnd ends z m ≠ z := fun e => by
  rcases ends_eq_of_mem hne hz with h | h <;>
    exact hne (by rw [congrArg Prod.fst h, congrArg Prod.snd h, e])

theorem degree_eq [DecidableEq Cell] (z : P) [DecidableRel (endGraph ends P M).Adj] :
    (endGraph ends P M).degree z =
      (M.filter (fun m => z.1 = (ends m).1 ∨ z.1 = (ends m).2)).card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hmem (m : Cell) (hm : m ∈ M) : otherEnd ends z.1 m ∈ P := by
    unfold otherEnd; split_ifs <;> [exact (hD.mem m hm).2; exact (hD.mem m hm).1]
  refine (Finset.card_bij
    (fun m hm => (⟨otherEnd ends z.1 m, hmem m (Finset.mem_filter.1 hm).1⟩ : P))
    (fun m hm => ?_) (fun m hm m' hm' h => ?_) (fun d hd => ?_)).symm
  · obtain ⟨hmM, hz⟩ := Finset.mem_filter.1 hm
    rw [SimpleGraph.mem_neighborFinset, endGraph_adj]
    exact ⟨fun h => otherEnd_ne (hD.ne m) hz (congrArg Subtype.val h).symm,
      (ends_eq_of_mem (hD.ne m) hz).imp (fun h => ⟨m, hmM, h⟩) (fun h => ⟨m, hmM, h⟩)⟩
  · have h' : otherEnd ends z.1 m = otherEnd ends z.1 m' := congrArg Subtype.val h
    apply hD.inj
    rcases ends_eq_of_mem (hD.ne m) (Finset.mem_filter.1 hm).2 with e | e <;>
      rcases ends_eq_of_mem (hD.ne m') (Finset.mem_filter.1 hm').2 with e' | e'
    · left; rw [e, e', h']
    · right; rw [e, e', h']; rfl
    · right; rw [e, e', h']; rfl
    · left; rw [e, e', h']
  · rw [SimpleGraph.mem_neighborFinset, endGraph_adj] at hd
    rcases hd.2 with ⟨m, hm, h⟩ | ⟨m, hm, h⟩
    · have hz : z.1 = (ends m).1 := (congrArg Prod.fst h).symm
      exact ⟨m, Finset.mem_filter.2 ⟨hm, Or.inl hz⟩,
        Subtype.ext (by unfold otherEnd; simp only [← hz, ite_true]; exact congrArg Prod.snd h)⟩
    · have hz : z.1 = (ends m).2 := (congrArg Prod.snd h).symm
      have hne : ¬ (ends m).1 = z.1 := fun e => hd.1 (Subtype.ext (e.symm.trans (congrArg Prod.fst h)))
      exact ⟨m, Finset.mem_filter.2 ⟨hm, Or.inr hz⟩,
        Subtype.ext (by unfold otherEnd; simp only [hne, ite_false]; exact congrArg Prod.fst h)⟩

end EndGraph

end PottsDiscontinuity.TorusCrossing
