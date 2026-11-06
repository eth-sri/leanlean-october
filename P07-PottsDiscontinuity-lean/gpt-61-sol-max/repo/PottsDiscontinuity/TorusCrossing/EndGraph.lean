module
public import Mathlib

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

section

variable (ends : Cell → Cell × Cell) (P M : Finset Cell)

/-- The graph on `P` with an edge `ends m` for each `m ∈ M`. -/
def endGraph : SimpleGraph P :=
  SimpleGraph.fromRel  fun c d => ∃ m ∈ M, ends m = (c.1, d.1) 

variable {ends P M}

theorem endGraph_adj (c d : P) :
    (endGraph ends P M).Adj c d ↔
      c ≠ d ∧ ((∃ m ∈ M, ends m = (c.1, d.1)) ∨  ∃ m ∈ M, ends m = (d.1, c.1) ) := by
                                                                                     rfl

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

theorem endEdge_injective : Function.Injective (endEdge hD) := by
  intro m m' h
  apply Subtype.ext
  have h' := congrArg Subtype.val h
  simp only [endEdge, Sym2.eq_iff] at h'
  apply hD.inj
  grind

theorem endEdge_surjective : Function.Surjective (endEdge hD) := by
  rintro ⟨e, he⟩
  induction e using Sym2.ind with
  | _ c d =>
    
    rcases he.2 with ⟨m, hm, h⟩ | ⟨m, hm, h⟩
    · refine ⟨⟨m, hm⟩, Subtype.ext ?_⟩
      simp only [endEdge, Sym2.eq_iff]
      simp_all
    · refine ⟨⟨m, hm⟩, Subtype.ext ?_⟩
      simp only [endEdge, Sym2.eq_iff]
      simp_all

/-- Medial vertices are in bijection with the edges of the graph. -/
noncomputable def endEdgeEquiv  :=
  Equiv.ofBijective (endEdge hD) ⟨endEdge_injective hD, endEdge_surjective hD⟩

/-- A finite set of medial vertices, read as an FK configuration (elements outside `M`
are ignored). -/
noncomputable def cfgOf (A : Finset Cell) : FK.Configuration (endGraph ends P M) :=
  (A.subtype (· ∈ M)).map (endEdgeEquiv hD).toEmbedding

/-- The medial vertices carrying the open edges of an FK configuration. -/
noncomputable def openMedials (C : FK.Configuration (endGraph ends P M))  :=
  (C.map (endEdgeEquiv hD).symm.toEmbedding).map ⟨Subtype.val, Subtype.val_injective⟩

section

variable (C : FK.Configuration (endGraph ends P M))


theorem mem_openMedials  (m : Cell) :
    m ∈ openMedials hD C ↔ ∃ hm : m ∈ M, endEdgeEquiv hD ⟨m, hm⟩ ∈ C := by
  unfold openMedials
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
  grind

theorem openMedials_subset  :
    openMedials hD C ⊆ M := fun m hm => ((mem_openMedials hD C m).1 hm).1

end

theorem mem_cfgOf (A : Finset Cell) (m : M) :
    endEdgeEquiv hD m ∈ cfgOf hD A ↔ m.1 ∈ A := by
  unfold cfgOf
  simp

theorem openMedials_cfgOf (A : Finset Cell) (hA : A ⊆ M) : openMedials hD (cfgOf hD A) = A := by
  grind [mem_openMedials, mem_cfgOf]

theorem cfgOf_openMedials (C : FK.Configuration (endGraph ends P M)) :
    cfgOf hD (openMedials hD C) = C := by
  ext e
  obtain ⟨m, rfl⟩ := (endEdgeEquiv hD).surjective e
  rw [mem_cfgOf, mem_openMedials]
  simp_all

theorem card_cfgOf (A : Finset Cell) (hA : A ⊆ M) : (cfgOf hD A).card = A.card := by
  grind [openMedials, openMedials_cfgOf]

/-- One step of open connectivity at the level of cells. -/
def StepRel (ends : Cell → Cell × Cell) (A : Finset Cell) (x y : Cell)  :=
  ∃ m ∈ A, ends m = (x, y) ∨ ends m = (y, x)

theorem endEdgeEquiv_val (m : M) :
    ((endEdgeEquiv hD m : (endGraph ends P M).edgeSet) : Sym2 P) =
      s((⟨(ends m.1).1, (hD.mem m.1 m.2).1⟩ : P), (⟨(ends m.1).2, (hD.mem m.1 m.2).2⟩ : P)) := rfl

theorem openGraph_adj_iff (C : FK.Configuration (endGraph ends P M)) (c d : P) :
    (FK.openGraph (endGraph ends P M) C).Adj c d ↔ StepRel ends (openMedials hD C) c.1 d.1 := by
  rw [FK.openGraph_adj, FK.openEdges]
  constructor
  · rintro ⟨e, he, heq⟩
    obtain ⟨m, rfl⟩ := (endEdgeEquiv hD).surjective e
    refine ⟨m.1, (mem_openMedials hD C _).2 ⟨m.2, he⟩, ?_⟩
    rw [endEdgeEquiv_val, Sym2.eq_iff] at heq
    grind
  · rintro ⟨m, hm, h⟩
    obtain ⟨hmM, hmC⟩ := (mem_openMedials hD C m).1 hm
    refine ⟨endEdgeEquiv hD ⟨m, hmM⟩, hmC, ?_⟩
    rw [endEdgeEquiv_val, Sym2.eq_iff]
    aesop

omit hD in
theorem stepRel_symm {A : Finset Cell} {x y : Cell} (h : StepRel ends A x y) : StepRel ends A y x := by
  grind +locals

/-- Actual open connectivity equals reflexive-transitive closure of cell-level steps. -/
theorem actualConnected_iff (C : FK.Configuration (endGraph ends P M)) (c d : P) :
    FK.ActualConnected (endGraph ends P M) C c d ↔
      Relation.ReflTransGen (StepRel ends (openMedials hD C)) c.1 d.1 := by
  unfold FK.ActualConnected
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    exact (Relation.ReflTransGen.lift Subtype.val  fun a b hab => (openGraph_adj_iff hD C a b).1 hab ) _ _ h
  · 
    have key : ∀ y , Relation.ReflTransGen (StepRel ends (openMedials hD C)) c.1 y →
        ∃ y' : P, y'.1 = y ∧ Relation.ReflTransGen (FK.openGraph (endGraph ends P M) C).Adj c y' := by
      intro y hy
      induction hy with
      | refl => exact ⟨c, rfl, Relation.ReflTransGen.refl⟩
      | @tail b z _ hstep ih =>
        obtain ⟨y', rfl, hy'⟩ := ih
        obtain ⟨m, hm, hmz⟩ := hstep
        have hmM := openMedials_subset hD C hm
        
        refine ⟨⟨z,  by
                       rcases hmz with hmz | hmz
                       · have := (hD.mem m hmM).2; rwa [hmz] at this
                       · have := (hD.mem m hmM).1; rwa [hmz] at this ⟩, rfl, hy'.tail ?_⟩
        rw [openGraph_adj_iff hD]
        exact ⟨m, hm, hmz⟩
    grind

/-- The end of `m` different from `z` (when `z` is an end of `m`). -/
def otherEnd (ends : Cell → Cell × Cell) (z m : Cell)  :=
  if (ends m).1 = z then (ends m).2 else (ends m).1

omit hD in
theorem ends_eq_of_mem {m z : Cell} (hne : (ends m).1 ≠ (ends m).2) (hz : z = (ends m).1 ∨ z = (ends m).2) :
    ends m = (z, otherEnd ends z m) ∨ ends m = (otherEnd ends z m, z) := by
  grind +locals

omit hD in
theorem otherEnd_ne {m z : Cell} (hne : (ends m).1 ≠ (ends m).2) (hz : z = (ends m).1 ∨ z = (ends m).2) :
    otherEnd ends z m ≠ z := by
  grind +locals

/-- The degree of a vertex is the number of medial vertices having it as an end. -/
theorem degree_eq [DecidableEq Cell] (z : P) [DecidableRel (endGraph ends P M).Adj] :
    (endGraph ends P M).degree z =
      (M.filter  fun m => z.1 = (ends m).1 ∨ z.1 = (ends m).2 ).card := by
  
  
  symm
  have hmem : ∀ m ∈ M,  z.1 = (ends m).1 ∨ z.1 = (ends m).2  → otherEnd ends z.1 m ∈ P := by
    intro m hm hz
    have h1 := hD.mem m hm
    unfold otherEnd
    split_ifs
    · exact h1.2
    · exact h1.1
  refine Finset.card_bij
    (fun m hm =>  ⟨otherEnd ends z.1 m, hmem m (Finset.mem_filter.1 hm).1
      (Finset.mem_filter.1 hm).2⟩ ) ?_ ?_ ?_
  · intro m hm
    obtain ⟨hmM, hz⟩ := Finset.mem_filter.1 hm
    rw [SimpleGraph.mem_neighborFinset, endGraph_adj]
    have hne := hD.ne m
    refine ⟨fun h => otherEnd_ne hne hz (congrArg Subtype.val h).symm, ?_⟩
    rcases ends_eq_of_mem hne hz with h | h
    · exact Or.inl ⟨m, hmM, h⟩
    · exact Or.inr ⟨m, hmM, h⟩
  · intro m hm m' hm' h
    obtain ⟨hmM, hz⟩ := Finset.mem_filter.1 hm
    obtain ⟨hmM', hz'⟩ := Finset.mem_filter.1 hm'
    
    apply hD.inj
    rcases ends_eq_of_mem (hD.ne m) hz with e | e <;>
      rcases ends_eq_of_mem (hD.ne m') hz' with e' | e'
    all_goals simp_all
  · intro d hd
    rw [SimpleGraph.mem_neighborFinset, endGraph_adj] at hd
    obtain ⟨hzd, hd⟩ := hd
    rcases hd with ⟨m, hm, h⟩ | ⟨m, hm, h⟩
    · 
      
      
      unfold otherEnd
      grind
    · 
      refine ⟨m, Finset.mem_filter.2 ⟨hm, Or.inr  (congrArg Prod.snd h).symm ⟩, Subtype.ext ?_⟩
      
      have hne : ¬ (ends m).1 = z.1 := by
        grind
      unfold otherEnd; simp only [hne, ite_false]; exact congrArg Prod.fst h

end

end PottsDiscontinuity.TorusCrossing
