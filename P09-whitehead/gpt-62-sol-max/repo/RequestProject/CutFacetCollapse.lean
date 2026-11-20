module

public import RequestProject.GeometricChainCollapse

@[expose] public section

/-! Positive corner cubes may always be collapsed across their own cut facets. -/

namespace FiniteChains
variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

noncomputable def preferCutFace (p : Cube V × (Cube V ⊕ Finset V)) :
    Cube V × (Cube V ⊕ Finset V) := by
  classical
  exact if p.1 = posCube (freeSet p.1) then (p.1, Sum.inr (freeSet p.1)) else p

noncomputable def preferCutFaces (lp : List (Cube V × (Cube V ⊕ Finset V))) :=
  lp.map preferCutFace

omit [LinearOrder V] in
theorem preferCutFaces_positive_pair {lp : List (Cube V × (Cube V ⊕ Finset V))}
    {p : Cube V × (Cube V ⊕ Finset V)} (hp : p ∈ preferCutFaces lp)
    (hpos : p.1 = posCube (freeSet p.1)) : p.2 = Sum.inr (freeSet p.1) := by
  grind +locals

omit [LinearOrder V] in
theorem preferCutFaces_isPairCollapse {L : ASC V}
    {lp : List (Cube V × (Cube V ⊕ Finset V))} {S : Finset (Cube V)}
    (hS : S ⊆ topCubes L) (h : Collapse.IsPairCollapse (spineInc L) lp S) :
    Collapse.IsPairCollapse (spineInc L) (preferCutFaces lp) S := by
  classical
  induction lp generalizing S with
  | nil => exact h
  | cons p lp ih =>
    have ht := mem_topCubes.mp (hS h.1)
    have hrest := ih (fun t ht => hS (Finset.mem_of_mem_erase ht)) h.2.2
    by_cases hp : p.1 = posCube (freeSet p.1)
    · simp only [preferCutFaces, List.map_cons, preferCutFace, if_pos hp]
      refine ⟨h.1, ?_, hrest⟩
      change spineInc L (Sum.inr (freeSet p.1)) ∩ S = {p.1}
      rw [spineInc, if_pos ht, ← hp]
      exact Finset.singleton_inter_of_mem h.1
    · simpa [Collapse.IsPairCollapse,preferCutFaces, List.map_cons, preferCutFace, if_neg hp] using
        And.intro h.1 (And.intro h.2.1 hrest)

theorem preferCutFaces_isChainCollapse {L : ASC V}
    {lp : List (Cube V × (Cube V ⊕ Finset V))} {S : Finset (Cube V)}
    (hS : S ⊆ topCubes L) (h : Collapse.IsPairCollapse (spineInc L) lp S) :
    CollapseChain.IsChainCollapse (cubeBdry (V := V)) (preferCutFaces lp) :=
  spine_pair_chainCollapse hS (preferCutFaces_isPairCollapse hS h)

end FiniteChains
