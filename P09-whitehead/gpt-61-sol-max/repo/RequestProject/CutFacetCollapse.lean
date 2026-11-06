import Mathlib.Tactic

import RequestProject.GeometricChainCollapse

/-! Positive corner cubes may always be collapsed across their own cut facets. -/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

noncomputable def preferCutFace (p : Cube V × (Cube V ⊕ Finset V)) :
    Cube V × (Cube V ⊕ Finset V) := if p.1 = posCube (freeSet p.1) then (p.1, Sum.inr (freeSet p.1)) else p

noncomputable def preferCutFaces (lp : List (Cube V × (Cube V ⊕ Finset V))) :=
  lp.map preferCutFace

section
omit [LinearOrder V]
theorem preferCutFaces_positive_pair {lp : List (Cube V × (Cube V ⊕ Finset V))}
    {p : Cube V × (Cube V ⊕ Finset V)} (hp : p ∈ preferCutFaces lp)
    (hpos : p.1 = posCube (freeSet p.1)) : p.2 = Sum.inr (freeSet p.1) := by
  obtain ⟨r, _, he⟩ := List.mem_map.mp hp
  subst p
  by_cases hr : r.1 = posCube (freeSet r.1)
  · simp [preferCutFace, if_pos hr]
  · grind [posCube, freeSet, Collapse.IsPairCollapse, preferCutFace]

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
    · simp_all [Collapse.IsPairCollapse, preferCutFaces, preferCutFace]
end

/-- The oriented chain certificate is determined by the actual free-face incidences. -/
theorem spine_pair_chainCollapse {L : ASC V}
    {lp : List (Cube V × (Cube V ⊕ Finset V))} {S : Finset (Cube V)}
    (hS : S ⊆ topCubes L) (h : Collapse.IsPairCollapse (spineInc L) lp S) :
    CollapseChain.IsChainCollapse (cubeBdry (V := V)) lp := by
  apply h.chainCollapse (tops := topCubes L) ?_ ?_ hS
  · intro t ht f htf
    cases f with
    | inl g =>
      by_cases hg : (freeSet g).card = 2
      · rw [spineInc, if_pos hg] at htf
        rcases cubeBdry_inl_eq_unit htf with hh | hh <;> rw [hh] <;> simp
      · simp [spineInc, hg] at htf
    | inr σ =>
      classical aesop (add simp [IsTri, spineInc, cubeBdry_inr_eq_neg_one])
  · classical grind [FiniteChains.cubeBdry_inl_eq_zero, FiniteChains.mem_cofaces, FiniteChains.freeSet_update_free, FiniteChains.mem_topCubes, FiniteChains.cubeBdry_inr_eq_zero, FiniteChains.freeSet_posCube, freeSet, mem_freeSet, spineInc, IsTri]

abbrev preferCutFaces_isChainCollapse {L : ASC V}
    {lp : List (Cube V × (Cube V ⊕ Finset V))} {S : Finset (Cube V)}
    (hS : S ⊆ topCubes L) (h : Collapse.IsPairCollapse (spineInc L) lp S)  :=
  FiniteChains.spine_pair_chainCollapse hS (FiniteChains.preferCutFaces_isPairCollapse hS h)

end FiniteChains
