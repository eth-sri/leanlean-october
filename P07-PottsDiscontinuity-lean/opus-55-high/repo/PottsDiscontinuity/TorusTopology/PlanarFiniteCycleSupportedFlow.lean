/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
public import Mathlib.Tactic

public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open SimpleGraph

theorem cycleFlow_zero_sum_on_neighborPair
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {u : V} (p : G.Walk u u) (v a b : V)
    (c : V → V → ℤ)
    (hsupport : ∀ x y, s(x, y) ∉ p.edges → c x y = 0)
    (hbalance : ∑ w : V, c v w = 0)
    (hneighbors : p.toSubgraph.neighborSet v = {a, b})
    (hab : a ≠ b) :
    c v a + c v b = 0 := by
  classical
  let ambient := Finset.univ.filter (fun w => G.Adj v w)
  let cycle := Finset.univ.filter (fun w => p.toSubgraph.Adj v w)
  have hsub : cycle ⊆ ambient := by
    grind
  have hout : ∀ w ∈ ambient, w ∉ cycle → c v w = 0 := by
    intro w hw hnot
    have hnotAdj : ¬p.toSubgraph.Adj v w := by grind
    apply hsupport
    intro hedge
    exact hnotAdj ((p.adj_toSubgraph_iff_mem_edges).2 hedge)
  have hsumEq :=
    Finset.sum_subset hsub hout
  have houtside : ∀ w ∈ Finset.univ, w ∉ ambient → c v w = 0 := by
    intro w _ hnot
    have hnotG : ¬ G.Adj v w := by grind
    apply hsupport
    intro hedge
    exact hnotG (p.adj_of_mem_edges hedge)
  have hall : (∑ w : V, c v w) = (∑ w ∈ ambient, c v w) := by
    symm
    exact Finset.sum_subset (by simp) houtside
  have hcycle : (∑ w ∈ cycle, c v w) = 0 := by
    omega
  have hcycleEq : cycle = ({a, b} : Finset V) := by
    ext w
    simp only [cycle, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← SimpleGraph.Subgraph.mem_neighborSet]
    simp_all
  simpa [hcycleEq, hab] using hcycle

section
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {u : V} (p : G.Walk u u) (hpc : p.IsCycle) (c : V → V → ℤ) (hanti : ∀ x y, c x y = -c y x) (hbalance : ∀ v, ∑ w : V, c v w = 0) (hsupport : ∀ x y, s(x, y) ∉ p.edges → c x y = 0)
include G u p hpc hanti hbalance hsupport
theorem cycleSupportedFlow_constantOnDarts
     :
    ∃ k : ℤ, ∀ d ∈ p.darts, c d.fst d.snd = k := by
  let k := c (p.getVert 0) (p.getVert 1)
  have hstep : ∀ i, 0 < i → i + 1 < p.length →
      c (p.getVert (i - 1)) (p.getVert i) =
        c (p.getVert i) (p.getVert (i + 1)) := by
    intro i hi hlen
    have hneighbors := hpc.neighborSet_toSubgraph_internal
      (by omega : i ≠ 0) (by omega : i < p.length)
    have hsum := cycleFlow_zero_sum_on_neighborPair G p (p.getVert i)
      (p.getVert (i - 1)) (p.getVert (i + 1)) c hsupport (hbalance _)
      hneighbors (hpc.getVert_sub_one_ne_getVert_add_one (by omega))
    grind
  have hconst : ∀ i, i + 1 < p.length →
      c (p.getVert i) (p.getVert (i + 1)) = k := by
    intro i
    induction i with
    | zero => grind
    | succ i ih =>
      grind
  have hlast : c (p.getVert (p.length - 1)) (p.getVert p.length) = k := by
    have hend := hpc.neighborSet_toSubgraph_endpoint
    have hsum := cycleFlow_zero_sum_on_neighborPair G p (p.getVert 0)
      (p.getVert 1) (p.getVert (p.length - 1)) c hsupport (hbalance _)
      (by simpa using hend)
      (by simpa using hpc.snd_ne_penultimate)
    have hstart : c u (p.getVert 1) = k := by
      have hstart' := hconst 0 (by
        have := hpc.three_le_length
        omega)
      simpa using hstart' 
    have hanti' := hanti (p.getVert (p.length - 1)) (p.getVert p.length)
    rw [p.getVert_length] at hanti'
    rw [p.getVert_zero] at hsum
    simp
    omega
  refine ⟨k, ?_⟩
  intro d hd
  obtain ⟨i, hi, hdeq⟩ := List.mem_iff_getElem.mp hd
  subst d
  rw [p.darts_getElem_eq_getVert i (by omega)]
  by_cases hnotLast : i + 1 < p.length <;> grind

theorem cycleSupportedFlow_constantOnDarts_sign
    (hnonzero : ∀ x y, s(x, y) ∈ p.edges → c x y ≠ 0)
    (hbound : ∀ x y, c x y = -1 ∨ c x y = 0 ∨ c x y = 1) :
    ∃ k : ℤ, (k = -1 ∨ k = 1) ∧ ∀ d ∈ p.darts, c d.fst d.snd = k := by
  obtain ⟨k, hk⟩ := cycleSupportedFlow_constantOnDarts G p hpc c hanti
    hbalance hsupport
  have hnotnil := hpc.not_nil
  let d := p.firstDart hnotnil
  have hd : d ∈ p.darts := by simp [d]
  have hedge : s(d.fst, d.snd) ∈ p.edges := by
    have hhead : p.edges.head (Walk.edges_eq_nil.not.mpr hnotnil) ∈ p.edges :=
      List.head_mem _
    rw [p.head_edges_eq_mk_start_snd (Walk.edges_eq_nil.not.mpr hnotnil)] at hhead
    tauto
  have hsign : k = -1 ∨ k = 1 := by
    grind
  exact ⟨k, hsign, hk⟩
end

end PottsDiscontinuity.TorusTopology.Planar.Medial
