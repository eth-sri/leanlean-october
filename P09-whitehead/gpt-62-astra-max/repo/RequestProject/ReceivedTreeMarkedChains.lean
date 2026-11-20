module

public import RequestProject.ReceivedTreeRootedChainFaithfulness

@[expose] public section

/-! Exact marked relative boundaries in the actual receiving-group cover. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
open scoped Classical
universe u
variable {K : Complex2.{u}} (T : SpanningTree K) {G : Type u} [Group G]
  (φ : PresGroup (treeRel T) →* G) {I : Type u}

variable (p : I → List (K.E × Bool))

/-- The actual sum of the lifted marked paths, before choosing coordinates. -/
noncomputable def markedChainMap :
    ((G × I) →₀ ℤ) →ₗ[ℤ] ((G × K.E) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => pathChain (liftPath T φ (p x.2) x.1))

theorem markedChainMap_single (g : G) (i : I) (n : ℤ) :
    markedChainMap T φ p (Finsupp.single (g, i) n) =
      n • pathChain (liftPath T φ (p i) g) :=
  by apply Finsupp.linearCombination_single

/-- A lifted root loop may end on another sheet, but its chain boundary is
supported entirely over the root. No closedness assumption is needed. -/
theorem markedChainMap_boundary_off_root (p : I → Loop K T.root)
    (c : (G × I) →₀ ℤ) (g : G) (v : K.V) (hv : v ≠ T.root) :
    bdry1 (cover T φ) (markedChainMap T φ (fun i => (p i).1) c) (g, v) = 0 := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single x n =>
    obtain ⟨h, i⟩ := x
    rw [markedChainMap_single, map_smul,
      bdry1_pathChain_of_isPath (liftPath_isPath T φ (p i).2 h)]
    rw [Finsupp.smul_apply, Finsupp.sub_apply] <;> grind

variable [Fintype I] [DecidableEq (NonTree T)]

theorem cellCoefficient_markedChainMap (p : I → List _)
    (c : (G × I) →₀ ℤ) (z : NonTree T) :
    cellCoefficient z.1 (markedChainMap T φ p c) =
      ∑ i, cellCoefficient i c * coefficientMap T φ (fox z (pathWord T (p i))) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [map_add, hc, hd, add_mul, Finset.sum_add_distrib]
  | single x n =>
    obtain ⟨g, i⟩ := x
    rw [markedChainMap_single, map_smul, cellCoefficient_liftPath,
      ← smul_mul_assoc, MonoidAlgebra.smul_single]
    simp [cellCoefficient_single]

variable (p : I → Loop K T.root) (γ : I → MonoidAlgebra ℤ G)

/-- Assemble the full group-ring marked coefficients into genuine edge chains. -/
noncomputable def markedChain :=
  markedChainMap T φ (fun i => (p i).1) ((cellCoordinates I).symm γ)

theorem cellCoefficient_markedChain (z : NonTree T) :
    cellCoefficient z.1 (markedChain T φ p γ) =
      ∑ i, γ i * coefficientMap T φ (fox z (pathWord T (p i).1)) := by
  simp [markedChain, cellCoefficient_markedChainMap, cellCoefficient_coordinates_symm]

omit [DecidableEq _] in
theorem markedChain_boundary_off_root (g : G) (v : K.V) (hv : v ≠ T.root) :
    bdry1 (cover T φ) (markedChain T φ p γ) (g, v) = 0 :=
  by solve_by_elim [markedChainMap_boundary_off_root]

/-- Equality of the non-tree Fox coordinates of a two-boundary and a marked
chain implies exact equality of the edge chains, including every tree edge. -/
theorem bdry2_eq_markedChain_of_coordinates (c : (G × K.F) →₀ ℤ)
    (hc : ∀ z : NonTree T, cellCoefficient z.1 (bdry2 (cover T φ) c) =
      ∑ i, γ i * coefficientMap T φ (fox z (pathWord T (p i).1))) :
    bdry2 (cover T φ) c = markedChain T φ p γ := by
  apply edgeChains_eq_of_nonTree_coordinates T φ
  · intro z
    rw [cellCoefficient_markedChain]
    exact hc z
  · grind [bdry1_bdry2, markedChain_boundary_off_root]

end FiniteChains.Comb.ReceivedTree
