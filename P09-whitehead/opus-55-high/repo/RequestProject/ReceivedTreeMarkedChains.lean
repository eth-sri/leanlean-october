import RequestProject.ReceivedTreeRootedChainFaithfulness
import RequestProject.Tac
noncomputable section


/-! Exact marked relative boundaries in the actual receiving-group cover. -/
bwd

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
open scoped Classical
universe u
variable {K : Complex2.{u}} (T : SpanningTree K) {G : Type u} [Group G]
  (φ : PresGroup (treeRel T) →* G) {I : Type u}

/-- The actual sum of the lifted marked paths, before choosing coordinates. -/
def markedChainMap (p : I → List (K.E × Bool)) :
    ((G × I) →₀ ℤ) →ₗ[ℤ] ((G × K.E) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => pathChain (liftPath T φ (p x.2) x.1))

theorem markedChainMap_single p g (i : I) n :
    markedChainMap T φ p (Finsupp.single (g, i) n) =
      n • pathChain (liftPath T φ (p i) g) :=
  Finsupp.linearCombination_single ℤ n _

/-- A lifted root loop may end on another sheet, but its chain boundary is
supported entirely over the root. No closedness assumption is needed. -/
theorem markedChainMap_boundary_off_root (p : I → Loop K T.root)
    c g v (hv : v ≠ T.root) :
    bdry1 (cover T φ) (markedChainMap T φ (fun i => (p i).1) c) (g, v) = 0 := by
  classical
  lin_ind c x n =>
    cases' x with h i
    rw [markedChainMap_single, map_smul,
      bdry1_pathChain_of_isPath (liftPath_isPath T φ (p i).2 h)]
    rw [Finsupp.smul_apply, Finsupp.sub_apply]
    grind

variable [Fintype I] [DecidableEq (NonTree T)]

theorem cellCoefficient_markedChainMap p
    (c : (G × I) →₀ ℤ) z :
    cellCoefficient z.1 (markedChainMap T φ p c) =
      ∑ i, cellCoefficient i c * coefficientMap T φ (fox z (pathWord T (p i))) := by
  classical
  lin_ind c with c d hc hd => simp [map_add, hc, hd, add_mul, Finset.sum_add_distrib]
  | x n =>
    cases' x with g i
    rw [markedChainMap_single, map_smul, cellCoefficient_liftPath,
      ← smul_mul_assoc, MonoidAlgebra.smul_single]
    simp [cellCoefficient_single]

/-- Assemble the full group-ring marked coefficients into genuine edge chains. -/
def markedChain (p : I → Loop K T.root) (γ : I → MonoidAlgebra ℤ G) :=
  markedChainMap T φ (fun i => (p i).1) ((cellCoordinates I).symm γ)

theorem cellCoefficient_markedChain p
    (γ : I → MonoidAlgebra ℤ G) z :
    cellCoefficient z.1 (markedChain T φ p γ) =
      ∑ i, γ i * coefficientMap T φ (fox z (pathWord T (p i).1)) := by
  simp [markedChain, cellCoefficient_markedChainMap, cellCoefficient_coordinates_symm]

omit [DecidableEq (NonTree T)] in
theorem markedChain_boundary_off_root (p : I → Loop K T.root)
    (γ : I → MonoidAlgebra ℤ G) (g : G) (v : K.V) (hv : v ≠ T.root) :
    bdry1 (cover T φ) (markedChain T φ p γ) (g, v) = 0 :=
  markedChainMap_boundary_off_root T φ p _ g v hv

/-- Equality of the non-tree Fox coordinates of a two-boundary and a marked
chain implies exact equality of the edge chains, including every tree edge. -/
theorem bdry2_eq_markedChain_of_coordinates p
    (γ : I → MonoidAlgebra ℤ G) (c : (G × K.F) →₀ ℤ)
    (hc : ∀ z, cellCoefficient z.1 (bdry2 (cover T φ) c) =
      ∑ i, γ i * coefficientMap T φ (fox z (pathWord T (p i).1))) :
    bdry2 (cover T φ) c = markedChain T φ p γ := by
  apply edgeChains_eq_of_nonTree_coordinates T φ
  · simp_all [cellCoefficient_markedChain]
  · intro g v hv
    rw [bdry1_bdry2, Finsupp.zero_apply, markedChain_boundary_off_root T φ p γ g v hv]
