import RequestProject.ClassicalCWLoopCellularization
import RequestProject.ClassicalGraphPathStraightening
import Mathlib.Topology.Connected.Clopen


/-! The actual graph underlying the original CW one-skeleton. Its vertices
are the literal zero-skeleton points and its edges the original one-cell
indices. Connectedness and finite edge-word representatives are proved from
the original CW axioms. Pending Lean verification. -/

noncomputable section
open scoped Classical
open Set Topology

namespace FiniteChains.ClassicalCW
open ClassicalSkeletonAttachment RelativeAttachment ClassicalGraphModel ContinuousEdgeWords

variable {X : Type} [TopologicalSpace X] [T2Space X] [CWComplex (Set.univ : Set X)]

theorem isClosed_of_closedCell_constant S
    (hS : ∀ n (j : RelCWComplex.cell (Set.univ : Set X) n),
      CWComplex.closedCell n j ⊆ S ∨ Disjoint (CWComplex.closedCell n j) S) : IsClosed S := by
  apply (CWComplex.closed _ S (Set.subset_univ _)).mpr
  intro n j
  rcases hS n j with h | h
  · rw [Set.inter_eq_right.mpr h]
    exact CWComplex.isClosed_closedCell
  · grind [Set.disjoint_iff_inter_eq_empty.mp h.symm]

theorem cw_pathComponent_isClopen (x : X) : IsClopen (pathComponent x) := by
  have hcell (n : ℕ) (j : RelCWComplex.cell Set.univ n) :
      CWComplex.closedCell n j ⊆ pathComponent x ∨
        Disjoint (CWComplex.closedCell n j) (pathComponent x) := by
    by_cases h : (CWComplex.closedCell n j ∩ pathComponent x).Nonempty
    · obtain ⟨y, hy, hxy⟩ := h
      left
      intro z hz
      exact hxy.trans ((closedCell_joined n j hy hz).joined)
    · exact Or.inr (Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp h))
  refine ⟨isClosed_of_closedCell_constant _ hcell, ?_⟩
  apply isClosed_compl_iff.mp
  apply isClosed_of_closedCell_constant
  grind

/-- Connected classical CW complexes are actually path connected. -/
theorem cw_pathConnectedSpace [ConnectedSpace X] : PathConnectedSpace X where
  nonempty := inferInstance
  joined x y := by
    have h := (cw_pathComponent_isClopen x).eq_univ (pathComponent.nonempty x)
    exact (show y ∈ pathComponent x from by simp_all)

theorem zeroSkeleton_cellSeparated :
    CellSeparated (CWComplex.skeletonLT (Set.univ : Set X) 1 : Set X) := by
  intro n j
  by_cases hn : n = 0
  · subst n
    exact (Set.subsingleton_singleton (a := RelCWComplex.map 0 j ![])).anti (by
      simp [CWComplex.openCell_zero_eq_singleton])
  · intro x hx y hy
    exact False.elim (Set.disjoint_left.mp
      (CWComplex.disjoint_skeletonLT_openCell (C := Set.univ) (j := j)
        (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)) hx.1 hx.2)

theorem zeroSkeleton_discrete :
    DiscreteTopology (SkeletonCarrier (Set.univ : Set X) 1) :=
  (zeroSkeleton_cellSeparated (X := X)).isDiscrete.to_subtype

def zeroCellPoint (j : RelCWComplex.cell (Set.univ : Set X) 0) :
    SkeletonCarrier (Set.univ : Set X) 1 :=
  ⟨vertexPoint j, CWComplex.closedCell_subset_skeletonLT 0 j
    (by rw [CWComplex.closedCell_zero_eq_singleton]; rfl)⟩

theorem zeroCellPoint_bijective : Function.Bijective (zeroCellPoint (X := X)) := by
  constructor
  · intro i j h
    have hi : vertexPoint i ∈ CWComplex.openCell 0 i := by
      rw [CWComplex.openCell_zero_eq_singleton]
      rfl
    have hj : vertexPoint i ∈ CWComplex.openCell 0 j := by
      have hv : vertexPoint i = vertexPoint j := congrArg Subtype.val h
      rw [hv, CWComplex.openCell_zero_eq_singleton]
      rfl
    have hlabel := RelCWComplex.eq_of_not_disjoint_openCell
      (Set.disjoint_left.mp · hi hj)
    simp_all
  · intro x
    have hx := x.property
    change x.val ∈ (CWComplex.skeletonLT (Set.univ : Set X) (1 : ℕ∞) : Set X) at hx
    rw [← CWComplex.iUnion_openCell_eq_skeletonLT] at hx
    obtain ⟨n, hn, j, hj⟩ := by simpa only [Set.mem_iUnion] using hx
    have hn' : n < 1 := by exact_mod_cast hn
    have hn0 : n = 0 := by omega
    subst n
    refine ⟨j, Subtype.ext ?_⟩
    exact (show x.val = vertexPoint j from by
      simp_all [CWComplex.openCell_zero_eq_singleton, Set.mem_singleton_iff, vertexPoint]).symm

/-- The literal original zero-cells label the vertices bijectively. -/
def zeroCellEquiv : RelCWComplex.cell (Set.univ : Set X) 0 ≃
    SkeletonCarrier (Set.univ : Set X) 1 :=
  Equiv.ofBijective zeroCellPoint zeroCellPoint_bijective

variable (K : Whitehead.TwoComplex)

theorem oneSkeleton_nonempty : Nonempty (OneSkeleton K) := by
  let x : K := Classical.choice inferInstance
  let j := pointVertex x
  exact ⟨skeletonInclusion _ 1 (zeroCellPoint j)⟩

theorem oneSkeleton_pathConnectedSpace : PathConnectedSpace (OneSkeleton K) where
  nonempty := oneSkeleton_nonempty K
  joined x y := by
    letI := cw_pathConnectedSpace (X := K)
    cases' PathConnectedSpace.joined x.val y.val with p
    cases' path_into_oneSkeleton K x y p with q _
    tauto

abbrev originalGraphAttaching := skeletonAttachingMap (Set.univ : Set K) 1

def originalGraph := graphCx (originalGraphAttaching K)

theorem originalGraph_isConnected : Comb.IsConnected (originalGraph K) := by
  letI := zeroSkeleton_discrete (X := K)
  letI : PathConnectedSpace (SkeletonCarrier (Set.univ : Set K) 2) :=
    oneSkeleton_pathConnectedSpace K
  let e := skeletonAsDiskAttachment (Set.univ : Set K) 1
  letI : PathConnectedSpace (DiskAttachment (originalGraphAttaching K)) :=
    e.surjective.pathConnectedSpace e.continuous
  exact graphCx_isConnected _ (originalGraphAttaching K).continuous

/-- The original graph admits a spanning tree, including for arbitrary
infinite cell families. Its existence uses actual continuous connectedness. -/
theorem originalGraph_exists_spanningTree (v : SkeletonCarrier Set.univ 1) :
    ∃ T : Comb.SpanningTree (originalGraph K), T.root = v :=
  Comb.SpanningTree.exists_of_isConnected (originalGraph_isConnected K) v
