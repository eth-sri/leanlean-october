import RequestProject.ClassicalCWChainDiskNaturality
import RequestProject.GraphWordDiskConnectedReflection
import RequestProject.TopologicalAcyclicCoverHomotopy
import RequestProject.TreeChain
import RequestProject.Tac


/-! Connectedness and compatible spanning trees for the simultaneous
original-cell models. The input is exactly connectedness of the given
CW subcomplexes. Unverified source. -/

noncomputable section
bwd

namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment
open Set Topology
open scoped Classical
variable (K : Whitehead.TwoComplex) {n : ℕ}
  (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set K))
  (hC : Monotone C) (hconn : ∀ i, ConnectedSpace (C i : Set K))
  [Choices C]

/-- A relative construction can fix the tree on its original graph.
The unseeded construction obtains one from connectedness. -/
class TreeChoice where
  initial : Option (Comb.SpanningTree (subcomplexGraph (C 0)))


variable [TreeChoice K C]

omit [TreeChoice K C] in
include hconn in
theorem wordDisk_connected (i : Fin (n + 1)) :
    ConnectedSpace (DiskAttachment (wordAttaching C hC i)) := Whitehead.connectedSpace_of_homotopyEquiv (wordDiskEquiv K C hC i).symm

omit [TreeChoice K C] in
include hC hconn in
theorem graph_connected (i : Fin (n + 1)) : Comb.IsConnected (subcomplexGraph (C i)) := by
  letI := subcomplexZeroSkeleton_discrete (C i)
  letI : ConnectedSpace (DiskAttachment
      (boundaryWordsAttaching (skeletonAttachingMap (C i : Set K) 1) (word C hC i))) :=
    wordDisk_connected K C hC hconn i
  exact graphCx_isConnected_of_wordDisks _ (word C hC i)

omit [TreeChoice K C] in
include hC hconn in
theorem graph_nonempty (i : Fin (n + 1)) : Nonempty (subcomplexGraph (C i)).V := by
  letI : ConnectedSpace (DiskAttachment
      (boundaryWordsAttaching (skeletonAttachingMap (C i : Set K) 1) (word C hC i))) :=
    wordDisk_connected K C hC hconn i
  exact graph_vertices_nonempty_of_wordDisks (V := SkeletonCarrier (C i : Set K) 1)
    _ (word C hC i)

def boundedStage (n r : ℕ) : Fin (n + 1) :=
  ⟨min r n, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

theorem boundedStage_monotone n : Monotone (boundedStage n) :=
  fun _ _ h => min_le_min h le_rfl

def boundedGraph (r : ℕ) := subcomplexGraph (C (boundedStage n r))

def boundedGraphInclusion (r : ℕ) :
    Comb.Hom (boundedGraph K C r) (boundedGraph K C (r + 1)) :=
  subcomplexGraphInclusion (hC (boundedStage_monotone n r.le_succ))

include hconn in
theorem boundedGraphs_have_compatible_trees :
    ∃ T : ∀ r, Comb.SpanningTree (boundedGraph K C r),
      (∀ S, TreeChoice.initial (K := K) (C := C) = some S → T 0 = S) ∧
      ∀ r e, (T (r + 1)).isTree ((boundedGraphInclusion K C hC r).onE e) ↔ (T r).isTree e := by
  letI : Nonempty (boundedGraph K C 0).V := graph_nonempty K C hC hconn _
  let v : (boundedGraph K C 0).V := Classical.choice inferInstance
  obtain ⟨R₀, hroot⟩ := Comb.SpanningTree.exists_of_isConnected
    (graph_connected K C hC hconn _) v
  let T₀ : Comb.SpanningTree (boundedGraph K C 0) :=
    (TreeChoice.initial (K := K) (C := C)).getD R₀
  obtain ⟨T, hT₀, hT⟩ := Comb.SpanningTree.exists_compatible_trees
    _ (boundedGraphInclusion K C hC)
    (fun r => graph_connected K C hC hconn _)
    (fun r => subcomplexGraphInclusion_injective_V _)
    (fun r => subcomplexGraphInclusion_injective_E _) T₀
  aesop
