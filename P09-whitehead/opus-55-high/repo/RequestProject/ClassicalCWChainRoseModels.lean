import RequestProject.ClassicalCWChainConnectivity
import RequestProject.ClassicalGraphTreeWordNaturality
import RequestProject.DiskRoseMaps
import RequestProject.Tac


/-! A simultaneous tree collapse of the actual graph-and-disk models.
The original two-cell labels and disk parameters are retained. Compatible
trees are constructed from connectedness, not supplied as a new input.
Unverified source. -/

noncomputable section
bwd

namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment
open Set Topology
open scoped Classical ContinuousMap
variable (K : Whitehead.TwoComplex) {n : ℕ}
  (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set K))
  (hC : Monotone C) (hconn : ∀ i, ConnectedSpace (C i : Set K))
  [Choices C]
  [TreeChoice K C]

omit [Choices C] [TreeChoice K C] in
theorem boundedTrees_compatible
    (T : ∀ r, Comb.SpanningTree (boundedGraph K C r))
    (hT : ∀ r e, (T (r + 1)).isTree ((boundedGraphInclusion K C hC r).onE e) ↔
      (T r).isTree e) {r s : ℕ} (hrs : r ≤ s)
    (e : (boundedGraph K C r).E) :
    (T s).isTree ((subcomplexGraphInclusion (hC (boundedStage_monotone n hrs))).onE e) ↔
      (T r).isTree e := by
  induction s, hrs using Nat.le_induction with
  | base => rfl
  | succ s hrs ih =>
      exact (hT s _).trans ih

include hconn in
theorem finiteGraphs_have_compatible_trees :
    ∃ T : ∀ i, Comb.SpanningTree (subcomplexGraph (C i)),
      (∀ S, TreeChoice.initial (K := K) (C := C) = some S → T 0 = S) ∧
      ∀ {i k : Fin (n + 1)} (hik : i ≤ k) e,
        (T k).isTree ((subcomplexGraphInclusion (hC hik)).onE e) ↔ (T i).isTree e := by
  obtain ⟨T, hT₀, hT⟩ := boundedGraphs_have_compatible_trees K C hC hconn
  have hs (i : Fin (n + 1)) : boundedStage n i.val = i := by
    apply Fin.ext
    exact Nat.min_eq_left (Nat.le_of_lt_succ i.isLt)
  let U (i : Fin (n + 1)) : Comb.SpanningTree (subcomplexGraph (C i)) := (hs i) ▸ T i.val
  have transport (a b : ℕ) (hab : a ≤ b) (i k : Fin (n + 1))
      (ha : boundedStage n a = i) (hb : boundedStage n b = k) (hik : i ≤ k) :
      ∀ e : (subcomplexGraph (C i)).E,
        (show Comb.SpanningTree (subcomplexGraph (C k)) from hb ▸ T b).isTree
            ((subcomplexGraphInclusion (hC hik)).onE e) ↔
          (show Comb.SpanningTree (subcomplexGraph (C i)) from ha ▸ T a).isTree e := by
    subst i
    subst k
    exact boundedTrees_compatible K C hC T hT hab
  refine ⟨U, ?_, ?_⟩
  · tauto
  grind

def chainTree (i : Fin (n + 1)) :=
  Classical.choose (finiteGraphs_have_compatible_trees K C hC hconn) i

theorem chainTree_zero S
    (hS : TreeChoice.initial (K := K) (C := C) = some S) :
    chainTree K C hC hconn 0 = S :=
  (Classical.choose_spec (finiteGraphs_have_compatible_trees K C hC hconn)).1 S hS

theorem chainTree_compatible {i k : Fin (n + 1)} (hik : i ≤ k)
    e :
    (chainTree K C hC hconn k).isTree ((subcomplexGraphInclusion (hC hik)).onE e) ↔
      (chainTree K C hC hconn i).isTree e :=
  (Classical.choose_spec (finiteGraphs_have_compatible_trees K C hC hconn)).2 hik e

abbrev RoseGen (i : Fin (n + 1)) :=
  {e : (subcomplexGraph (C i)).E // ¬(chainTree K C hC hconn i).isTree e}

def roseGenInclusion (hik : i ≤ k) :
    RoseGen K C hC hconn i ↪ RoseGen K C hC hconn k where
  toFun e := ⟨(subcomplexGraphInclusion (hC hik)).onE e.val,
    fun ht => e.property ((chainTree_compatible K C hC hconn hik e.val).mp ht)⟩
  inj' := by
    intro e f hef
    apply Subtype.ext
    exact subcomplexGraphInclusion_injective_E (hC hik) (congrArg Subtype.val hef)

def graphCollapse i :
    DiskAttachment (skeletonAttachingMap (C i : Set K) 1) ≃ₕ
      ClassicalGraphModel.Rose (RoseGen K C hC hconn i) := by
  letI := subcomplexZeroSkeleton_discrete (C i)
  exact graphRoseHomotopyEquiv _
    (skeletonAttachingMap _ 1).continuous _

theorem graphCollapse_natural hik :
    (diskRoseMap (roseGenInclusion K C hC hconn hik)).comp
        (graphCollapse K C hC hconn i).toFun =
      (graphCollapse K C hC hconn k).toFun.comp (subcomplexGraphDiskMap (hC hik)) := by
  letI := subcomplexZeroSkeleton_discrete (C i)
  letI := subcomplexZeroSkeleton_discrete (C k)
  have H := graphRoseHomotopyEquiv_natural
    _ (skeletonAttachingMap (C i : Set K) 1).continuous
    _ (skeletonAttachingMap (C k : Set K) 1).continuous
    _ _
    _ (chainTree_compatible K C hC hconn hik)
    _ (subcomplexGraphDiskMap_old _)
    (subcomplexDiskMap_cell _ 1)
  tauto

def collapsedAttaching i :=
  (graphCollapse K C hC hconn i).toFun.comp (wordAttaching C hC i)

theorem collapsedAttaching_natural hik
    j a :
    diskRoseMap (roseGenInclusion K C hC hconn hik) (collapsedAttaching K C hC hconn i ⟨j, a⟩) =
      collapsedAttaching K C hC hconn k ⟨subcomplexCellInclusion (hC hik) 2 j, a⟩ := by
  have H := congrArg (· (wordAttaching C hC i ⟨j, a⟩))
    (graphCollapse_natural K C hC hconn hik)
  change _ = graphCollapse K C hC hconn k
    (subcomplexGraphDiskMap (hC hik) (wordAttaching C hC i ⟨j, a⟩)) at H
  rwd [wordAttaching_natural] at H
  exact H

def collapsedDiskInclusion {i k : Fin (n + 1)} (hik : i ≤ k) :=
  diskFamilyMap _ _
    _
    _ (collapsedAttaching_natural K C hC hconn hik)

def collapsedDiskChange (i : Fin (n + 1)) :=
  diskAttachmentBaseChangeHomotopyEquiv (wordAttaching C hC i) (graphCollapse K C hC hconn i)

theorem collapsedDiskChange_natural hik :
    (collapsedDiskInclusion K C hC hconn hik).comp (collapsedDiskChange K C hC hconn i).toFun =
      (collapsedDiskChange K C hC hconn k).toFun.comp (wordDiskInclusion K C hC hik) := by
  apply hom_ext _
    _
  · intro x
    have hmid := congrArg (old (collapsedAttaching K C hC hconn k)
      (boundaryFamilyInclusion (RelCWComplex.cell (C k : Set K) 2) (Fin 2 → ℝ)))
      (congrArg (· x) (graphCollapse_natural K C hC hconn hik))
    tauto
  · rintro ⟨j, x⟩
    have hleft := (congrArg (collapsedDiskInclusion K C hC hconn hik)
      (diskAttachmentBaseChangeHomotopyEquiv_cell _
        (graphCollapse K C hC hconn i) _)).trans
      (diskFamilyMap_cell _ _
        _ _
        _ j x)
    have hright := (congrArg _
      (diskFamilyMap_cell _ _
        _ _
        (wordAttaching_natural K C hC hik) j x)).trans
      (diskAttachmentBaseChangeHomotopyEquiv_cell _
        (graphCollapse K C hC hconn k) _)
    exact hleft.trans hright.symm

theorem collapsedDiskInclusion_killsPi2_iff hik :
    Whitehead.KillsPi2 (collapsedDiskInclusion K C hC hconn hik) ↔
      Whitehead.KillsPi2 (⟨Set.inclusion (hC hik), continuous_inclusion (hC hik)⟩ :
        C((C i : Set K), (C k : Set K))) := by
  rwd [← wordDiskInclusion_killsPi2_iff K C hC hik]
  apply Whitehead.killsPi2_homotopyEquiv_square_iff
    _ _
  rwd [collapsedDiskChange_natural]
