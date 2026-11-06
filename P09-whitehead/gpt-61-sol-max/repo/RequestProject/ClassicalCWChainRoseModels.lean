import Mathlib.Tactic

import RequestProject.ClassicalCWChainConnectivity
import RequestProject.ClassicalGraphTreeWordNaturality
import RequestProject.DiskRoseMaps

/-! A simultaneous tree collapse of the actual graph-and-disk models.
The original two-cell labels and disk parameters are retained. Compatible
trees are constructed from connectedness, not supplied as a new input.
Unverified source. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

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
      exact (hT s ((subcomplexGraphInclusion
        (hC (boundedStage_monotone n hrs))).onE e)).trans ih

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
    aesop (add simp [boundedTrees_compatible])
  refine ⟨U, ?_, ?_⟩
  · intro S hS
    exact hT₀ S hS
  · grind

variable (i : Fin (n + 1))
def chainTree   :=
  Classical.choose (finiteGraphs_have_compatible_trees K C hC hconn) i

theorem chainTree_zero (S : Comb.SpanningTree (subcomplexGraph (C 0)))
    (hS : TreeChoice.initial (K := K) (C := C) = some S) :
    chainTree K C hC hconn 0 = S :=
  (Classical.choose_spec (finiteGraphs_have_compatible_trees K C hC hconn)).1 S hS

abbrev chainTree_compatible {i k : Fin (n + 1)} (hik : i ≤ k)
    (e : (subcomplexGraph (C i)).E)  :=
  (Classical.choose_spec (FiniteChains.ClassicalCW.ChainWords.finiteGraphs_have_compatible_trees K C hC hconn)).right hik
    e

abbrev RoseGen  :=
  {e : (subcomplexGraph (C i)).E // ¬(chainTree K C hC hconn i).isTree e}

def roseGenInclusion {i k : Fin (n + 1)} (hik : i ≤ k) :
    RoseGen K C hC hconn i ↪ RoseGen K C hC hconn k where
  toFun e := ⟨(subcomplexGraphInclusion (hC hik)).onE e.val,
    fun ht => e.property ((chainTree_compatible K C hC hconn hik e.val).mp ht)⟩
  inj' := by
    intro e f hef
    apply Subtype.ext
    exact subcomplexGraphInclusion_injective_E (hC hik) (congrArg Subtype.val hef)

def graphCollapse  :
    DiskAttachment (skeletonAttachingMap (C i : Set K) 1) ≃ₕ
      ClassicalGraphModel.Rose (RoseGen K C hC hconn i) := by
  letI := subcomplexZeroSkeleton_discrete (C i)
  exact graphRoseHomotopyEquiv (skeletonAttachingMap (C i : Set K) 1)
    (skeletonAttachingMap (C i : Set K) 1).continuous (chainTree K C hC hconn i)

theorem graphCollapse_natural {i k : Fin (n + 1)} (hik : i ≤ k) :
    (diskRoseMap (roseGenInclusion K C hC hconn hik)).comp
        (graphCollapse K C hC hconn i).toFun =
      (graphCollapse K C hC hconn k).toFun.comp (subcomplexGraphDiskMap (hC hik)) := by
  classical solve_by_elim (transparency := .default) [FiniteChains.ClassicalCW.subcomplexZeroSkeleton_discrete, FiniteChains.ClassicalGraphModel.graphRoseHomotopyEquiv_natural, FiniteChains.ClassicalCW.ChainWords.chainTree_compatible, FiniteChains.ClassicalCW.subcomplexGraphDiskMap_old, FiniteChains.ClassicalCW.subcomplexDiskMap_cell, FiniteChains.RelativeAttachment.hom_ext, FiniteChains.RelativeAttachment.diskFamilyMap_cell]

def collapsedAttaching   :=
  (graphCollapse K C hC hconn i).toFun.comp (wordAttaching C hC i)

theorem collapsedAttaching_natural {i k : Fin (n + 1)} (hik : i ≤ k)
    (j : RelCWComplex.cell (C i : Set K) 2) (a : UnitBoundary (Fin 2 → ℝ)) :
    diskRoseMap (roseGenInclusion K C hC hconn hik) (collapsedAttaching K C hC hconn i ⟨j, a⟩) =
      collapsedAttaching K C hC hconn k ⟨subcomplexCellInclusion (hC hik) 2 j, a⟩ := by
  have H := congrArg (fun f => f (wordAttaching C hC i ⟨j, a⟩))
    (graphCollapse_natural K C hC hconn hik)
  change _ = graphCollapse K C hC hconn k
    (subcomplexGraphDiskMap (hC hik) (wordAttaching C hC i ⟨j, a⟩)) at H
  rw  [wordAttaching_natural] at H
  exact H

def collapsedDiskInclusion {i k : Fin (n + 1)} (hik : i ≤ k) :=
  diskFamilyMap (collapsedAttaching K C hC hconn i) (collapsedAttaching K C hC hconn k)
    (diskRoseMap (roseGenInclusion K C hC hconn hik))
    (subcomplexCellInclusion (hC hik) 2) (collapsedAttaching_natural K C hC hconn hik)

def collapsedDiskChange  :=
  diskAttachmentBaseChangeHomotopyEquiv (wordAttaching C hC i) (graphCollapse K C hC hconn i)

theorem collapsedDiskChange_natural {i k : Fin (n + 1)} (hik : i ≤ k) :
    (collapsedDiskInclusion K C hC hconn hik).comp (collapsedDiskChange K C hC hconn i).toFun =
      (collapsedDiskChange K C hC hconn k).toFun.comp (wordDiskInclusion K C hC hik) := by
  apply hom_ext (wordAttaching C hC i)
    (boundaryFamilyInclusion (RelCWComplex.cell (C i : Set K) 2) (Fin 2 → ℝ))
  · intro x
    have hleft := (congrArg (collapsedDiskInclusion K C hC hconn hik)
      (diskAttachmentBaseChangeHomotopyEquiv_old (wordAttaching C hC i)
        (graphCollapse K C hC hconn i) x)).trans
      (diskFamilyMap_old (collapsedAttaching K C hC hconn i) (collapsedAttaching K C hC hconn k)
        (diskRoseMap (roseGenInclusion K C hC hconn hik)) (subcomplexCellInclusion (hC hik) 2)
        (collapsedAttaching_natural K C hC hconn hik) (graphCollapse K C hC hconn i x))
    have hright := (congrArg (collapsedDiskChange K C hC hconn k)
      (diskFamilyMap_old (wordAttaching C hC i) (wordAttaching C hC k)
        (subcomplexGraphDiskMap (hC hik)) (subcomplexCellInclusion (hC hik) 2)
        (wordAttaching_natural K C hC hik) x)).trans
      (diskAttachmentBaseChangeHomotopyEquiv_old (wordAttaching C hC k)
        (graphCollapse K C hC hconn k) (subcomplexGraphDiskMap (hC hik) x))
    have hmid := congrArg (old (collapsedAttaching K C hC hconn k)
      (boundaryFamilyInclusion (RelCWComplex.cell (C k : Set K) 2) (Fin 2 → ℝ)))
      (congrArg (fun f => f x) (graphCollapse_natural K C hC hconn hik))
    exact hleft.trans (hmid.trans hright.symm)
  · rintro ⟨j, x⟩
    have hleft := (congrArg (collapsedDiskInclusion K C hC hconn hik)
      (diskAttachmentBaseChangeHomotopyEquiv_cell (wordAttaching C hC i)
        (graphCollapse K C hC hconn i) ⟨j, x⟩)).trans
      (diskFamilyMap_cell (collapsedAttaching K C hC hconn i) (collapsedAttaching K C hC hconn k)
        (diskRoseMap (roseGenInclusion K C hC hconn hik)) (subcomplexCellInclusion (hC hik) 2)
        (collapsedAttaching_natural K C hC hconn hik) j x)
    have hright := (congrArg (collapsedDiskChange K C hC hconn k)
      (diskFamilyMap_cell (wordAttaching C hC i) (wordAttaching C hC k)
        (subcomplexGraphDiskMap (hC hik)) (subcomplexCellInclusion (hC hik) 2)
        (wordAttaching_natural K C hC hik) j x)).trans
      (diskAttachmentBaseChangeHomotopyEquiv_cell (wordAttaching C hC k)
        (graphCollapse K C hC hconn k) ⟨subcomplexCellInclusion (hC hik) 2 j, x⟩)
    exact hleft.trans hright.symm

theorem collapsedDiskInclusion_killsPi2_iff {i k : Fin (n + 1)} (hik : i ≤ k) :
    Whitehead.KillsPi2 (collapsedDiskInclusion K C hC hconn hik) ↔
      Whitehead.KillsPi2 (⟨Set.inclusion (hC hik), continuous_inclusion (hC hik)⟩ :
        C((C i : Set K), (C k : Set K))) := by
  rw  [← wordDiskInclusion_killsPi2_iff K C hC hik]
  apply Whitehead.killsPi2_homotopyEquiv_square_iff
    (collapsedDiskChange K C hC hconn i) (collapsedDiskChange K C hC hconn k)
  rw  [collapsedDiskChange_natural]

end FiniteChains.ClassicalCW.ChainWords
