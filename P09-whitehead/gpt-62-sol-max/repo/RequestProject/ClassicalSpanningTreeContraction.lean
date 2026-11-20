module

public import RequestProject.ClassicalGraphContraction
public import Mathlib.Topology.Homotopy.Contractible

@[expose] public section

/-! A genuine continuous contraction of the disk realization of an arbitrary
spanning tree. Only each vertex's natural-number height is finite. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment
open scoped unitInterval Topology Classical

variable {V J : Type} [TopologicalSpace V]
  (r : BoundaryFamily J (Fin 1 → ℝ) → V) (T : Comb.SpanningTree (graphCx r))

def treeAttaching : BoundaryFamily {j : J // T.isTree j} (Fin 1 → ℝ) → V :=
  fun a => r ⟨a.1.val, a.2⟩

abbrev TreeSpace := DiskAttachment (treeAttaching r T)

def treeVertex (a : V) : TreeSpace r T :=
  old (treeAttaching r T) (boundaryFamilyInclusion {j : J // T.isTree j} _) a

def treeUpPath (a : V) (ha : a ≠ T.root) :
    Path (treeVertex r T a) (treeVertex r T (T.parent a ha)) :=
  (graphGermPath (treeAttaching r T)
    (⟨(T.up a ha).1, T.isTree_up ha⟩, (T.up a ha).2)).cast
      (congrArg (treeVertex r T) (T.up_src a ha).symm) rfl

/-- Follow the finitely many chosen parent edges to the root. -/
def treeRootPath (a : V) : Path (treeVertex r T a) (treeVertex r T T.root) :=
  if ha : a = T.root then
    (Path.refl (treeVertex r T T.root)).cast (congrArg (treeVertex r T) ha) rfl
  else (treeUpPath r T a ha).trans (treeRootPath (T.parent a ha))
  termination_by T.ht a
  decreasing_by
    have h := T.ht_parent ha
    omega


theorem treeRootPath_of_ne {a : V} (ha : a ≠ T.root) :
    treeRootPath r T a = (treeUpPath r T a ha).trans (treeRootPath r T (T.parent a ha)) := by
  rw [treeRootPath]
  simp only [dif_neg ha]

/-- Every retained edge is a chosen parent edge, so the actual vertex paths
have precisely the compatibility used by the cellwise contraction. -/
theorem treeRootPath_edge (j : {j : J // T.isTree j}) :
    treeRootPath r T (graphSrc (treeAttaching r T) j) =
      (graphEdgePath (treeAttaching r T) j).trans
        (treeRootPath r T (graphTgt (treeAttaching r T) j)) ∨
    treeRootPath r T (graphTgt (treeAttaching r T) j) =
      (graphEdgePath (treeAttaching r T) j).symm.trans
        (treeRootPath r T (graphSrc (treeAttaching r T) j)) := by
  obtain ⟨a, ha, he⟩ := (T.isTree_iff j.val).mp j.property
  generalize hb : (T.up a ha).2 = b
  have hg : T.up a ha = (j.val, b) := Prod.ext he hb
  have hp : (⟨(T.up a ha).1, T.isTree_up ha⟩, (T.up a ha).2) = (j, b) :=
    Prod.ext (Subtype.ext he) hb
  let s := Comb.germSrc (graphSrc (treeAttaching r T)) (graphTgt (treeAttaching r T)) (j, b)
  let t := Comb.germTgt (graphSrc (treeAttaching r T)) (graphTgt (treeAttaching r T)) (j, b)
  have hs : a = s := by rw [← T.up_src a ha, hg]; rfl
  have ht : T.parent a ha = t := by rw [Comb.SpanningTree.parent, hg]; rfl
  have h : treeRootPath r T s =
      (graphGermPath (treeAttaching r T) (j, b)).trans (treeRootPath r T t) := by
    apply Path.ext
    funext u
    have hu := congrArg (fun p => p u) (treeRootPath_of_ne r T ha)
    calc
      treeRootPath r T s u = treeRootPath r T a u :=
        congrArg (fun v => treeRootPath r T v u) hs.symm
      _ = _ := hu
      _ = _ := by
        simp only [Path.trans_apply, treeUpPath, Path.cast_coe]
        split_ifs
        · exact congrArg (fun e => graphGermPath (treeAttaching r T) e _) hp
        · exact congrArg (fun v => treeRootPath r T v _) ht
  cases b
  · exact Or.inr h
  · exact Or.inl h

variable [DiscreteTopology V]

/-- The actual spanning-tree disk attachment is contracted to its literal
old root vertex. The entire tree may have arbitrarily many edges. -/
def treeContraction : ContinuousMap.Homotopy (ContinuousMap.id (TreeSpace r T))
    (ContinuousMap.const (TreeSpace r T) (treeVertex r T T.root)) :=
  graphContraction (treeAttaching r T) T.root (treeRootPath r T) (treeRootPath_edge r T)



/-- The same specified collapse, with the universe-polymorphic singleton. -/
def treeHomotopyEquivPUnit : ContinuousMap.HomotopyEquiv (TreeSpace r T) PUnit where
  toFun := ContinuousMap.const _ PUnit.unit
  invFun := ContinuousMap.const _ (treeVertex r T T.root)
  left_inv := ⟨(treeContraction r T).symm⟩
  right_inv := by
    have he : (ContinuousMap.const PUnit PUnit.unit) = ContinuousMap.id PUnit := by
      ext x
    change ContinuousMap.Homotopic (ContinuousMap.const PUnit PUnit.unit) (ContinuousMap.id PUnit)
    rw [he]

end FiniteChains.ClassicalGraphModel
