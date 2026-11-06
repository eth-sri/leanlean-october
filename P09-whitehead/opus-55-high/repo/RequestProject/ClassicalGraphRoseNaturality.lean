import RequestProject.ClassicalGraphRose
import RequestProject.DiskFamilyMap


/-! Compatible spanning trees give an actual commuting graph-to-rose
square. The forward collapse is canonical on every characteristic
interval even though its homotopy inverse uses tree paths. Unverified. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment
variable {V W J K : Type} [TopologicalSpace V] [TopologicalSpace W]
  [DiscreteTopology V] [DiscreteTopology W]
  (r : BoundaryFamily J (Fin 1 → ℝ) → V) (hr : Continuous r)
  (s : BoundaryFamily K (Fin 1 → ℝ) → W) (hs : Continuous s)
  (T : Comb.SpanningTree (graphCx r)) (U : Comb.SpanningTree (graphCx s))
  (h : Comb.Hom (graphCx r) (graphCx s))
  (ht : ∀ j, U.isTree (h.onE j) ↔ T.isTree j)

def graphNonTreeMap : {j : J // ¬T.isTree j} → {k : K // ¬U.isTree k} :=
  fun j => ⟨h.onE j.val, by grind⟩

def graphRoseCombinatorialMap :
    Comb.Hom (graphCx (roseAttaching {j : J // ¬T.isTree j}))
      (graphCx (roseAttaching {k : K // ¬U.isTree k})) where
  onV := id
  onE := graphNonTreeMap r s T U h ht
  onF := Empty.elim
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF f := Empty.elim f
  att_onF f := Empty.elim f

def graphRoseMap : C(Rose {j : J // ¬T.isTree j}, Rose {k : K // ¬U.isTree k}) :=
  diskFamilyMap _ _ (ContinuousMap.id PUnit)
    (graphNonTreeMap r s T U h ht) (by simp)

theorem graphRoseHomotopyEquiv_natural (f : C(DiskAttachment r, DiskAttachment s))
    (hv : ∀ v, f (old r (boundaryFamilyInclusion J _) v) =
      old s (boundaryFamilyInclusion K _) (h.onV v))
    (he : ∀ j x, f (cell r (boundaryFamilyInclusion J _) ⟨j, x⟩) =
      cell s (boundaryFamilyInclusion K _) ⟨h.onE j, x⟩) :
    (graphRoseMap r s T U h ht).comp (graphRoseHomotopyEquiv r hr T).toFun =
      (graphRoseHomotopyEquiv s hs U).toFun.comp f := by
  apply hom_ext r _
  · intro v
    change graphRoseMap r s T U h ht (graphRoseHomotopyEquiv r hr T (old _ _ v)) =
      graphRoseHomotopyEquiv s hs U (f (old _ _ v))
    rw [graphRoseHomotopyEquiv_old, hv]
    rfl
  · rintro ⟨j, x⟩
    change graphRoseMap r s T U h ht (graphRoseHomotopyEquiv r hr T (cell _ _ ⟨j, x⟩)) =
      graphRoseHomotopyEquiv s hs U (f (cell _ _ ⟨j, x⟩))
    rw [he]
    by_cases hj : T.isTree j
    · have hk := (ht j).mpr hj
      rw [graphRoseHomotopyEquiv_treeCell r hr T ⟨⟨j, hj⟩, x⟩,
        graphRoseHomotopyEquiv_treeCell s hs U ⟨⟨h.onE j, hk⟩, x⟩]
      rfl
    · have hk : ¬U.isTree (h.onE j) := by simp_all
      rw [graphRoseHomotopyEquiv_nonTreeCell r hr T ⟨⟨j, hj⟩, x⟩,
        graphRoseHomotopyEquiv_nonTreeCell s hs U ⟨⟨h.onE j, hk⟩, x⟩]
      exact diskFamilyMap_cell _ _ _
        _ _ _ x
