module

public import RequestProject.GenusSpineComponent
public import RequestProject.BlockConnected

@[expose] public section

/-! The full surviving spine is connected. The paths use only the retained
vertices and edges, together with a downward edge from the starting cell.
Pending final Lean verification.
-/

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
open scoped Classical
variable (q : ℕ) [NeZero q]

noncomputable def spineSignVertex (ξ : GenusVertex q → ZMod 2) (hξ : ξ ≠ 0) : GenusSpineCell q :=
  ⟨Sum.inl (vtxCube ξ hξ), genusSpineCellSet_of_dimension_lt_two q _ (by
    simp [truncatedCellDimension, vtxCube])⟩

noncomputable def spineSignEdge (v : GenusVertex q) (ξ : GenusVertex q → ZMod 2) : GenusSpineCell q :=
  ⟨Sum.inl (oneCube v ξ), genusSpineCellSet_of_dimension_lt_two q _ (by
    simp [truncatedCellDimension, oneCube])⟩

theorem spineReach_refl (a : GenusSpineCell q) :
    Reach (orderCx (GenusSpineCell q)) a a := reach_self _ _

theorem spineReach_trans {a b c : GenusSpineCell q}
    (h : Reach (orderCx (GenusSpineCell q)) a b)
    (h' : Reach (orderCx (GenusSpineCell q)) b c) :
    Reach (orderCx (GenusSpineCell q)) a c := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨r, hr⟩ := h'
  exact ⟨p ++ r, hp.append hr⟩

theorem spineReach_le {a b : GenusSpineCell q} (h : a ≤ b) :
    Reach (orderCx (GenusSpineCell q)) a b := ⟨[ordPos h], isPath_ordPos h⟩

theorem spineReach_ge {a b : GenusSpineCell q} (h : b ≤ a) :
    Reach (orderCx (GenusSpineCell q)) a b := ⟨[ordNeg h], isPath_ordNeg h⟩

theorem spineSignVertex_flip (ξ : GenusVertex q → ZMod 2) (hξ : ξ ≠ 0)
    (v : GenusVertex q) (b : ZMod 2) (h' : Function.update ξ v b ≠ 0) :
    Reach (orderCx (GenusSpineCell q)) (spineSignVertex q ξ hξ)
      (spineSignVertex q (Function.update ξ v b) h') :=
  spineReach_trans q
    (spineReach_le q (b := spineSignEdge q v ξ) (vtxCube_le_oneCube hξ v))
    (spineReach_ge q (vtxCube_update_le_oneCube (ξ := ξ) v b h'))

/-- Sign changes stay inside the actual surviving one-skeleton. -/
theorem spineSignVertex_connected (v₀ : GenusVertex q)
    (ξ : GenusVertex q → ZMod 2) (hξ : ξ ≠ 0) :
    Reach (orderCx (GenusSpineCell q)) (spineSignVertex q ξ hξ)
      (spineSignVertex q (unitSgn v₀) (unitSgn_ne_zero v₀)) :=
  signVertex_connected (spineReach_refl q) (spineReach_trans q)
    (spineSignVertex q) (spineSignVertex_flip q) v₀ ξ hξ

/-- Every surviving cell reaches a retained sign vertex by genuine comparabilities. -/
theorem spineCell_to_signVertex (c : GenusSpineCell q) :
    ∃ (ξ : GenusVertex q → ZMod 2) (hξ : ξ ≠ 0),
      Reach (orderCx (GenusSpineCell q)) c (spineSignVertex q ξ hξ) := by
  obtain ⟨c, hc⟩ := c
  cases c with
  | inl c =>
      by_cases hs : c.1.spx = ∅
      · have hne  := fun h => c.2 ⟨hs, h⟩
        refine ⟨c.1.sgn, hne, ?_⟩
        have he : c = vtxCube c.1.sgn hne := by
          apply Subtype.ext
          exact QCube.ext' hs (fun _ _ => rfl)
        have hv : (⟨Sum.inl c, hc⟩ : GenusSpineCell q) = spineSignVertex q c.1.sgn hne :=
          Subtype.ext (congrArg Sum.inl he)
        tauto
      · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hs
        have hne : Function.update c.1.sgn v 1 ≠ 0 := by
          intro h
          simpa using congrFun h v
        refine ⟨Function.update c.1.sgn v 1, hne, spineReach_ge q ?_⟩
        change (vtxCube (Function.update c.1.sgn v 1) hne).1 ≤ c.1
        refine ⟨Finset.empty_subset _, fun w hw => ?_⟩
        have hwv : w ≠ v := fun h => hw (h ▸ hv)
        simp [vtxCube, hwv]
  | inr σ =>
      obtain ⟨v, hv⟩ := σ.2.1
      let s := spineCutSingleton q v
      let e := spineSignEdge q v 0
      have hsc : s ≤ ⟨Sum.inr σ, hc⟩ := by
        change ({v}) ⊆ σ.1
        exact Finset.singleton_subset_iff.mpr hv
      have hse : s ≤ e := by
        change ({v} : Finset (GenusVertex q)) ⊆ {v} ∧
          Function.update (0 : GenusVertex q → ZMod 2) v 0 = 0
        exact ⟨Finset.Subset.refl _, by funext w; simp⟩
      have hve : spineSignVertex q (unitSgn v) (unitSgn_ne_zero v) ≤ e := by
        change (vtxCube (unitSgn v) (unitSgn_ne_zero v)).1 ≤ (oneCube v 0).1
        refine ⟨Finset.empty_subset _, fun w hw => ?_⟩
        have hwv : w ≠ v := fun h => hw (by rw [h]; exact Finset.mem_singleton_self v)
        simp [vtxCube, oneCube, unitSgn, hwv]
      exact ⟨unitSgn v, unitSgn_ne_zero v,
        spineReach_trans q (spineReach_ge q hsc)
          (spineReach_trans q (spineReach_le q hse) (spineReach_ge q hve))⟩

theorem genusSpine_orderCx_isConnected : IsConnected (orderCx (GenusSpineCell q)) := by
  let v₀ := cV (gc q) (cyc (8 * q) 0)
  have hbase (c : GenusSpineCell q) : Reach (orderCx (GenusSpineCell q)) c
      (spineSignVertex q (unitSgn v₀) (unitSgn_ne_zero v₀)) := by
    obtain ⟨ξ, hξ, hc⟩ := spineCell_to_signVertex q c
    exact spineReach_trans q hc (spineSignVertex_connected q v₀ ξ hξ)
  intro a b
  obtain ⟨p, hp⟩ := hbase a
  obtain ⟨r, hr⟩ := hbase b
  exact ⟨p ++ revPath r, hp.append (isPath_revPath hr)⟩

theorem genusSpineCx_isConnected : IsConnected (genusSpineCx q) :=
  strictOrderCx_isConnected (genusSpine_orderCx_isConnected q)

theorem markedSpine_component_onF_surjective :
    Function.Surjective (componentIncl (genusSpineCx q) (spineBase q)).onF := by
  intro t
  exact ⟨⟨t, genusSpineCx_isConnected q (spineBase q) ((genusSpineCx q).base t)⟩, rfl⟩

end FiniteChains.Davis.Genus
