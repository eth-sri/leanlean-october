import RequestProject.GenusSpineComponent
import RequestProject.BlockConnected
noncomputable section


/-! The full surviving spine is connected. The paths use only the retained
vertices and edges, together with a downward edge from the starting cell.
Pending final Lean verification.
-/

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
open scoped Classical
variable (q : ℕ) [NeZero q]

def spineSignVertex (ξ : GenusVertex q → ZMod 2) (hξ : ξ ≠ 0) : GenusSpineCell q :=
  ⟨Sum.inl (vtxCube ξ hξ), genusSpineCellSet_of_dimension_lt_two q _ (by tauto)⟩

def spineSignEdge (v : GenusVertex q) (ξ : GenusVertex q → ZMod 2) : GenusSpineCell q :=
  ⟨Sum.inl (oneCube v ξ), genusSpineCellSet_of_dimension_lt_two q _ (by tauto)⟩


theorem spineReach_trans {a b c : GenusSpineCell q}
    (h : Reach (orderCx (GenusSpineCell q)) a b)
    (h' : Reach (orderCx (GenusSpineCell q)) b c) :
    Reach (orderCx (GenusSpineCell q)) a c := by
  cases' h with p hp
  cases' h' with r hr
  exact ⟨p ++ r, hp.append hr⟩

theorem spineReach_le {a b : GenusSpineCell q} (h : a ≤ b) :
    Reach (orderCx (GenusSpineCell q)) a b := ⟨[ordPos h], isPath_ordPos h⟩

theorem spineReach_ge {a b : GenusSpineCell q} (h : b ≤ a) :
    Reach (orderCx (GenusSpineCell q)) a b := ⟨[ordNeg h], isPath_ordNeg h⟩

theorem spineSignVertex_flip (ξ : GenusVertex q → ZMod 2) (hξ : ξ ≠ 0)
    v b (h' : Function.update ξ v b ≠ 0) :
    Reach (orderCx (GenusSpineCell q)) (spineSignVertex q ξ hξ)
      (spineSignVertex q (Function.update ξ v b) h') :=
  spineReach_trans q
    (spineReach_le q (b := spineSignEdge q v ξ) (vtxCube_le_oneCube hξ v))
    (spineReach_ge q (vtxCube_update_le_oneCube (ξ := ξ) v b h'))

/-- Sign changes stay inside the actual surviving one-skeleton. -/
theorem spineSignVertex_to_unit v₀ :
    ∀ n ξ hξ,
      ξ v₀ = 1 → (sgnSupport ξ).card = n →
      Reach (orderCx (GenusSpineCell q)) (spineSignVertex q ξ hξ)
        (spineSignVertex q (unitSgn v₀) (unitSgn_ne_zero v₀)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ξ hξ hv₀ hcard
    by_cases hsupp : ∀ w, ξ w ≠ 0 → w = v₀
    · have hxi : ξ = unitSgn v₀ := by
        funext w
        by_cases hw : w = v₀
        · subst w
          simp [unitSgn, hv₀]
        · have hz : ξ w = 0 := by
            grind
          simp [unitSgn, hw, hz]
      subst ξ
      tauto
    · push_neg at hsupp
      obtain ⟨w, hw, hwv⟩ := hsupp
      let ξ' := Function.update ξ w 0
      have hξ'v₀ : ξ' v₀ = 1 := by
        grind
      have hξ'ne : ξ' ≠ 0 := by
        aesop
      have hsub : sgnSupport ξ' ⊂ sgnSupport ξ := by
        constructor
        · grind [mem_sgnSupport]
        · intro hle
          have hh := hle (mem_sgnSupport.2 hw)
          simp_all [mem_sgnSupport, ξ']
      have hlt : (sgnSupport ξ').card < n := by
        rw [← hcard]
        exact Finset.card_lt_card hsub
      exact spineReach_trans q (spineSignVertex_flip q ξ hξ w 0 hξ'ne)
        (by tauto)

theorem spineSignVertex_connected v₀
    ξ hξ :
    Reach (orderCx (GenusSpineCell q)) (spineSignVertex q ξ hξ)
      (spineSignVertex q (unitSgn v₀) (unitSgn_ne_zero v₀)) := by
  let ξ' := Function.update ξ v₀ 1
  have hv₀ : ξ' v₀ = 1 := by grind
  have hξ' : ξ' ≠ 0 := by
    intro h
    simp_all
  exact spineReach_trans q (spineSignVertex_flip q ξ hξ v₀ 1 hξ')
    (spineSignVertex_to_unit q v₀ _ ξ' hξ' hv₀ rfl)

/-- Every surviving cell reaches a retained sign vertex by genuine comparabilities. -/
theorem spineCell_to_signVertex (c : GenusSpineCell q) :
    ∃ (ξ : GenusVertex q → ZMod 2) (hξ : ξ ≠ 0),
      Reach (orderCx (GenusSpineCell q)) c (spineSignVertex q ξ hξ) := by
  cases' c with c hc
  cases c with
  | inl c =>
      by_cases hs : c.1.spx = ∅
      · have hne : c.1.sgn ≠ 0 := by grind
        refine ⟨c.1.sgn, hne, ?_⟩
        have he : c = vtxCube c.1.sgn hne := by
          apply Subtype.ext
          exact QCube.ext' hs (fun _ _ => rfl)
        have hv : ⟨Sum.inl c, hc⟩ = spineSignVertex q c.1.sgn hne :=
          Subtype.ext (congrArg Sum.inl he)
        tauto
      · cases' Finset.nonempty_iff_ne_empty.mpr hs with v hv
        have hne : Function.update c.1.sgn v 1 ≠ 0 := by
          intro h
          simpa using congrFun h v
        refine ⟨Function.update c.1.sgn v 1, hne, spineReach_ge q ?_⟩
        refine ⟨Finset.empty_subset _, fun w hw => ?_⟩
        have hwv : w ≠ v := by grind
        simp [vtxCube, hwv]
  | inr σ =>
      cases' σ.2.1 with v hv
      let s := spineCutSingleton q v
      let e := spineSignEdge q v 0
      have hsc := Finset.singleton_subset_iff.mpr hv
      have hse : s ≤ e := by
        change ({v} : Finset (GenusVertex q)) ⊆ {v} ∧
          Function.update (0 : GenusVertex q → ZMod 2) v 0 = 0
        simp
      have hve : spineSignVertex q _ (unitSgn_ne_zero v) ≤ e := by
        refine ⟨Finset.empty_subset _, fun w hw => ?_⟩
        have hwv : w ≠ v := fun h => hw (by rw [h]; exact Finset.mem_singleton_self v)
        simp [vtxCube, oneCube, unitSgn, hwv]
      exact ⟨unitSgn v, unitSgn_ne_zero v,
        spineReach_trans q (spineReach_ge q hsc)
          (spineReach_trans q (spineReach_le q hse) (spineReach_ge q hve))⟩

theorem genusSpine_orderCx_isConnected : IsConnected (orderCx (GenusSpineCell q)) := by
  let v₀ := cV (gc q) (cyc _ 0)
  have hbase (c : GenusSpineCell q) : Reach (orderCx (GenusSpineCell q)) c
      (spineSignVertex q _ (unitSgn_ne_zero v₀)) := by
    obtain ⟨ξ, hξ, hc⟩ := spineCell_to_signVertex q c
    exact spineReach_trans q hc (spineSignVertex_connected q v₀ ξ hξ)
  intro a b
  cases' hbase a with p hp
  cases' hbase b with r hr
  exact ⟨p ++ revPath r, hp.append (isPath_revPath hr)⟩

theorem genusSpineCx_isConnected : IsConnected (genusSpineCx q) :=
  strictOrderCx_isConnected (genusSpine_orderCx_isConnected q)

theorem markedSpine_component_onF_surjective :
    Function.Surjective (componentIncl (genusSpineCx q) (spineBase q)).onF := by
  intro t
  exact ⟨⟨t, genusSpineCx_isConnected q _ _⟩, rfl⟩
