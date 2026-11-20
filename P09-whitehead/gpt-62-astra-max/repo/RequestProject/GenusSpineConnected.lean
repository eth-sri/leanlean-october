module

public import RequestProject.GenusSpineComponent


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
    solve_by_elim)⟩

noncomputable def spineSignEdge (v : GenusVertex q) (ξ : GenusVertex q → ZMod 2) : GenusSpineCell q :=
  ⟨Sum.inl (oneCube v ξ), genusSpineCellSet_of_dimension_lt_two q _ (by
    solve_by_elim)⟩

theorem spineReach_refl (a : GenusSpineCell q) :
    Reach (orderCx (GenusSpineCell q)) a a := by solve_by_elim

theorem spineReach_trans {a b c : GenusSpineCell q}
    (h : Reach (orderCx (GenusSpineCell q)) a b)
    (h' : Reach (orderCx (GenusSpineCell q)) b c) :
    Reach (orderCx (GenusSpineCell q)) a c := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨r, hr⟩ := h'
  exact ⟨p ++ r, hp.append hr⟩

variable {a b : GenusSpineCell q}

theorem spineReach_le (h : a ≤ b) :
    Reach (orderCx (GenusSpineCell q)) a b := ⟨[ordPos h], isPath_ordPos h⟩

theorem spineReach_ge (h : b ≤ a) :
    Reach (orderCx (GenusSpineCell q)) a b := ⟨[ordNeg h], isPath_ordNeg h⟩

theorem spineSignVertex_flip (ξ : GenusVertex q → ZMod 2) (hξ : ξ ≠ 0)
    (v : GenusVertex q) (b : ZMod 2) (h' : Function.update ξ v b ≠ 0) :
    Reach (orderCx (GenusSpineCell q)) (spineSignVertex q ξ hξ)
      (spineSignVertex q (Function.update ξ v b) h') :=
  spineReach_trans q
    (spineReach_le q (b := spineSignEdge q v ξ) (vtxCube_le_oneCube hξ v))
    (spineReach_ge q (vtxCube_update_le_oneCube (ξ := ξ) v b h'))

variable (v₀ : GenusVertex q)

/-- Sign changes stay inside the actual surviving one-skeleton. -/
theorem spineSignVertex_to_unit :
    ∀ (n : ℕ) (ξ : GenusVertex q → ZMod 2) (hξ : ξ ≠ 0),
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
            by_contra hne
            solve_by_elim
          simp [unitSgn, hw, hz]
      subst ξ
      exact spineReach_refl q _
    · push_neg at hsupp
      obtain ⟨w, hw, hwv⟩ := hsupp
      let ξ' := Function.update ξ w 0
      have hξ'v₀ : ξ' v₀ = 1 := by
        simp only [ξ', Function.update_apply, if_neg (Ne.symm hwv), hv₀]
      have hξ'ne : ξ' ≠ 0 := by
        intro h
        simp_all
      have hsub : sgnSupport ξ' ⊂ sgnSupport ξ := by
        constructor
        · intro x hx
          rw [mem_sgnSupport] at hx ⊢
          by_cases hxw : x = w
          · simp_all
          · aesop
        · intro hle
          have hh := hle (mem_sgnSupport.2 hw)
          simp_all [mem_sgnSupport, ξ']
      have hlt : (sgnSupport ξ').card < n := by
        rw [← hcard]
        exact Finset.card_lt_card hsub
      exact spineReach_trans q (spineSignVertex_flip q ξ hξ w 0 hξ'ne)
        (ih _ hlt ξ' hξ'ne hξ'v₀ rfl)

theorem spineSignVertex_connected
    (ξ : GenusVertex q → ZMod 2) (hξ : ξ ≠ 0) :
    Reach (orderCx (GenusSpineCell q)) (spineSignVertex q ξ hξ)
      (spineSignVertex q (unitSgn v₀) (unitSgn_ne_zero v₀)) := by
  let ξ' := Function.update ξ v₀ 1
  have hv₀ : ξ' v₀ = 1 := by simp [ξ']
  have hξ' : ξ' ≠ 0 := by
    intro h
    simp_all
  exact spineReach_trans q (spineSignVertex_flip q ξ hξ v₀ 1 hξ')
    (spineSignVertex_to_unit q v₀ _ ξ' hξ' hv₀ rfl)

/-- Every surviving cell reaches a retained sign vertex by genuine comparabilities. -/
theorem spineCell_to_signVertex (c : GenusSpineCell q) :
    ∃ (ξ : GenusVertex q → ZMod 2) (hξ : ξ ≠ 0),
      Reach (orderCx (GenusSpineCell q)) c (spineSignVertex q ξ hξ) := by
  obtain ⟨c, hc⟩ := c
  cases c with
  | inl c =>
      by_cases hs : c.1.spx = ∅
      · have hne := fun h => c.2 ⟨hs, h⟩
        refine ⟨c.1.sgn, hne, ?_⟩
        have he : c = vtxCube _ hne := by
          apply Subtype.ext
          solve_by_elim [QCube.ext']
        have hv : (⟨Sum.inl c, hc⟩) = spineSignVertex q _ hne :=
          Subtype.ext (congrArg Sum.inl he)
        solve_by_elim
      · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hs
        have hne : Function.update c.1.sgn v 1 ≠ 0 := by
          intro h
          simpa using congrFun h v
        refine ⟨Function.update _ v 1, hne, spineReach_ge q ?_⟩
        refine ⟨Finset.empty_subset _, fun w hw => ?_⟩; have hwv : w ≠ v := fun h => hw (h ▸ hv); simp [vtxCube, hwv]
  | inr σ =>
      obtain ⟨v, hv⟩ := σ.2.1
      let s := spineCutSingleton q v
      let e := spineSignEdge q v 0
      have hsc : s ≤ (⟨Sum.inr σ, hc⟩) := Finset.singleton_subset_iff.mpr hv
      have hse : s ≤ e := by
        change ({v} : Finset _) ⊆ {v} ∧
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
  let v₀ := cV (gc q) (cyc (8 * q) 0)
  have hbase (c : GenusSpineCell q) : Reach (orderCx (GenusSpineCell q)) c
      (spineSignVertex q (unitSgn v₀) (unitSgn_ne_zero v₀)) := by
    obtain ⟨ξ, hξ, hc⟩ := spineCell_to_signVertex q c
    solve_by_elim [spineReach_trans, spineSignVertex_connected]
  intro a b
  obtain ⟨p, hp⟩ := hbase a
  obtain ⟨r, hr⟩ := hbase b
  exact ⟨p ++ revPath r, hp.append (isPath_revPath hr)⟩

theorem genusSpineCx_isConnected : IsConnected (genusSpineCx q) :=
  strictOrderCx_isConnected (genusSpine_orderCx_isConnected q)

theorem markedSpine_component_onF_surjective :
    Function.Surjective (componentIncl (genusSpineCx q) (spineBase q)).onF := by
  intro t
  solve_by_elim [genusSpineCx_isConnected]

end FiniteChains.Davis.Genus
