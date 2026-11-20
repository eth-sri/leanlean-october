module

public import RequestProject.FinsuppBasis

public import RequestProject.TreeCoverRelativeBoundary

@[expose] public section

/-! The converse homology comparison for spanning-tree collapse.
No finiteness assumption on the original cells or cover is used.
Pending final Lean verification. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb.SpanningTree
universe u
variable {K : Complex2.{u}} (T : SpanningTree K)
  (N : Subgroup (FreeGroup (NonTree T))) [N.Normal]
  [DecidableEq (NonTree T)] (hN : ∀ f, treeRel T f ∈ N)

theorem piE_sectionE (z : (CovQ T N × NonTree T) →₀ ℤ) :
    piE T N (sectionE T N z) = z := by
  classical
  finsupp_basis z
  intro a
  rcases a with ⟨q, e⟩
  rw [sectionE, Finsupp.linearCombination_single, map_smul, piE_pathChain_liftK]
  have hl  :=
    (mk_letters (loopPath T e)).trans (pathWord_loopPath e)
  rw [pathChain_liftPath_congr (T := T) (N := N) hl]
  simp [liftPath_cons_true, PathVoltage.liftPath, pathChain_cons]

omit [N.Normal] [DecidableEq (NonTree T)] in
theorem piV_iotaV (z : CovQ T N →₀ ℤ) : piV T N (iotaV T N z) = z := by
  finsupp_singles z
  intro q n
  simp

theorem coverComplex_isAcyclic_of_treeCover
    (h : IsAcyclic (treeCover T N hN)) : IsAcyclic (coverComplex N (treeRel T) hN) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    apply h.h2
    apply piE_injective_of_same_boundary T N hN
    · rw [bdry1_bdry2, bdry1_bdry2]
    · rw [piE_bdry2 (hN := hN), piE_bdry2 (hN := hN), hab]
  · intro z hz
    have hlift : bdry1 (treeCover T N hN) (sectionE T N z) = 0 := by
      rw [bdry1_sectionE (hN := hN), hz, map_zero]
    obtain ⟨a, ha⟩ := h.h1 (sectionE T N z) hlift
    exact ⟨a, by rw [← piE_bdry2 (hN := hN), ha, piE_sectionE]⟩
  · intro z hz
    have hlift : augC (treeCover T N hN) (iotaV T N z) = 0 := by
      rw [← augC_piV (hN := hN), piV_iotaV, hz]
    obtain ⟨a, ha⟩ := h.h0 (iotaV T N z) hlift
    exact ⟨piE T N a, by rw [← piV_bdry1 (hN := hN), ha, piV_iotaV]⟩

end FiniteChains.Comb.SpanningTree
