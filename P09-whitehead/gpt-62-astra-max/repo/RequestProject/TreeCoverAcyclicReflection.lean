module

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
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp_all
  | single a n =>
      rcases a with ⟨q, e⟩
      rw [sectionE, Finsupp.linearCombination_single, map_smul, piE_pathChain_liftK]
      rw [pathChain_liftPath_congr (N := N) ((mk_letters (loopPath T e)).trans (pathWord_loopPath e))]
      simp [liftPath_cons_true, pathChain_cons, pathChain_nil]

omit [N.Normal] [DecidableEq _] in
theorem piV_iotaV (z : CovQ T N →₀ ℤ) : piV T N (iotaV T N z) = z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp_all
  | single q n => simp

theorem coverComplex_isAcyclic_of_treeCover
    (h : IsAcyclic (treeCover T N hN)) : IsAcyclic (coverComplex N (treeRel T) hN) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    apply h.h2
    apply piE_injective_of_same_boundary T N hN
    · simp [bdry1_bdry2]
    · simp_all [piE_bdry2]
  · intro z hz
    have hlift : bdry1 (treeCover T N hN) (sectionE T N z) = 0 := by
      simp_all [bdry1_sectionE]
    obtain ⟨a, ha⟩ := h.h1 _ hlift
    exact ⟨a, by rw [← piE_bdry2 (hN := hN), ha, piE_sectionE]⟩
  · intro z hz
    have hlift : augC (treeCover T N hN) (iotaV T N z) = 0 := by
      rw [← augC_piV (hN := hN), piV_iotaV, hz]
    obtain ⟨a, ha⟩ := h.h0 _ hlift
    exact ⟨piE T N a, by rw [← piV_bdry1 (hN := hN), ha, piV_iotaV]⟩

end FiniteChains.Comb.SpanningTree
