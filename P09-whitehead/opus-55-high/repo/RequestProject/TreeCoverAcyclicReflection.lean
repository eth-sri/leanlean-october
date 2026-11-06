import RequestProject.TreeCoverRelativeBoundary
import RequestProject.Tac


/-! The converse homology comparison for spanning-tree collapse.
No finiteness assumption on the original cells or cover is used.
Pending final Lean verification. -/

noncomputable section
bwd

namespace FiniteChains.Comb.SpanningTree
universe u
variable {K : Complex2.{u}} (T : SpanningTree K)
  (N : Subgroup (FreeGroup (NonTree T))) [N.Normal]
  [DecidableEq (NonTree T)] (hN : ∀ f, treeRel T f ∈ N)

theorem piE_sectionE z :
    piE T N (sectionE T N z) = z := by
  classical
  lin_ind z a n =>
      cases' a with q e
      rw [sectionE, Finsupp.linearCombination_single, map_smul, piE_pathChain_liftK]
      have hl :=
        (mk_letters _).trans (pathWord_loopPath e)
      rw [pathChain_liftPath_congr (T := T) (N := N) hl]
      simp [liftPath_cons_true, pathChain_cons, pathChain_nil]

omit [N.Normal] [DecidableEq (NonTree T)] in
theorem piV_iotaV (z : CovQ T N →₀ ℤ) : piV T N (iotaV T N z) = z := by
  induction z using Finsupp.induction_linear <;> simp_all

theorem coverComplex_isAcyclic_of_treeCover
    (h : IsAcyclic (treeCover T N hN)) : IsAcyclic (coverComplex N (treeRel T) hN) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    apply h.h2
    apply piE_injective_of_same_boundary T N hN
    · grind [bdry1_bdry2]
    · simp [piE_bdry2 (hN := hN), hab]
  · intro z hz
    have hlift : bdry1 (treeCover T N hN) (sectionE T N z) = 0 := by
      rw [bdry1_sectionE (hN := hN), hz, map_zero]
    cases' h.h1 _ hlift with a ha
    exact ⟨a, by rw [← piE_bdry2 (hN := hN), ha, piE_sectionE]⟩
  · intro z hz
    have hlift : augC (treeCover T N hN) (iotaV T N z) = 0 := by
      rw [← augC_piV (hN := hN), piV_iotaV, hz]
    cases' h.h0 _ hlift with a ha
    exact ⟨piE T N a, by rw [← piV_bdry1 (hN := hN), ha, piV_iotaV]⟩
