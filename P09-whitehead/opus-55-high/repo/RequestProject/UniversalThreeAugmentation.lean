import RequestProject.OrderUniversalThree
import RequestProject.CombPi2
import RequestProject.Tac


/-! Forgetting the deck coordinate of the actual lifted three-boundary. -/
bwd

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] (a : P)

theorem hurewicz_uOrdTetBoundary t :
    hurewicz (orderCx P) a (uOrdTetBoundary t) = ordTetBoundary t.1.2 := by
  have hs (c d : UF (orderCx P) a →₀ ℤ) :
      Finsupp.mapDomain (univProj (orderCx P) a).onF (c - d) =
        Finsupp.mapDomain (univProj (orderCx P) a).onF c -
          Finsupp.mapDomain (univProj (orderCx P) a).onF d :=
    (Finsupp.lmapDomain ℤ ℤ (univProj (orderCx P) a).onF).map_sub c d
  change Finsupp.mapDomain (univProj (orderCx P) a).onF (uOrdTetBoundary t) = _
  simp [uOrdTetBoundary, hs, Finsupp.mapDomain_add, Finsupp.mapDomain_single]
  rfl

/-- Augmentation commutes with the actual degree-three cellular boundary. -/
theorem hurewicz_uOrdBoundary3 c :
    hurewicz (orderCx P) a (uOrdBoundary3 c) =
      ordBoundary3 (Finsupp.mapDomain (·.1.2) c) := by
  lin_ind c with c d hc hd => simp [map_add, hc, hd, Finsupp.mapDomain_add]
  | t n =>
      rw [uOrdBoundary3, Finsupp.linearCombination_single, map_smul,
        hurewicz_uOrdTetBoundary, Finsupp.mapDomain_single, ordBoundary3,
        Finsupp.linearCombination_single]
