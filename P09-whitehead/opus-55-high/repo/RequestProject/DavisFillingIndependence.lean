import RequestProject.DavisUniversalThree
import RequestProject.UniversalThreeAugmentation


/-! Independence of actual universal-cover fillings modulo three-boundaries. -/
namespace FiniteChains.Davis
open RACG Comb
variable {V : Type u} [DecidableEq V] [Fintype V]

/-- Two fillings of the same cover chain differ by an actual lifted three-boundary. -/
theorem fillings_difference_boundary3 (A : CommRel V) (b : QCube A)
    c d
    (h : Comb.bdry2 (uCover (orderCx (QCube A)) b) c =
      Comb.bdry2 (uCover (orderCx (QCube A)) b) d) :
    ∃ y, uOrdBoundary3 y = c - d := by
  apply exists_universal_bdry3_of_cycle_qCube A b
  simp_all

/-- Projected fillings of the same lifted boundary differ by an ordinary three-boundary. -/
theorem projected_fillings_difference_boundary3 (A : CommRel V) (b : QCube A)
    c d
    (h : Comb.bdry2 (uCover (orderCx (QCube A)) b) c =
      Comb.bdry2 (uCover (orderCx (QCube A)) b) d) :
    ∃ y,
      ordBoundary3 y = hurewicz (orderCx (QCube A)) b c -
        hurewicz (orderCx (QCube A)) b d := by
  cases' fillings_difference_boundary3 A b c d h with y hy
  refine ⟨Finsupp.mapDomain (·.1.2) y, ?_⟩
  rw [← hurewicz_uOrdBoundary3, hy, map_sub]
