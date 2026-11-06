module

public import RequestProject.DavisNerveCover
public import RequestProject.DavisCellularAcyclic
public import RequestProject.OrderUniversalThree

@[expose] public section

/-! Full-nerve degree-two exactness for the actual path-class universal cover of the cube quotient. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type u} [DecidableEq V] [Fintype V]

/-- Degree-two exactness in the actual path-class universal cover, retaining its full
 three-cell boundary. No desired asphericity or homology premise is assumed. -/
theorem exists_universal_bdry3_of_cycle_davis (A : CommRel V) (a : Sph A)
    (z : UF (orderCx (QCube A)) (qProjCube a) →₀ ℤ)
    (hz : Comb.bdry2 (uCover (orderCx (QCube A)) (qProjCube a)) z = 0) :
    ∃ y : UOrdTet (QCube A) (qProjCube a) →₀ ℤ, uOrdBoundary3 y = z :=
  exists_uOrdBoundary3_of_cover_exact qProjCube_isPosetCover a
    (isConnected_davis A) (simplyConnected_davis A)
    (exists_cellular_bdry3_of_cycle_davis A) z hz

/-- The same exactness at every base vertex of the quotient. -/
theorem exists_universal_bdry3_of_cycle_qCube (A : CommRel V) (b : QCube A)
    (z : UF (orderCx (QCube A)) b →₀ ℤ)
    (hz : Comb.bdry2 (uCover (orderCx (QCube A)) b) z = 0) :
    ∃ y : UOrdTet (QCube A) b →₀ ℤ, uOrdBoundary3 y = z := by
  obtain ⟨a, rfl⟩ := qProjCube_isPosetCover.surj b
  exact exists_universal_bdry3_of_cycle_davis A a z hz

end FiniteChains.Davis
