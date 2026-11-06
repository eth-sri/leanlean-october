import RequestProject.QCubeThreeFacetCoordinates
import RequestProject.Tac
noncomputable section


/-! Integral coefficient calculation for the six oriented faces of an ordered three-cube.
The separate geometric comparison must identify this matrix with actual cube edge cells. -/
bwd

namespace FiniteChains.Davis

def fixedCoordinateSign (s : ZMod 2) := if s = 0 then 1 else -1

def threeFacetBoundaryColumn (i : Fin 3 × ZMod 2) :
    (Fin 3 × ZMod 2 × ZMod 2) →₀ ℤ :=
  if i.1 = 0 then
    -Finsupp.single (0, i.2, 0) 1 + Finsupp.single (0, i.2, 1) 1 +
      Finsupp.single (1, i.2, 0) 1 - Finsupp.single (1, i.2, 1) 1
  else if i.1 = 1 then
    -Finsupp.single (0, 0, i.2) 1 + Finsupp.single (0, 1, i.2) 1 +
      Finsupp.single (2, i.2, 0) 1 - Finsupp.single (2, i.2, 1) 1
  else
    -Finsupp.single (1, 0, i.2) 1 + Finsupp.single (1, 1, i.2) 1 +
      Finsupp.single (2, 0, i.2) 1 - Finsupp.single (2, 1, i.2) 1

def threeFacetBoundaryMatrix : ((Fin 3 × ZMod 2) →₀ ℤ) →ₗ[ℤ]
    ((Fin 3 × ZMod 2 × ZMod 2) →₀ ℤ) :=
  Finsupp.linearCombination ℤ threeFacetBoundaryColumn

set_option maxHeartbeats 1000000

theorem threeFacetBoundaryMatrix_row0 r s t :
    threeFacetBoundaryMatrix r (0, s, t) =
      -fixedCoordinateSign t * r (0, s) - fixedCoordinateSign s * r (1, t) := by
  classical
  lin_ind r with r q hr hq => simp [map_add, Finsupp.add_apply, hr, hq]; ring
  | i n =>
      obtain ⟨e, u⟩ := i
      fin_cases e <;> fin_cases u <;> fin_cases s <;> fin_cases t <;>
        norm_num [threeFacetBoundaryMatrix, threeFacetBoundaryColumn, fixedCoordinateSign,
          Finsupp.single_apply, Prod.mk.injEq]

theorem threeFacetBoundaryMatrix_row1 r s t :
    threeFacetBoundaryMatrix r (1, s, t) =
      fixedCoordinateSign t * r (0, s) - fixedCoordinateSign s * r (2, t) := by
  classical
  lin_ind r with r q hr hq => simp [map_add, Finsupp.add_apply, hr, hq]; ring
  | i n =>
      obtain ⟨e, u⟩ := i
      fin_cases e <;> fin_cases u <;> fin_cases s <;> fin_cases t <;>
        norm_num [threeFacetBoundaryMatrix, threeFacetBoundaryColumn, fixedCoordinateSign,
          Finsupp.single_apply, Prod.mk.injEq]

def threeFacetOrientation (i : Fin 3 × ZMod 2) :=
  (if i.1 = 1 then -1 else 1) * fixedCoordinateSign i.2

theorem threeFacetBoundaryMatrix_kernel r
    (hr : threeFacetBoundaryMatrix r = 0) :
    ∀ i, r i = r (0, 0) * threeFacetOrientation i := by
  have h00 := congrArg (· (0, 0, 0)) hr
  have h10 := congrArg (· (1, 0, 0)) hr
  have h01 := congrArg (· (0, 1, 0)) hr
  have h02 := congrArg (· (0, 0, 1)) hr
  have h12 := congrArg (· (1, 0, 1)) hr
  simp [threeFacetBoundaryMatrix_row0, threeFacetBoundaryMatrix_row1,
    Finsupp.zero_apply] at h00 h10 h01 h02 h12
  norm_num [fixedCoordinateSign] at h00 h10 h01 h02 h12
  rintro ⟨e, s⟩
  fin_cases e
  · fin_cases s
    · change r (0, 0) = r (0, 0) * (1)
      norm_num
    · change r (0, 1) = r (0, 0) * (-1)
      norm_num
      omega
  · fin_cases s
    · change r (1, 0) = r (0, 0) * (-1)
      norm_num
      omega
    · change r (1, 1) = r (0, 0) * (1)
      norm_num
      omega
  · fin_cases s
    · change r (2, 0) = r (0, 0) * (1)
      norm_num
      omega
    · change r (2, 1) = r (0, 0) * (-1)
      norm_num
      omega
