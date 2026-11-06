import Mathlib.Tactic

import RequestProject.QCubeThreeFacetCoordinates

/-! Integral coefficient calculation for the six oriented faces of an ordered three-cube.
The separate geometric comparison must identify this matrix with actual cube edge cells. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis

def fixedCoordinateSign (s : ZMod 2)  := if s = 0 then 1 else -1

variable (i : Fin 3 × ZMod 2)
noncomputable def threeFacetBoundaryColumn  :
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

noncomputable def threeFacetBoundaryMatrix  :=
  Finsupp.linearCombination ℤ threeFacetBoundaryColumn

set_option maxHeartbeats 1000000

variable (r : (Fin 3 × ZMod 2) →₀ ℤ)
theorem threeFacetBoundaryMatrix_row0  (s t : ZMod 2) :
    threeFacetBoundaryMatrix r (0, s, t) =
      -fixedCoordinateSign t * r (0, s) - fixedCoordinateSign s * r (1, t) := by
  classical
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r q hr hq => grind [Finsupp.add_apply]
  | single i n =>
      obtain ⟨e, u⟩ := i
      fin_cases e <;> fin_cases u <;> fin_cases s <;> fin_cases t <;>
        norm_num [threeFacetBoundaryMatrix, threeFacetBoundaryColumn, fixedCoordinateSign,
          Finsupp.single_apply, Prod.mk.injEq]

theorem threeFacetBoundaryMatrix_row1  (s t : ZMod 2) :
    threeFacetBoundaryMatrix r (1, s, t) =
      fixedCoordinateSign t * r (0, s) - fixedCoordinateSign s * r (2, t) := by
  classical
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r q hr hq => grind [Finsupp.add_apply]
  | single i n =>
      obtain ⟨e, u⟩ := i
      fin_cases e <;> fin_cases u <;> fin_cases s <;> fin_cases t <;>
        norm_num [threeFacetBoundaryMatrix, threeFacetBoundaryColumn, fixedCoordinateSign,
          Finsupp.single_apply, Prod.mk.injEq]

def threeFacetOrientation   :=
  (if i.1 = 1 then -1 else 1) * fixedCoordinateSign i.2

theorem threeFacetBoundaryMatrix_kernel 
    (hr : threeFacetBoundaryMatrix r = 0) :
    ∀ i, r i = r (0, 0) * threeFacetOrientation i := by
  have h00 := congrArg (fun z : (Fin 3 × ZMod 2 × ZMod 2) →₀ ℤ => z (0, 0, 0)) hr
  have h10 := congrArg (fun z : (Fin 3 × ZMod 2 × ZMod 2) →₀ ℤ => z (1, 0, 0)) hr
  have h01 := congrArg (fun z : (Fin 3 × ZMod 2 × ZMod 2) →₀ ℤ => z (0, 1, 0)) hr
  have h02 := congrArg (fun z : (Fin 3 × ZMod 2 × ZMod 2) →₀ ℤ => z (0, 0, 1)) hr
  have h12 := congrArg (fun z : (Fin 3 × ZMod 2 × ZMod 2) →₀ ℤ => z (1, 0, 1)) hr
  simp only [threeFacetBoundaryMatrix_row0, threeFacetBoundaryMatrix_row1,
    Finsupp.zero_apply] at h00 h10 h01 h02 h12
  norm_num [fixedCoordinateSign] at h00 h10 h01 h02 h12
  rintro ⟨e, s⟩
  fin_cases e
  · fin_cases s
    · change r (0, 0) = r (0, 0) * (1 : ℤ)
      norm_num
    · change r (0, 1) = r (0, 0) * (-1 : ℤ)
      norm_num
      omega
  · fin_cases s
    · change r (1, 0) = r (0, 0) * (-1 : ℤ)
      norm_num
      omega
    · change r (1, 1) = r (0, 0) * (1 : ℤ)
      norm_num
      omega
  · fin_cases s
    · change r (2, 0) = r (0, 0) * (1 : ℤ)
      norm_num
      omega
    · change r (2, 1) = r (0, 0) * (-1 : ℤ)
      norm_num
      omega

end FiniteChains.Davis
