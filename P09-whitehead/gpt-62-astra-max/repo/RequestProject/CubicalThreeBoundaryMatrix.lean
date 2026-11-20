module

public import RequestProject.QCubeFacetIndex

@[expose] public section

/-! Integral coefficient calculation for the six oriented faces of an ordered three-cube.
The separate geometric comparison must identify this matrix with actual cube edge cells. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis

def fixedCoordinateSign (s : ZMod 2) := if s = 0 then 1 else -1

def smallEdgeIndex (i : Fin 3 × ZMod 2) (t : ZMod 2) : Fin 3 × ZMod 2 × ZMod 2 :=
  if i.1 = 0 then (1, i.2, t) else if i.1 = 1 then (2, i.2, t) else (2, t, i.2)

def largeEdgeIndex (i : Fin 3 × ZMod 2) (t : ZMod 2) : Fin 3 × ZMod 2 × ZMod 2 :=
  if i.1 = 0 then (0, i.2, t) else if i.1 = 1 then (0, t, i.2) else (1, t, i.2)

noncomputable def threeFacetBoundaryColumn (i : Fin 3 × ZMod 2) : (Fin 3 × ZMod 2 × ZMod 2) →₀ ℤ :=
  Finsupp.single (smallEdgeIndex i 0) 1 - Finsupp.single (smallEdgeIndex i 1) 1 -
    Finsupp.single (largeEdgeIndex i 0) 1 + Finsupp.single (largeEdgeIndex i 1) 1

noncomputable def threeFacetBoundaryMatrix :=
  Finsupp.linearCombination ℤ threeFacetBoundaryColumn

variable (r : (Fin 3 × ZMod 2) →₀ ℤ) (s t : ZMod 2)

theorem threeFacetBoundaryMatrix_row0 :
    threeFacetBoundaryMatrix r (0, s, t) =
      -fixedCoordinateSign t * r (0, s) - fixedCoordinateSign s * r (1, t) := by
  classical
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r q hr hq => simp only [map_add, Finsupp.add_apply, hr, hq]; ring
  | single i n =>
      obtain ⟨e, u⟩ := i
      fin_cases e <;> fin_cases u <;> fin_cases s <;> fin_cases t <;>
        norm_num [threeFacetBoundaryMatrix, threeFacetBoundaryColumn, smallEdgeIndex, largeEdgeIndex, fixedCoordinateSign,
          Finsupp.single_apply, Prod.mk.injEq]

theorem threeFacetBoundaryMatrix_row1 :
    threeFacetBoundaryMatrix r (1, s, t) =
      fixedCoordinateSign t * r (0, s) - fixedCoordinateSign s * r (2, t) := by
  classical
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r q hr hq => simp only [map_add, Finsupp.add_apply, hr, hq]; ring
  | single i n =>
      obtain ⟨e, u⟩ := i
      fin_cases e <;> fin_cases u <;> fin_cases s <;> fin_cases t <;>
        norm_num [threeFacetBoundaryMatrix, threeFacetBoundaryColumn, smallEdgeIndex, largeEdgeIndex, fixedCoordinateSign,
          Finsupp.single_apply, Prod.mk.injEq]

def threeFacetOrientation (i : Fin 3 × ZMod 2) :=
  (if i.1 = 1 then -1 else 1) * fixedCoordinateSign i.2

theorem threeFacetBoundaryMatrix_kernel (r : (Fin 3 × ZMod 2) →₀ ℤ)
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
    · change r _ = r _ * 1
      norm_num
    · change r (0, 1) = r _ * (-1)
      omega
  · fin_cases s
    · change r (1, 0) = r _ * (-1)
      omega
    · change r (1, 1) = r _ * 1
      omega
  · fin_cases s
    · change r (2, 0) = r _ * 1
      omega
    · change r (2, 1) = r _ * (-1)
      omega

end FiniteChains.Davis
