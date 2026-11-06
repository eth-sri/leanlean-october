module

public import RequestProject.ChamberQuotientCover
public import RequestProject.OrderPosetCoverThree

@[expose] public section

/-! The full Davis nerve covers the quotient cube poset, including its three-cells. -/

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

omit [Fintype V] in
theorem qProjCube_monotone : Monotone (qProjCube (A := A)) := by
  intro p q h
  refine ⟨h.1, fun w hw => ?_⟩
  have hwp : w ∉ p.spx := fun hc => hw (h.1 hc)
  rw [qProjCube_sgn_of_not_mem hwp, qProjCube_sgn_of_not_mem hw]
  exact (phi_rep_eq_of_inChamber (inChamber_rep_of_le h) hw).symm

/-- The actual quotient projection is a poset covering, before removing any chambers. -/
theorem qProjCube_isPosetCover : IsPosetCover (qProjCube (A := A)) where
  mono := qProjCube_monotone
  surj c := exists_zOld_qProjCube c
  up _ _ h := existsUnique_up_old h
  down _ _ h := existsUnique_down_old h

end FiniteChains.Davis
