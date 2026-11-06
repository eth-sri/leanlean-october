module

public import RequestProject.Oriented
public import RequestProject.OrderNerveLowerCone
public import RequestProject.RelatorCircleBoundaryHomeomorph

@[expose] public section

/-! The actual closed lower ideal of a nonempty relator apex is a genuine
two-dimensional disk. Its strict lower interval is precisely the norm-one
boundary, with the fixed relator-circle parametrization. -/

noncomputable section
namespace FiniteChains.PresModel
open Comb RelativeAttachment
open scoped Classical

variable {α J : Type} (w : J → FiniteChains.Comb.Oriented α) (j : J)
    (hn : 0 < (w j).length)

noncomputable instance relatorCircle_fintype : Fintype (RelatorCircle w j) :=
  Fintype.ofFinite _

def presConeBallHomeomorph :
    orderNerveRealization (Set.Iic (apexOf w j)) ≃ₜ ClosedUnitBall (Fin 2 → ℝ) := by
  letI : Nonempty (RelatorCircle w j) := relatorCircle_nonempty w j (List.ne_nil_of_length_pos hn)
  exact lowerConeBallHomeomorph (apexOf w j) (relatorCircleOrderIso w j)
    (relatorCircleBoundaryHomeomorph w j hn)

end FiniteChains.PresModel
