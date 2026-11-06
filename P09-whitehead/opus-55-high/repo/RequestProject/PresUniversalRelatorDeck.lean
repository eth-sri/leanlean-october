import RequestProject.PresCoverRelatorNaturality
import RequestProject.OrderUniversalDeck
import RequestProject.OrderUniversalPosetCover
import RequestProject.PresPosetConnected


namespace FiniteChains.PresModel
open Comb
variable {α J : Type u} (w : J → List (α × Bool))
  (hpos : ∀ j, 0 < (w j).length)

include hpos

/-- The actual path-class cover projection of the nonempty-word presentation model. -/
theorem presUniversalEnd_isPosetCover :
    IsPosetCover (uOrderEnd (P := PresPos w) (a := ptBase w)) := by
  apply uOrderEnd_isPosetCover
  apply presPos_isConnected w
  grind
