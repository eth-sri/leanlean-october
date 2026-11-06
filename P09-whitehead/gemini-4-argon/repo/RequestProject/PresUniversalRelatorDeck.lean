module

public import RequestProject.PresCoverRelatorNaturality
public import RequestProject.OrderUniversalDeck
public import RequestProject.OrderUniversalPosetCover
public import RequestProject.PresPosetConnected

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool))
  (hpos : ∀ j, 0 < (w j).length)

include hpos

/-- The actual path-class cover projection of the nonempty-word presentation model. -/
theorem presUniversalEnd_isPosetCover :
    IsPosetCover (uOrderEnd (P := PresPos w) (a := ptBase w)) := by
  apply uOrderEnd_isPosetCover
  apply presPos_isConnected w
  intro j he
  have h := hpos j
  rw [he, List.length_nil] at h
  omega
