module

public import RequestProject.Oriented
public import RequestProject.PresPosetPartialOrder
public import RequestProject.OrderUniversalCocycleComparability
public import RequestProject.PresReadingLetterPrefix

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u v
variable {α J : Type u} {G : Type v} [Group G]
  (w : J → FiniteChains.Comb.Oriented α) (gen : α → G)
  (hrel : ∀ j, wordVal gen (w j) = 1) (a : PresPos w)

/-- The actual lifted cone midpoint reads as its apex reading times the signed word prefix. -/
theorem presUniversal_midpoint_reading (j : J) (k : ℕ) (b : α × Bool)
    (hb : (w j)[k]? = some b) (p q : UOrder (PresPos w) a) (hle : p ≤ q)
    (hp : uOrderEnd p = iCirc w (TCirc.pt w j k CPos.cmid))
    (hq : uOrderEnd q = apexOf w j) :
    (presCoc w gen hrel).readVertex a p =
      (presCoc w gen hrel).readVertex a q *
        (prefixVal w gen j k * (if b.2 then 1 else (gen b.1)⁻¹)) := by
  rw [(presCoc w gen hrel).readVertex_lower_of_le a p q hle, hp, hq]
  change (presCoc w gen hrel).readVertex a q * (trivVal w gen j k CPos.cmid)⁻¹ = _
  rw [trivVal_cmid_inv_of_get w gen j k b hb]

end FiniteChains.PresModel
