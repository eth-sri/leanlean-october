module

public import Mathlib.Tactic

@[expose] public section

namespace HordijkSteelThreshold

def diamondPotential {V : Type*} (right : V → V) (rightEdge : V → Bool) :
    ℕ → V → Bool
  | 0, _ => false
  | k + 1, v => rightEdge v ^^ diamondPotential right rightEdge k (right v)

theorem diamondPotential_edges {V : Type*}
    (left right : V → V) (height : V → ℕ)
    (leftEdge rightEdge : V → Bool)
    (hheight : ∀ v, height (right v) ≤ height v - 1)
    (hcommute : ∀ v, left (right v) = right (left v))
    (hroot : ∀ v, height v = 0 → leftEdge v = false ∧ rightEdge v = false)
    (hdiamond : ∀ v, (((leftEdge v ^^ rightEdge v) ^^ leftEdge (right v)) ^^
      rightEdge (left v)) = false)
    (k : ℕ) (v : V) (hv : height v ≤ k) :
    ((diamondPotential right rightEdge k v ^^
      diamondPotential right rightEdge k (left v)) = leftEdge v) ∧
    ((diamondPotential right rightEdge k v ^^
      diamondPotential right rightEdge k (right v)) = rightEdge v) := by
  induction k generalizing v with
  | zero =>
    obtain ⟨hl, hr⟩ := hroot v (by omega)
    simp [diamondPotential, hl, hr]
  | succ k ih =>
    obtain ⟨hil, hir⟩ := ih (right v) (by have := hheight v; omega)
    rw [hcommute v] at hil
    have hd := hdiamond v
    simp only [diamondPotential]
    revert hil hir hd
    generalize leftEdge v = a, rightEdge v = b, leftEdge (right v) = c, rightEdge (left v) = d,
      rightEdge (right v) = e,
      diamondPotential right rightEdge k (right v) = x,
      diamondPotential right rightEdge k (right (left v)) = y,
      diamondPotential right rightEdge k (right (right v)) = z
    decide +revert

end HordijkSteelThreshold
