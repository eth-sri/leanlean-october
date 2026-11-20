module

public import PottsDiscontinuity.TorusTopology.SquareLatticeTurning

/-! Every actual simple periodic lattice curve has zero turn over a period. -/

@[expose] public section

namespace PottsDiscontinuity.TorusTopology
open Finset Planar.Medial

/-- The actual compass direction of a sequence's nth unit edge. -/
def sequenceCompass (f : ℕ → ℤ × ℤ)
    (h : ∀ n, FK.squareLattice.Adj (f n) (f (n+1))) (n : ℕ) : Fin 4 :=
  squareDartCompass ⟨⟨f n,f (n+1)⟩,h n⟩

/-- The periodic discrete turning theorem, with an arbitrary nonzero deck vector. -/
theorem periodic_lattice_turn_eq_zero
    (f : ℕ → ℤ × ℤ) (hadj : ∀ n, FK.squareLattice.Adj (f n) (f (n+1)))
    (hf : Function.Injective f) (L : ℕ) (D : ℤ × ℤ) (hper : ∀ n, f (n+L)=f n+D) :
    (∑ n ∈ range L, primalCompassQuarterTurn (sequenceCompass f hadj n)
      (sequenceCompass f hadj (n+1))) = 0 := by
  have ht := LatticeSecants.turn_periodic_sum f L D hadj hf hper
  have he (i : ℕ) : LatticeSecants.turn (f (i+1)-f i) (f (i+2)-f (i+1)) =
      2 * primalCompassQuarterTurn (sequenceCompass f hadj i) (sequenceCompass f hadj (i+1)) := by
    simpa [sequenceCompass, squareDartCompass] using
          LatticeSecants.turn_eq_quarter (LatticeSecants.unitStep_sub (hadj i))
            (LatticeSecants.unitStep_sub (hadj (i+1)))
  simp_rw [he, ← mul_sum] at ht
  omega

end PottsDiscontinuity.TorusTopology
