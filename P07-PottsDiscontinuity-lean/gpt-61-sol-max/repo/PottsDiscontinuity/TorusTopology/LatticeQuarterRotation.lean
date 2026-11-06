module
public import Mathlib

public import PottsDiscontinuity.TorusTopology.LatticeSequenceWalk

/-! Orientation-preserving quarter rotation of actual lattice curves. -/

@[expose] public section

namespace PottsDiscontinuity.TorusTopology
open Planar.Medial

/-- Positive quarter rotation of the integer plane. -/
def latticeQuarterRotation (z : ℤ × ℤ)  := (-z.2,z.1)

lemma latticeQuarterRotation_injective : Function.Injective latticeQuarterRotation := by
  intro u v h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp [latticeQuarterRotation] at hx hy
  exact Prod.ext hy (by omega)

lemma latticeQuarterRotation_add (u v : ℤ × ℤ) :
    latticeQuarterRotation (u+v) = latticeQuarterRotation u+latticeQuarterRotation v := by
  ext <;> simp [latticeQuarterRotation]; ring

lemma latticeQuarterRotation_adj (u v : ℤ × ℤ) :
    FK.squareLattice.Adj (latticeQuarterRotation u) (latticeQuarterRotation v) ↔
      FK.squareLattice.Adj u v := by
  rw [FK.squareLattice_adj_iff,FK.squareLattice_adj_iff]
  dsimp [latticeQuarterRotation]
  omega

lemma squareDartCompass_quarterRotation {u v : ℤ × ℤ} (h : FK.squareLattice.Adj u v) :
    squareDartCompass ⟨⟨latticeQuarterRotation u,latticeQuarterRotation v⟩,
      (latticeQuarterRotation_adj u v).mpr h⟩ = squareDartCompass ⟨⟨u,v⟩,h⟩+1 := by
  
  rcases  (FK.squareLattice_adj_iff u v).mp h  with ⟨hx|hx,hy⟩ | ⟨hx,hy|hy⟩
  all_goals
    grind [squareDartCompass, latticeQuarterRotation]

lemma primalCompassQuarterTurn_add_one (a b : Fin 4) :
    primalCompassQuarterTurn (a+1) (b+1) = primalCompassQuarterTurn a b := by
  fin_cases a <;> fin_cases b <;> decide

section

variable (f : ℕ → ℤ × ℤ) (h : ∀ n, FK.squareLattice.Adj (f n) (f (n+1)))
include h

lemma sequenceCompass_quarterRotation  (n : ℕ) :
    sequenceCompass (fun n => latticeQuarterRotation (f n))
      (fun n => (latticeQuarterRotation_adj _ _).mpr (h n)) n =
      sequenceCompass f h n+1 := squareDartCompass_quarterRotation (h n)

lemma sum_sequenceTurn_quarterRotation  (L : ℕ) :
     ∑ n ∈ Finset.range L, primalCompassQuarterTurn
      (sequenceCompass (fun n => latticeQuarterRotation (f n))
        (fun n => (latticeQuarterRotation_adj _ _).mpr (h n)) n)
      (sequenceCompass (fun n => latticeQuarterRotation (f n))
        (fun n => (latticeQuarterRotation_adj _ _).mpr (h n)) (n+1))  =
    ∑ n ∈ Finset.range L, primalCompassQuarterTurn (sequenceCompass f h n)
      (sequenceCompass f h (n+1)) := by
  simp_all [sequenceCompass_quarterRotation, primalCompassQuarterTurn_add_one]

end

end PottsDiscontinuity.TorusTopology
