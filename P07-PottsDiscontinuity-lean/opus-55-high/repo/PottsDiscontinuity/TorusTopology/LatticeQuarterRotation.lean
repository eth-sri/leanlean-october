module

public import PottsDiscontinuity.TorusTopology.LatticeSequenceWalk

/-! Orientation-preserving quarter rotation of actual lattice curves. -/

@[expose] public section

namespace PottsDiscontinuity.TorusTopology
open Planar.Medial

/-- Positive quarter rotation of the integer plane. -/
def latticeQuarterRotation (z : ℤ × ℤ) : ℤ × ℤ := (-z.2,z.1)

theorem latticeQuarterRotation_injective : Function.Injective latticeQuarterRotation := by
  intro u v h
  grind [latticeQuarterRotation]

section
variable (u v : ℤ × ℤ)
theorem latticeQuarterRotation_add  :
    latticeQuarterRotation (u+v) = latticeQuarterRotation u+latticeQuarterRotation v := by
  ext <;> simp [latticeQuarterRotation]; ring

theorem latticeQuarterRotation_adj  :
    FK.squareLattice.Adj (latticeQuarterRotation u) (latticeQuarterRotation v) ↔
      FK.squareLattice.Adj u v := by
  rw [FK.squareLattice_adj_iff,FK.squareLattice_adj_iff]
  grind [latticeQuarterRotation]
end

theorem squareDartCompass_quarterRotation {u v : ℤ × ℤ} (h : FK.squareLattice.Adj u v) :
    squareDartCompass ⟨⟨latticeQuarterRotation u,latticeQuarterRotation v⟩,
      (latticeQuarterRotation_adj u v).mpr h⟩ = squareDartCompass ⟨⟨u,v⟩,h⟩+1 := by
  have hh := (FK.squareLattice_adj_iff u v).mp h
  all_goals
    dsimp only [squareDartCompass,latticeQuarterRotation]
    split_ifs <;> norm_num <;> omega

theorem primalCompassQuarterTurn_add_one (a b : Fin 4) :
    primalCompassQuarterTurn (a+1) (b+1) = primalCompassQuarterTurn a b := by
  fin_cases a <;> fin_cases b <;> decide

section
variable (f : ℕ → ℤ × ℤ) (h : ∀ n, FK.squareLattice.Adj (f n) (f (n+1)))
theorem sequenceCompass_quarterRotation (n : ℕ) :
    sequenceCompass (fun n => latticeQuarterRotation (f n))
      (fun n => (latticeQuarterRotation_adj _ _).mpr (h n)) n =
      sequenceCompass f h n+1 :=
  squareDartCompass_quarterRotation (h n)

theorem sum_sequenceTurn_quarterRotation (L : ℕ) :
    (∑ n ∈ Finset.range L, primalCompassQuarterTurn
      (sequenceCompass (fun n => latticeQuarterRotation (f n))
        (fun n => (latticeQuarterRotation_adj _ _).mpr (h n)) n)
      (sequenceCompass (fun n => latticeQuarterRotation (f n))
        (fun n => (latticeQuarterRotation_adj _ _).mpr (h n)) (n+1))) =
    ∑ n ∈ Finset.range L, primalCompassQuarterTurn (sequenceCompass f h n)
      (sequenceCompass f h (n+1)) := by
  simp_all [sequenceCompass_quarterRotation, primalCompassQuarterTurn_add_one]
end

end PottsDiscontinuity.TorusTopology
