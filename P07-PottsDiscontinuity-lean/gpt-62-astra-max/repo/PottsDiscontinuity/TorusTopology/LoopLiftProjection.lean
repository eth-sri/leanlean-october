module

public import PottsDiscontinuity.TorusTopology.LoopOrbitLift
public import PottsDiscontinuity.TorusTopology.LiftedEdgeCover

/-! The ordered integer lift projects to the actual directed dart orbit on the torus
(under `Torus.stepPerm`) at every step. In particular its displacement is geometric,
rather than merely an abstract sum of two cocycles. -/

@[expose] public section

open PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusLoops TorusRC
variable {N M : ℕ}

lemma periodicCoordinate_add_one (hN : 0 < N) (z : ℤ) :
    periodicCoordinate hN (z+1) = nxt (periodicCoordinate hN z) := by
  have hh := periodicCoordinate_sub_one hN (z+1)
  grind

variable (ω : ArrowConfig N M) {hNp : 0 < N} {hMp : 0 < M} (s : Smoothing N M)
    (h : CompatibleConfig ω s) (d : DirectedDart ω)

/-- Integer nearest-neighbor steps project to precisely the medial step's vertex. -/
lemma loopLiftPosition_step_projection
    {d : Dart N M} {z : ℤ × ℤ}
    (hx : periodicCoordinate hNp z.1 = d.1.1)
    (hy : periodicCoordinate hMp z.2 = d.1.2) :
    (periodicCoordinate hNp (z.1 + horizontalIncrement d),
     periodicCoordinate hMp (z.2 + verticalIncrement d)) = (stepPerm s d).1 := by
  rcases d with ⟨⟨i,j⟩,p⟩
  cases p <;>
    simp only [horizontalIncrement,verticalIncrement,add_zero,← sub_eq_add_neg,
      periodicCoordinate_sub_one,periodicCoordinate_add_one,hx,hy,
      stepPerm_apply,strandReverse,edgeReverse]

/-- At every time, the lift lies above the vertex of the actual torus dart. -/
theorem loopLiftPosition_projection {ω : ArrowConfig N M} {s : Smoothing N M}
    (h : CompatibleConfig ω s) (d : DirectedDart ω) (n : ℕ) :
    (periodicCoordinate (Fin.pos d.val.1.1) (loopLiftPosition h d n).1,
     periodicCoordinate (Fin.pos d.val.1.2) (loopLiftPosition h d n).2) =
      ((directedStep h)^[n] d).val.1 := by
  induction n with
  | zero => simp [loopLiftPosition_zero,periodicCoordinate_nat]
  | succ n ih =>
    rw [loopLiftPosition_succ]
    have hx := congrArg Prod.fst ih
    have hy := congrArg Prod.snd ih
    have hh := loopLiftPosition_step_projection (hNp := (Fin.pos d.val.1.1)) (hMp := (Fin.pos d.val.1.2))
      s (d := (((directedStep h)^[n] d).val)) (z := (loopLiftPosition h d n)) hx hy
    simpa only [Prod.fst_add,Prod.snd_add,Function.iterate_succ_apply',directedStep_val] using hh

/-- Distinct times before the least period represent distinct actual directed darts. -/
theorem loopOrbit_dart_injective :
    Function.Injective (fun k : Fin (loopPeriod h d) =>
      ((directedStep h)^[k.val] d).val) := by
  intro k l hh
  apply Fin.ext
  exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod k.isLt l.isLt).mp
    (Subtype.ext hh)

/-- Keeping direction resolves a torus vertex visited by both smoothed strands. -/
theorem loopLiftPosition_port_injective :
    Function.Injective (fun k : Fin (loopPeriod h d) =>
      (loopLiftPosition h d k.val,((directedStep h)^[k.val] d).val.2)) := by
  intro k l hh
  have hz := congrArg Prod.fst hh
  change loopLiftPosition h d k.val = loopLiftPosition h d l.val at hz
  have hp := congrArg Prod.snd hh
  apply loopOrbit_dart_injective ω s h d
  apply Prod.ext
  · rw [← loopLiftPosition_projection,← loopLiftPosition_projection,hz]
  · exact hp

end PottsDiscontinuity.TorusTopology
