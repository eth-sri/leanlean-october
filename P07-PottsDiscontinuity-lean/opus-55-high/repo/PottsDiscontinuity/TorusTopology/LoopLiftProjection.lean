module

public import PottsDiscontinuity.TorusTopology.LoopOrbitLift
public import PottsDiscontinuity.TorusTopology.LiftedEdgeCover

/-! The ordered integer lift projects to the actual directed dart orbit on the torus
(under `Torus.stepPerm`) at every step. In particular its displacement is geometric,
rather than merely an abstract sum of two cocycles. -/

public section

open PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusLoops TorusRC
variable {N M : ℕ}

/-- Integer nearest-neighbor steps project to precisely the medial step's vertex. -/
theorem loopLiftPosition_step_projection
    (hNp : 0 < N) (hMp : 0 < M) (s : Smoothing N M)
    (d : Dart N M) (z : ℤ × ℤ)
    (hx : periodicCoordinate hNp z.1 = d.1.1)
    (hy : periodicCoordinate hMp z.2 = d.1.2) :
    (periodicCoordinate hNp (z.1 + horizontalIncrement d),
     periodicCoordinate hMp (z.2 + verticalIncrement d)) = (stepPerm s d).1 := by
  rcases d with ⟨⟨i,j⟩,p⟩
  cases p <;>
    simp only [horizontalIncrement,verticalIncrement,add_zero,← sub_eq_add_neg,
      periodicCoordinate_sub_one,periodicCoordinate_add_one,hx,hy,
      stepPerm_apply,strandReverse,edgeReverse]

section
variable (ω : ArrowConfig N M) (s : Smoothing N M) (h : CompatibleConfig ω s) (d : DirectedDart ω)
/-- At every time, the lift lies above the vertex of the actual torus dart. -/
theorem loopLiftPosition_projection (n : ℕ) :
    (periodicCoordinate (Fin.pos d.val.1.1) (loopLiftPosition ω s h d n).1,
     periodicCoordinate (Fin.pos d.val.1.2) (loopLiftPosition ω s h d n).2) =
      ((directedStep ω s h)^[n] d).val.1 := by
  induction n with
  | zero => simp [loopLiftPosition_zero,periodicCoordinate_nat]
  | succ n ih =>
    rw [loopLiftPosition_succ]
    have hh := loopLiftPosition_step_projection (Fin.pos d.val.1.1) (Fin.pos d.val.1.2)
      s (((directedStep ω s h)^[n] d).val) (loopLiftPosition ω s h d n) (congrArg Prod.fst ih) (congrArg Prod.snd ih)
    simpa only [Prod.fst_add,Prod.snd_add,Function.iterate_succ_apply',directedStep_val] using hh

/-- Distinct times before the least period represent distinct actual directed darts. -/
theorem loopOrbit_dart_injective  :
    Function.Injective (fun k : Fin (loopPeriod ω s h d) =>
      ((directedStep ω s h)^[k.val] d).val) := by
  intro k l hh
  apply Fin.ext
  exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod k.isLt l.isLt).mp
    (Subtype.ext hh)

/-- Keeping direction resolves a torus vertex visited by both smoothed strands. -/
theorem loopLiftPosition_port_injective  :
    Function.Injective (fun k : Fin (loopPeriod ω s h d) =>
      (loopLiftPosition ω s h d k.val,((directedStep ω s h)^[k.val] d).val.2)) := by
  intro k l hh
  apply loopOrbit_dart_injective ω s h d
  grind [loopLiftPosition_projection]
end

end PottsDiscontinuity.TorusTopology
