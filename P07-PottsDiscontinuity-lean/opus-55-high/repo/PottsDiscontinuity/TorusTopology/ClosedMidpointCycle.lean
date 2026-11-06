module

public import PottsDiscontinuity.TorusTopology.MidpointWalk

/-! A zero-winding torus orbit is an actual simple square-lattice cycle after
lifting and rotating its edge midpoints. -/

@[expose] public section

open PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusLoops FK
variable {N M : ℕ}

section
variable (ω : ArrowConfig N M) (s : Smoothing N M) (h : CompatibleConfig ω s) (d : DirectedDart ω)
theorem lift_ne_start_one  :
    loopLiftPosition ω s h d 1 ≠ loopLiftPosition ω s h d 0 := by
  rw [show 1 = 0+1 from rfl,loopLiftPosition_succ]
  rcases d with ⟨⟨⟨i,j⟩,p⟩,hd⟩
  cases p <;> simp [horizontalIncrement,verticalIncrement,Prod.ext_iff]

theorem lift_ne_start_two  :
    loopLiftPosition ω s h d 2 ≠ loopLiftPosition ω s h d 0 := by
  rw [show 2 = (0+1)+1 from rfl,loopLiftPosition_succ,loopLiftPosition_succ]
  simp
  rcases d with ⟨⟨⟨i,j⟩,p⟩,hd⟩
  cases p <;>
    simp only [strandReverse,edgeReverse,horizontalIncrement,verticalIncrement]
  all_goals
    cases hb : s _ <;>
      simp [pairedPort,Prod.ext_iff]
end

section
variable (ω : ArrowConfig N M) (s : Smoothing N M) (h : CompatibleConfig ω s) (d : DirectedDart ω) (i : Fin N) (j : Fin M) (hv : loopVertical ω s h j (directedLoopOf ω s h d) = 0) (hh : loopSum ω s h (horizontalCross i) (directedLoopOf ω s h d) = 0)
include i j hv hh
theorem three_le_loopPeriod_of_zero_winding
     :
    3 ≤ loopPeriod ω s h d := by
  have hp := loopPeriod_pos ω s h d
  have hz := (loopLiftPosition_period_eq_start_iff ω s h d i j).mpr ⟨hv,hh⟩
  have h1 := lift_ne_start_one ω s h d
  have h2 := lift_ne_start_two ω s h d
  grind

/-- The closed lattice polygon is obtained from the actual orbit, with its
original starting dart retained. No cycle is selected from mere existence. -/
noncomputable def closedLoopMidpointWalk
     :
    squareLattice.Walk (loopMidpointPosition ω s h d 0) (loopMidpointPosition ω s h d 0) :=
  (loopMidpointWalk ω s h d (loopPeriod ω s h d)).copy rfl
    (loopMidpointPosition_closed_of_zero_winding ω s h d i j hv hh)

/-- The closed lifted polygon is simple in the genuine plane lattice. -/
theorem closedLoopMidpointWalk_isCycle
     :
    (closedLoopMidpointWalk ω s h d i j hv hh).IsCycle := by
  let p := closedLoopMidpointWalk ω s h d i j hv hh
  have hlen : p.length = loopPeriod ω s h d := by
    simp [p,closedLoopMidpointWalk,loopMidpointWalk_length]
  have h3 := three_le_loopPeriod_of_zero_winding ω s h d i j hv hh
  have hnot : ¬ p.Nil := by
    grind
  have hsupport : p.support.dropLast =
      (List.range (loopPeriod ω s h d)).map (loopMidpointPosition ω s h d) := by
    simp [p,closedLoopMidpointWalk,loopMidpointWalk_support,List.range_succ]
  have hnodup : p.support.dropLast.Nodup := by
    rw [hsupport]
    refine List.Nodup.map_on ?_ List.nodup_range
    intro a ha b hb hab
    simp_all
    have he := loopMidpointPosition_injective ω s h d
      (a₁ := ⟨a,ha⟩) (a₂ := ⟨b,hb⟩) hab
    simp_all
  have htail : p.tail.IsPath := by
    rw [SimpleGraph.Walk.isPath_def,SimpleGraph.Walk.support_tail_of_not_nil p hnot]
    exact p.tail_support_perm_dropLast_support.nodup_iff.mpr hnodup
  change p.IsCycle
  exact SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨htail,by omega⟩
end

end PottsDiscontinuity.TorusTopology
