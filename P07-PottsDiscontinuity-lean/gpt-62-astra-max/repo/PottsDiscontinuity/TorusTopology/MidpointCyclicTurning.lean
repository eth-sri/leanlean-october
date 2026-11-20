module

public import PottsDiscontinuity.TorusTopology.ClosedMidpointCycle
public import PottsDiscontinuity.TorusTopology.MidpointTurning
public import PottsDiscontinuity.TorusTopology.PeriodicMidpointLift
public import PottsDiscontinuity.TorusTopology.SquareLatticeTurning

@[expose] public section

namespace PottsDiscontinuity.TorusTopology
open SimpleGraph Torus TorusLoops
open PottsDiscontinuity.SixVertex
open Planar.Medial
variable {N M : ℕ}

/-- Positive cyclic compass encoding of the four actual cardinal ports. -/
def portCompass : Port → Fin 4
  | .east => 0 | .north => 1 | .west => 2 | .south => 3

lemma portCompass_quarterTurn (p r : Port) :
    primalCompassQuarterTurn (portCompass p) (portCompass r) = latticeQuarterTurn p r := by
  cases p <;> cases r <;> decide

lemma squareDartCompass_eq_portCompass {u v : ℤ × ℤ}
    (h : FK.squareLattice.Adj u v) (p : Port) (hv : v = u+portVector p) :
    squareDartCompass ⟨⟨u,v⟩,h⟩ = portCompass p := by
  subst v
  cases p <;> simp [squareDartCompass,Secant.lab,portCompass,portVector]

variable (ω : ArrowConfig N M) (s : Smoothing N M) (h : CompatibleConfig ω s) (d : DirectedDart ω)

lemma loopMidpointWalk_compassDirections (n : ℕ) :
    squareWalkCompassDirections (loopMidpointWalk h d n) =
      (List.range n).map (fun k => portCompass
        (midpointDirection s ((directedStep h)^[k] d).val)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [loopMidpointWalk,squareWalkCompassDirections,Walk.darts_concat,
      List.concat_eq_append,List.map_append,List.map_singleton]
    change squareWalkCompassDirections (loopMidpointWalk h d n) ++ _ = _
    rw [ih,List.range_succ,List.map_append,List.map_singleton]
    congr 1
    exact congrArg (fun z => [z]) (squareDartCompass_eq_portCompass _ _
      (loopMidpointPosition_succ_direction ω s h d n))

lemma rotate_range_map_one {α : Type*} (f : ℕ → α) (L : ℕ) (hL : 0 < L)
    (hf : f L = f 0) :
    ((List.range L).map f).rotate 1 = (List.range L).map (fun n => f (n+1)) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
  conv_lhs => rw [List.range_succ_eq_map,List.map_cons,List.rotate_cons_succ,List.rotate_zero]
  rw [List.range_succ,List.map_append,List.map_singleton]
  simp only [List.map_map,Function.comp_def]
  rw [hf]

lemma closedLoopMidpointWalk_cyclicTurn (i : Fin N) (j : Fin M)
    (hv : loopVertical j (directedLoopOf h d) = 0)
    (hh : loopSum (horizontalCross i) (directedLoopOf h d) = 0) :
    squareWalkCyclicTurn (closedLoopMidpointWalk hv hh) =
      4 * loopRotationNumber (directedLoopOf h d) := by
  have hdirs : squareWalkCompassDirections (closedLoopMidpointWalk hv hh) =
      (List.range (loopPeriod h d)).map (fun k => portCompass
        (midpointDirection s ((directedStep h)^[k] d).val)) := by
    simpa [squareWalkCompassDirections,closedLoopMidpointWalk] using
      loopMidpointWalk_compassDirections ω s h d (loopPeriod h d)
  have hf : (portCompass (midpointDirection s
      ((directedStep h)^[loopPeriod h d] d).val)) =
        portCompass (midpointDirection s ((directedStep h)^[0] d).val) := by
    rw [show loopPeriod h d = 0+loopPeriod h d by omega,loopOrbit_add_period]
  unfold squareWalkCyclicTurn compassWordCyclicTurn
  rw [hdirs,rotate_range_map_one _ _ (loopPeriod_pos h d) hf]
  rw [List.zipWith_map]
  simp only [List.zipWith_self]
  have htable : ∀ k, primalCompassQuarterTurn
      (portCompass (midpointDirection s ((directedStep h)^[k] d).val))
      (portCompass (midpointDirection s ((directedStep h)^[k+1] d).val)) =
      midpointQuarterTurn s ((directedStep h)^[k] d).val := by
    intro k
    rw [portCompass_quarterTurn]
    rw [Function.iterate_succ_apply',directedStep_val]
    rfl
  simp_rw [htable]
  have hsum (f : ℕ → ℤ) (n : ℕ) :
      ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
    induction n with
    | zero => simp
    | succ n ih => simp [List.range_succ,Finset.sum_range_succ,ih]
  rw [hsum]
  exact sum_period_midpointQuarterTurn_eq_four_mul_rotationNumber ω s h d

end PottsDiscontinuity.TorusTopology
