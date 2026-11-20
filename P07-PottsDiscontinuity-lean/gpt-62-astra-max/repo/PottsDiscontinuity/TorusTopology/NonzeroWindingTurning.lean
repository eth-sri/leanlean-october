module

public import PottsDiscontinuity.TorusTopology.PeriodicLatticeTurning
public import PottsDiscontinuity.TorusTopology.MidpointCyclicTurning
public import PottsDiscontinuity.TorusTopology.PeriodicCurveBasics

/-! The essential-loop turning classification, on the exact torus loop carrier
`Torus.Loop` used in Corollary 3.13. -/

@[expose] public section

namespace PottsDiscontinuity.TorusTopology
open Torus TorusLoops Finset
variable {N M : ℕ}

/-- A loop with nonzero homological winding has rotation number zero. -/
theorem loopRotationNumber_eq_zero_of_nonzero_winding
    (hN : Even N) (hM : Even M) (i : Fin N) (j : Fin M) (A : RCConfig N M)
    (q : Loop hN hM (rcSmoothing A))
    (hw : loopVertical j q ≠ 0 ∨
      loopSum
        (PottsDiscontinuity.TorusLoops.horizontalCross i) q ≠ 0) :
    loopRotationNumber q = 0 := by
  obtain ⟨d,rfl⟩ := Quotient.exists_rep q
  let ω := checkerArrows N M
  let s := rcSmoothing A
  let h := checkerArrows_compatible hN hM s
  let f := loopMidpointPosition h d
  let D := ((loopDeckDisplacement h d i j).1+(loopDeckDisplacement h d i j).2,
    (loopDeckDisplacement h d i j).2-(loopDeckDisplacement h d i j).1)
  have hadj : ∀ n, FK.squareLattice.Adj (f n) (f (n+1)) := loopMidpointPosition_adj ω s h d
  have hinj : Function.Injective f := loopMidpointPosition_injective_of_nonzero_winding ω s h d i j hw
  have hper : ∀ n, f (n+loopPeriod h d)=f n+D :=
    loopMidpointPosition_add_period ω s h d i j
  have hz := periodic_lattice_turn_eq_zero f hadj hinj (loopPeriod h d) D
    (loopPeriod_pos h d) hper
  have hdir (n : ℕ) : Secant.lab (f n) (f (n+1)) =
      portCompass (midpointDirection s ((directedStep h)^[n] d).val) := by
    exact squareDartCompass_eq_portCompass (hadj n) _
      (loopMidpointPosition_succ_direction ω s h d n)
  have hturn : (∑ n ∈ range (loopPeriod h d),
      midpointQuarterTurn s ((directedStep h)^[n] d).val) = 0 := by
    convert hz using 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [hdir,hdir,portCompass_quarterTurn,Function.iterate_succ_apply',directedStep_val]
    rfl
  have ht := sum_period_midpointQuarterTurn_eq_four_mul_rotationNumber ω s h d
  rw [hturn] at ht
  dsimp [ω,s,h,directedLoopOf] at ht
  omega

end PottsDiscontinuity.TorusTopology
