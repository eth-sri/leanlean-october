module

public import PottsDiscontinuity.TorusTopology.BoundarySpan
public import PottsDiscontinuity.TorusTopology.LiftedPotentials
public import PottsDiscontinuity.TorusTopology.SeamWinding
public import PottsDiscontinuity.TorusTopology.StripPotential

/-! B intersect C prime forces U=1 on the exact events `TorusRC.torusRCBarrier` and
`TorusRC.torusCPrime` used in the proof of (3.15). The lower bound
uses finite cellular topology and the actual prescribed integer lifts. -/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusRC CorrLength
variable {N M : ℕ}

variable (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M) (hNdiv : 8 ∣ N) (n : ℕ)
    (hnN : 8*n ≤ N) (j : Fin M) (A : RCConfig N M) (hB : A ∈ torusRCBarrier hNp hMp n)
    (hC : A ∈ torusCPrime hNp hMp hNdiv hM n)

/-- A nonzero vertical loop forces U ≥ 1, using evenness of total mass. -/
theorem one_le_U_of_vertical_loop
    (hloop : ∃ q : Loop hN hM (rcSmoothing A),
      loopVertical j q ≠ 0) :
    1 ≤ rcVerticalWinding hN hM j A := by
  classical
  obtain ⟨q,hq⟩ := hloop
  have hp := Int.natAbs_pos.2 hq
  have hb : (loopVertical j q).natAbs ≤
      verticalMass (checkerArrows_compatible hN hM (rcSmoothing A)) j :=
    Finset.single_le_sum (fun r _ => Nat.zero_le
      ((loopVertical j r).natAbs))
      (Finset.mem_univ q)
  have he := two_mul_verticalWindingCount hN
    (checkerArrows_compatible hN hM (rcSmoothing A)) j
  change 2 * rcVerticalWinding hN hM j A = _ at he
  change _ ≤ verticalMass (checkerArrows_compatible hN hM (rcSmoothing A)) j at hb
  omega

include hnN hB hC in
/-- The lower bound in the implication B ∩ C′ ⇒ U = 1, for the exact corrected source
events: B and C prime give
at least one pair of vertical loop windings. -/
theorem one_le_U_of_barrier_and_CPrime :
    1 ≤ rcVerticalWinding hN hM ⟨0,hMp⟩ A := by
  have hno := hB.1
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst n
    let u : RotatedVertex := ⟨(0,0),⟨0,rfl⟩⟩
    exact hno ⟨u,u,rfl,by rfl,SimpleGraph.Reachable.refl _⟩
  have hwidth : 3*n < N := by omega
  have hX := horizontal_displacement_zero_of_no_strip_crossing hN hM hNp hMp A n hn hwidth hno
  have hconn := torusCPrime_vertical_connection hNp hMp hNdiv hM n A hC
  have hY := exists_vertical_cycle_of_lifted_period hN hM hNp hMp A hconn
  apply one_le_U_of_vertical_loop hN hM ⟨0,hMp⟩ A
  exact exists_vertical_loop_of_aligned_vertical_cycle hN hM hNp hMp ⟨0,hMp⟩ A hX hY

include hnN hB hC in
/-- B ∩ C′ forces U = 1: the exact statement consumed by the proof of (3.15), with no
topological premise added. -/
theorem barrier_and_CPrime_imply_U_eq_one :
    rcVerticalWinding hN hM ⟨0,hMp⟩ A = 1 := Nat.le_antisymm
    (rcVerticalWinding_le_one_of_seamAllButOneOpen hN hM hMp ⟨0,hMp⟩ A hB.2)
    (one_le_U_of_barrier_and_CPrime hN hM hNp hMp hNdiv n hnN A hB hC)

/-- The exact topology contract `TorusRC.hBCU` of the (3.15) argument is discharged. -/
theorem hBCU_proved : hBCU hN hM hNp hMp hNdiv n :=
  fun hnN _hNM A hB hC =>
    barrier_and_CPrime_imply_U_eq_one hN hM hNp hMp hNdiv n hnN A hB hC

end PottsDiscontinuity.TorusTopology
