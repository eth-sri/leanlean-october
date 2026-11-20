module

public import PottsDiscontinuity.Torus.LoopStatistics
public import PottsDiscontinuity.TorusRC.LiftedEvent

/-! # Barrier and seam-closed cylinder events for Lemma 3.15 -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

section
variable (hN : 0 < N) (hM : 0 < M) (A : RCConfig N M) (n : ℕ)

include hN hM A n in
/-- A left-to-right primal crossing of the lifted strip with horizontal
coordinates in `[0,3n]`. The vertical coordinate is unrestricted, so this is
the annular crossing used in the source event B. -/
def torusRCLeftStripCrossing : Prop :=
  ∃ u v : RotatedVertex,
    u.val.1 = 0 ∧ v.val.1 = ((3 * n : ℕ) : ℤ) ∧
      (liftedStripGraph hN hM A 0 ((3 * n : ℕ) : ℤ)).Reachable u v

include hM A in
/-- Every indexed primal edge crossing the seam row is open, except for one. -/
def torusRCSeamAllButOneOpen : Prop :=
  ∃ i₀ : Fin N,
    A (i₀, (⟨0, hM⟩ : Fin M)) = false ∧
      ∀ i : Fin N, i ≠ i₀ → A (i, (⟨0, hM⟩ : Fin M)) = true

include hN hM n in
/-- Source event B: no primal crossing of the left annular strip, and all but
one of the indexed primal seam edges are open. The absence of the crossing is
equivalent, by annular crossing duality, to the dual winding barrier used by
the topological implication. -/
def torusRCBarrier : Set (RCConfig N M) :=
  {A | ¬ torusRCLeftStripCrossing hN hM A n ∧ torusRCSeamAllButOneOpen hM A}

include A in
/-- Closing all indexed edges in the seam row cuts the vertical torus into a
cylinder with distinct bottom and top rows. -/
def torusRCSeamClosed : RCConfig N M :=
  fun e => if e.2.val = 0 then false else A e

end

variable (hN : Even N) (hM : Even M) (hNpos : 0 < N) (hMpos : 0 < M) (r : ℕ)
include hN hM

include r in
/-- The clean cylinder crossing event used in the premise `hUr` below: there are `r` different
open primal clusters of the seam-closed configuration, each joining row zero
to the top row. The vertices are existential, so the event handles every
horizontal location and both checkerboard parities. -/
def torusRCSeamClosedCylinderCrossings (A : RCConfig N M) : Prop :=
  ∃ x : Fin r → FaceVertex N M true,
    (∀ i, (x i).val.2.val = 0) ∧
      (∀ i, ∃ y : FaceVertex N M true,
        y.val.2.val + 1 = M ∧
          (diamondOpenGraph hN hM true A).Reachable (x i) y) ∧
      ∀ i j, i ≠ j →
        ¬ (diamondOpenGraph hN hM true A).Reachable (x i) (x j)

include hNpos hMpos in
/-- Exact topological premise that B ∩ C′ forces `U = 1`, where the event B is
`torusRCBarrier` and C′ is `torusCPrime`. It is discharged by `TorusTopology.hBCU_proved`
in `TorusTopology/BarrierEvent.lean`. -/
def hBCU
    (hNdiv : 8 ∣ N) (n : ℕ) : Prop :=
  8 * n ≤ N → N / 2 < M →
    ∀ A : RCConfig N M,
      A ∈ torusRCBarrier hNpos hMpos n →
      A ∈ torusCPrime hNpos hMpos hNdiv hM n →
      rcVerticalWinding hN hM ⟨0, hMpos⟩ A = 1

include hMpos r in
/-- Exact topological premise that `U ≥ r` forces `r` distinct bottom-to-top clusters
after the seam row is closed. It is discharged by `TorusTopology.hUr_proved` in
`TorusTopology/CylinderCount.lean`. -/
def hUr : Prop :=
  ∀ A : RCConfig N M,
    r ≤ rcVerticalWinding hN hM ⟨0, hMpos⟩ A →
      torusRCSeamClosedCylinderCrossings hN hM r (torusRCSeamClosed A)

end PottsDiscontinuity.TorusRC
