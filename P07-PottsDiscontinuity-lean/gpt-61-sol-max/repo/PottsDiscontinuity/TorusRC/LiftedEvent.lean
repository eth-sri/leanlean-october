module
public import Mathlib

public import PottsDiscontinuity.TorusRC.LiftedPaths

/-! # Event C prime with a lifted end segment -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

/-- The source's right-hand column x=3N/4, in the integer cover. -/
def sourceRightColumn (N : ℕ) : ℤ := (3 * (N / 4) : ℕ)

theorem sourceRightColumn_even (hN : 8 ∣ N) : Even (sourceRightColumn N) := by
  grind +locals

/-- The chain up to the last complete `2n` block, followed by a final lifted
segment to height `M`. Every path is localized to its specified lift. -/
def liftedCPrime (hN : 0 < N) (hM : 0 < M) (a b x : ℤ) (hx : Even x)
    (hMeven : Even M) (n R : ℕ) : Set (RCConfig N M) := by
  let k := M / (2 * n)
  let y := liftedChainSite x hx n
  exact {A | A ∈ liftedChainEvent hN hM a b R y k ∧
    liftedBoxConnection hN hM A a b R (y k)
      (liftedColumnSite x (M : ℤ) hx (by exact_mod_cast hMeven))}

/-- The source-positioned corrected event C prime: paths remain in the right
half and inside the radius-N/4 box around each prescribed lift. -/
def torusCPrime (hN : 0 < N) (hM : 0 < M) (hNdiv : 8 ∣ N)
    (hMeven : Even M) (n : ℕ) : Set (RCConfig N M) :=
  liftedCPrime hN hM (N / 2 : ℤ) (N : ℤ) (sourceRightColumn N)
    (sourceRightColumn_even hNdiv) hMeven n (N / 4)

section

variable (hN : 0 < N) (hM : 0 < M)


/-- C prime forces an actual path in the lifted primal graph from height zero
to height `M`. This retains winding information lost by a torus connection. -/
theorem liftedCPrime_vertical_connection 
    (a b x : ℤ) (hx : Even x) (hMeven : Even M) (n R : ℕ)
    (A : RCConfig N M) (hA : A ∈ liftedCPrime hN hM a b x hx hMeven n R) :
    (liftedStripGraph hN hM A a b).Reachable
      (liftedColumnSite x 0 hx ⟨0, rfl⟩)
      (liftedColumnSite x (M : ℤ) hx (by exact_mod_cast hMeven)) := by
  
  
  
  let y := liftedChainSite x hx n
  have hchain := liftedChainEvent_reachable hN hM a b R y (M / (2 * n)) A hA.1
  
  
  obtain ⟨w, _hw⟩ := hA.2
  exact hchain.trans ⟨w⟩

theorem torusCPrime_vertical_connection 
    (hNdiv : 8 ∣ N) (hMeven : Even M) (n : ℕ) (A : RCConfig N M)
    (hA : A ∈ torusCPrime hN hM hNdiv hMeven n) :
    (liftedStripGraph hN hM A (N / 2 : ℤ) (N : ℤ)).Reachable
      (liftedColumnSite (sourceRightColumn N) 0 (sourceRightColumn_even hNdiv)
        ⟨0, rfl⟩)
      (liftedColumnSite (sourceRightColumn N) (M : ℤ)
        (sourceRightColumn_even hNdiv) (by exact_mod_cast hMeven)) := by
                                                                        solve_by_elim [_root_.PottsDiscontinuity.TorusRC.liftedCPrime_vertical_connection]

end

end PottsDiscontinuity.TorusRC
