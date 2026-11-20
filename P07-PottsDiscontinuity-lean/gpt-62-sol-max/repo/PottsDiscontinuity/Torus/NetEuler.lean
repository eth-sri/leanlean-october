module

public import PottsDiscontinuity.Torus.RibbonHandleBound

/-! The loop-weight comparison only needs the bounded Euler correction.
The number of ribbon handles provides that correction directly. -/

@[expose] public section

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

noncomputable def rcNetIndicator (hN : Even N) (hM : Even M) (A : RCConfig N M) : ℕ :=
  ribbonHandleCount hN hM A

theorem rcNetIndicator_le_one (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    rcNetIndicator hN hM A ≤ 1 := ribbonHandleCount_le_one hN hM A

theorem rcNetIndicator_eq_zero_or_one (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    rcNetIndicator hN hM A = 0 ∨ rcNetIndicator hN hM A = 1 := by
  have := rcNetIndicator_le_one hN hM A
  omega

theorem euler_netIndicator (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    2 * clusterCount hN hM true A + openCount A =
      rcLoopCount hN hM A + N * M / 2 + 2 * rcNetIndicator hN hM A :=
  euler_ribbonHandleCount hN hM A

end PottsDiscontinuity.Torus
