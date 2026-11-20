module

public import PottsDiscontinuity.Torus.DiamondFullConnectivity
public import PottsDiscontinuity.Torus.RibbonHandleMonotone

/-!
# At most one handle on the cellular torus

The full primal ribbon graph has one handle by the proved Euler count, connectivity,
and white-face boundary count. Monotonicity bounds every open subgraph by it.
The winding-based characterization of that handle remains a separate theorem.
-/

@[expose] public section

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

theorem ribbonHandleCount_closed (hN : Even N) (hM : Even M) :
    ribbonHandleCount hN hM (closedRCConfig N M) = 0 := by
  have he := euler_ribbonHandleCount hN hM (closedRCConfig N M)
  rw [clusterCount_closed, rcLoopCount_closed, openCount_closed, card_faceVertex hN] at he
  omega

theorem ribbonHandleCount_open (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M) :
    ribbonHandleCount hN hM (openRCConfig N M) = 1 := by
  have he := euler_ribbonHandleCount hN hM (openRCConfig N M)
  grind only [clusterCount_open, rcLoopCount_open, openCount_open]

/-- The total number of handles of any primal sub-ribbon graph is zero or one. -/
theorem ribbonHandleCount_le_one (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    ribbonHandleCount hN hM A ≤ 1 := by
  by_cases hn : N = 0
  · subst N
    have ha : A = closedRCConfig 0 M := by funext v; exact Fin.elim0 v.1
    rw [ha, ribbonHandleCount_closed]
    omega
  · by_cases hm : M = 0
    · subst M
      solve_by_elim
    · have hb := ribbonHandleCount_mono hN hM A (openRCConfig N M) (fun _ _ => rfl)
      simpa [ribbonHandleCount_open hN hM (Nat.pos_of_ne_zero hn) (Nat.pos_of_ne_zero hm)] using hb

end PottsDiscontinuity.Torus
