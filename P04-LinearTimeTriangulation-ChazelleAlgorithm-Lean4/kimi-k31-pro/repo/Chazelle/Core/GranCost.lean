module

public import Chazelle.Core.GranBD
public import Chazelle.RewriteTactics

/-!
# WP-F, part 18: the cost of granularity enforcement

The cost of the whole procedure is `κ D (K (⌈log₂ K⌉ + 1) + 1)` (`cost_total`): the
initialisation is linear in `K` (`A ≤ 2 K` arcs, `R = K + 1` regions) up to `K` binary searches
over the arcs, the worklist makes `O(D K)` steps of cost `O(D)`, and the construction and
decomposition of the result cost `O_D(K log K)`.
-/

namespace Chazelle.Core

namespace Gran

@[expose] public section

/-- The cost of the main path (initialisation, worklist, output). -/
def costMain (K A R D : ℕ) : ℕ :=
  costInit K A R D + ((60 * D + 402) * (K + (D + 1) * K) + 2) + (21 * K + 7)

/-- The constant of the procedure. -/
def κGran (κB κD D : ℕ) : ℕ := 500000 * (D + 2) ^ 2 + κB + κD * (D + 1)

theorem clog_two_le {K A : ℕ} (hA : A ≤ 2 * K) : Nat.clog 2 A ≤ Nat.clog 2 K + 1 := by
  apply Nat.clog_le_of_le_pow
  have := Nat.le_pow_clog (by norm_num : 1 < 2) K
  rwo [pow_succ]

theorem costInit_le {K A R D : ℕ} (hA : A ≤ 2 * K) (hR : R = K + 1) :
    costInit K A R D ≤ 100000 * (D * K + D + K + 1) + 10880 * (K * (Nat.clog 2 A + 1)) := by
  unfold costInit costA NFLoc.locCost
  rw [dmOf_oEnd]
  simp [dmOf, Dm.cap]
  subst hR
  ring_nf
  nlinarith [hA]

theorem room_le (K A R D : ℕ) :
    (dmOf K A R D 0).oEnd + K * (2 * NFLoc.locCost 5100 A + 30) ≤ costInit K A R D := by
  unfold costInit costA
  have : K * (2 * NFLoc.locCost 5100 A + 30) ≤ K * (2 * NFLoc.locCost 5100 A + 32) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

theorem costBD_mono {κB κD D x y : ℕ} (h : x ≤ y) : costBD κB κD D x ≤ costBD κB κD D y := by
  unfold costBD
  have := Nat.clog_mono_right 2 h
  gcongr

theorem cost_total {κB κD K A R D ℓ : ℕ} (hA : A ≤ 2 * K) (hR : R = K + 1) (hℓ : ℓ ≤ K) :
    4 + costMain K A R D + costBD κB κD D ℓ ≤
      κGran κB κD D * (K * (Nat.clog 2 K + 1) + 1) := by
  set X := K * (Nat.clog 2 K + 1) + 1 with hX
  have hKX : K + 1 ≤ X := by rwnl [hX]
  have hY : K * (Nat.clog 2 A + 1) ≤ 2 * X := by
    have := clog_two_le hA
    have : K * (Nat.clog 2 A + 1) ≤ K * (Nat.clog 2 K + 2) := Nat.mul_le_mul_left _ (by omega)
    rwnl [hX]
  have hℓX : ℓ * (Nat.clog 2 ℓ + 1) + 1 ≤ X := by
    have := Nat.mul_le_mul hℓ (Nat.add_le_add_right (Nat.clog_mono_right 2 hℓ) 1)
    omega
  have hI := costInit_le (D := D) hA hR
  set T := (D + 2) ^ 2 with hT
  have hT4 : 4 ≤ T := by rwnl [hT]
  have hDK : D * K + D + K + 1 ≤ T * X := by
    have : D * K + D + K + 1 = (D + 1) * (K + 1) := by ring
    rw [this]
    exact Nat.mul_le_mul (by rwnl [hT]) hKX
  have hL : (60 * D + 402) * (K + (D + 1) * K) ≤ 402 * (T * X) := by
    have : (60 * D + 402) * (K + (D + 1) * K) = ((60 * D + 402) * (D + 2)) * K := by ring
    rw [this]
    have h1 : (60 * D + 402) * (D + 2) ≤ 402 * T := by rwnl [hT]
    calc ((60 * D + 402) * (D + 2)) * K ≤ (402 * T) * X := Nat.mul_le_mul h1 (by omega)
      _ = 402 * (T * X) := by ring
  have hX1 : X ≤ T * X := Nat.le_mul_of_pos_left X (by omega)
  have hTX : 4 ≤ T * X := by nlinarith
  have hB : costBD κB κD D ℓ ≤ 7 + (κB + κD * (D + 1)) * X := by
    unfold costBD
    have := Nat.mul_le_mul_left κB hℓX
    have := Nat.mul_le_mul_left (κD * (D + 1)) hℓX
    nlinarith
  unfold costMain κGran
  have e : (500000 * T + κB + κD * (D + 1)) * X = 500000 * (T * X) + (κB + κD * (D + 1)) * X := by
    ring
  rw [e]
  omega

end

end Gran

end Chazelle.Core
