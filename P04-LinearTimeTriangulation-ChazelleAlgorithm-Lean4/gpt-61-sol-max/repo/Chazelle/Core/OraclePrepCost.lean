module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.OraclePrepBook

/-!
# Lemma 3.6 (WP-H), preprocessing part 34: the cost bounds of the preprocessing

With `K` chords, every quantity of the preprocessing is at most `64 (K + 1)` and every cost at
most a constant times `Fb K = (K + 1) (⌈log₂ 64 (K + 1)⌉ + 1)`; with `K ≤ 60 (2 m + 7)` (Lemma 2.3)
and `m ≥ 1`, `Fb K ≤ 40 (K (⌈log₂ m⌉ + 1) + 1)` (`Fb_le`).
-/

namespace Chazelle.Core

namespace OracleR

@[expose] public section

theorem clog_mul_le (a b : ℕ) : Nat.clog 2 (a * b) ≤ Nat.clog 2 a + Nat.clog 2 b := by
  rw [Nat.clog_le_iff_le_pow (by norm_num), pow_add]
  exact Nat.mul_le_mul (Nat.le_pow_clog (by norm_num) a) (Nat.le_pow_clog (by norm_num) b)

/-- The unit of the costs. -/
def Fb (K : ℕ) : ℕ := (K + 1) * (Nat.clog 2 (64 * (K + 1)) + 1)

theorem nclog_le {n K : ℕ} (h : n ≤ 64 * (K + 1)) : n * (Nat.clog 2 n + 1) ≤ 64 * Fb K := by
  unfold Fb
  have := Nat.clog_mono_right 2 h
  calc n * (Nat.clog 2 n + 1) ≤ (64 * (K + 1)) * (Nat.clog 2 (64 * (K + 1)) + 1) :=
        Nat.mul_le_mul h (by omega)
    _ = 64 * ((K + 1) * (Nat.clog 2 (64 * (K + 1)) + 1)) := by ring

theorem sortCost_le {κ n K : ℕ} (h : n ≤ 64 * (K + 1)) :
    SortR.sortCost κ n ≤ (κ + 30) * (64 * Fb K + 1) := by
  unfold SortR.sortCost
  have := nclog_le h
  simp_all

theorem clCost_le {μ E K : ℕ} (h : μ + E ≤ 64 * (K + 1)) :
    clCost μ E ≤ Cluster.clusterK * (64 * Fb K + 1) := by
  unfold clCost
  have := nclog_le h
  exact Nat.mul_le_mul_left _ (by omega)

theorem clog_le_Fb {x K : ℕ} (h : x ≤ 64 * (K + 1)) : Nat.clog 2 x ≤ Fb K := by
  unfold Fb
  have := Nat.clog_mono_right 2 h
  grind

theorem mul_clog_le_Fb {a x K : ℕ} (ha : a ≤ 5 * (K + 1)) (h : x ≤ 64 * (K + 1)) :
    a * (Nat.clog 2 x + 1) ≤ 5 * Fb K := by
  unfold Fb
  have := Nat.clog_mono_right 2 h
  calc a * (Nat.clog 2 x + 1) ≤ (5 * (K + 1)) * (Nat.clog 2 (64 * (K + 1)) + 1) :=
        Nat.mul_le_mul ha (by omega)
    _ = 5 * ((K + 1) * (Nat.clog 2 (64 * (K + 1)) + 1)) := by ring

theorem one_le_Fb (K : ℕ) : 1 ≤ Fb K := by
  core_grind

theorem K_le_Fb (K : ℕ) : K + 1 ≤ Fb K := by
  omega_nf

/-- **The unit against the budget of the specification.** -/
theorem Fb_le {K m : ℕ} (hm : 1 ≤ m) (hK : K ≤ 60 * (2 * m + 7)) :
    Fb K ≤ 40 * (K * (Nat.clog 2 m + 1) + 1) := by
  unfold Fb
  rcases Nat.eq_zero_or_pos K with rfl | hK0
  · have : Nat.clog 2 64 = 6 := by
      aesop
    simp [this]
  · have h1 : 64 * (K + 1) ≤ 131072 * m := by omega
    have h2 : Nat.clog 2 (64 * (K + 1)) ≤ 17 + Nat.clog 2 m := by
      have := Nat.clog_mono_right 2 h1
      have h3 := clog_mul_le 131072 m
      have h4 : Nat.clog 2 131072 = 17 := by
        aesop
      omega
    calc (K + 1) * (Nat.clog 2 (64 * (K + 1)) + 1) ≤ (2 * K) * (18 + Nat.clog 2 m) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ ≤ 40 * (K * (Nat.clog 2 m + 1) + 1) := by nlinarith

end

end OracleR

end Chazelle.Core
