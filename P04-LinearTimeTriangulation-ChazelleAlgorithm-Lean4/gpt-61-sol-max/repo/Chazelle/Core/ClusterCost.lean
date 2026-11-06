module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.ClusterPhase2Exec

/-!
# WP-I, part 71: the cost bound

All the step bounds of the procedure, and the size `END - A0` of its work area, are at most
`clusterK · ((μ + E) (⌈log₂ (μ + E)⌉ + 1) + 1)`.
-/

namespace Chazelle.Core.Cluster

@[expose] public section

/-- The constant of the cost bound. -/
def clusterK : ℕ := 200000

section
variable (g : GV) (hμ : 0 < g.μ)
include hμ
theorem GV.two_pow_L_le : 2 ^ g.L ≤ 2 * (g.N + g.μ + 1) := by
  have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := g.N + g.μ + 1) (by omega)
  have hL : 0 < g.L := by
    have hP := g.two_pow_L
    grind
  have e : 2 ^ g.L = 2 * 2 ^ (g.L - 1) := by
    rw [← pow_succ']; simp_all +arith
  change 2 ^ (Nat.clog 2 (g.N + g.μ + 1)).pred < g.N + g.μ + 1 at h
  change 2 ^ g.L ≤ 2 * (g.N + g.μ + 1)
  rw [e]
  have : 2 ^ (g.L - 1) < g.N + g.μ + 1 := h
  omega

theorem GV.L_le :
    g.L ≤ Nat.clog 2 (g.μ + g.E) + 2 := by
  apply Nat.clog_le_of_le_pow
  have := Nat.le_pow_clog (b := 2) (by norm_num) (g.μ + g.E)
  simp_all [pow_add] <;> omega_nf


end

theorem cube_le (L : ℕ) : (L + 2) ^ 3 ≤ 64 * 2 ^ L := by
  induction L with
  | zero => norm_num
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · grind
    · have h2 := Nat.mul_le_mul h h
      have h3 := Nat.mul_le_mul h2 h
      have : (n + 1 + 2) ^ 3 ≤ 2 * (n + 2) ^ 3 := by ring_nf; nlinarith
      omega

/-- The number of split steps times their cost. -/
theorem q_bounds {μ k k' s L : ℕ} (hk : 1 ≤ k) (hμ : 0 < μ) (hμk : μ ≤ k ^ 3)
    (hk' : k' = min k μ) (hs : s = min (k' * k') μ) :
    2 * μ / s * k' ≤ 2 * μ ∧ 2 * μ / s ≤ 2 * μ ∧
      2 * μ / s * (L + 2) ≤ 2 * μ + 2 * (L + 2) ^ 2 := by
  have hk'1 : 1 ≤ k' := by omega
  have hk'μ : k' ≤ μ := by omega
  have hs1 : k' ≤ s := by
    rw [hs]; refine le_min ?_ hk'μ; nlinarith
  have hqs : 2 * μ / s * s ≤ 2 * μ := Nat.div_mul_le_self _ _
  refine ⟨le_trans (Nat.mul_le_mul_left _ hs1) hqs, Nat.div_le_self _ _, ?_⟩
  by_cases h : μ ≤ k' * k'
  · have e : s = μ := by omega
    have : 2 * μ / s = 2 := by rw [e]; exact Nat.mul_div_cancel _ hμ
    grind
  · push Not at h
    have e : s = k' * k' := by omega
    have hkk : k' = k := by
      omega
    rcases Nat.le_total (L + 2) s with h3 | h3
    · have := Nat.mul_le_mul_left (2 * μ / s) h3; omega
    · have hq : 2 * μ / s ≤ 2 * k := by
        apply Nat.div_le_of_le_mul
        rw [e, hkk]
        ring_nf <;> omega
      
      calc 2 * μ / s * (L + 2) ≤ 2 * k * (L + 2) := Nat.mul_le_mul_right _ hq
        _ ≤ 2 * (L + 2) * (L + 2) := by nlinarith
        _ ≤ 2 * μ + 2 * (L + 2) ^ 2 := by nlinarith

/-- The total cost of the procedure (steps of the phases, the labelling, the outputs and the
raise of the allocator). -/
def totalCost (g : GV) : ℕ := cost1 g + (cost2a g + ((120 * g.μ + 50 * g.N + 30) +
  (2 + (3 * (g.END - g.A0) + 2))))

set_option maxHeartbeats 4000000 in
theorem totalCost_le (g : GV) (hμ : 0 < g.μ) (hE : 0 < g.E) (hk : 1 ≤ g.k)
    (hμk : g.μ ≤ g.k ^ 3) :
    totalCost g ≤ clusterK * ((g.μ + g.E) * (Nat.clog 2 (g.μ + g.E) + 1) + 1) := by
  unfold totalCost cost1 cost2a clusterK
  set Λ := Nat.clog 2 (g.μ + g.E) + 1 with hΛ
  set X := g.μ + g.E with hX
  
  set Pp := X * Λ with hPp
  
  have hΛP : Λ ≤ Pp := Nat.le_mul_of_pos_left _ (by omega)
  have hN : g.N = 2 * g.E := rfl
  have hLl := g.L_le hμ
  have hL3 : g.L ≤ 3 * Λ := by omega
  have h2L := g.two_pow_L_le hμ
  have hU : g.U = g.N + g.μ + 2 ^ g.L + 3 := rfl
  have hU8 : g.U ≤ 8 * X := by omega
  have hEND : g.END - g.A0 = 54 * g.U + 2 * (g.L * g.U) := by
    have := g.END_eq; omega
  have T1 : g.μ * g.L ≤ 3 * Pp := by
    calc g.μ * g.L ≤ X * (3 * Λ) := Nat.mul_le_mul (by omega) hL3
      _ = 3 * Pp := by ring_nf <;> omega
  have T2 : g.N * g.L ≤ 6 * Pp := by
    calc g.N * g.L ≤ (2 * X) * (3 * Λ) := Nat.mul_le_mul (by omega) hL3
      _ = 6 * Pp := by ring_nf <;> omega
  have T3 : g.L * g.U ≤ 24 * Pp := by
    calc g.L * g.U ≤ (3 * Λ) * (8 * X) := Nat.mul_le_mul hL3 hU8
      _ = 24 * Pp := by grind
  obtain ⟨hq1, hq2, hq3⟩ := q_bounds (L := g.L) (k' := g.k') (s := g.s) hk hμ hμk rfl rfl
  set q := 2 * g.μ / g.s with hq
  have C3 : (g.L + 2) ^ 3 ≤ 384 * X := by
    have := cube_le g.L; omega
  
  
  have S2 : 34 * (q * (g.L + 2)) * (g.L + 2) ≤
      34 * (2 * g.μ + 2 * (g.L + 2) ^ 2) * (g.L + 2) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hq3)
  
  
  have S5 : splitC g.L g.k' * q = (34 * g.L + 34) * (g.L + 2) * q + 36 * g.L * q +
      36 * (q * g.k') + 340 * q := by unfold splitC; ring
  grind

end

end Chazelle.Core.Cluster
