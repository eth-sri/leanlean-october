module

public import PottsDiscontinuity.SixVertex.BlockPerronFrobenius

/-!
# Six-vertex sector maxima and trace bounds

This file packages the finite-sector maximum of the block Perron roots and the trace estimates
used in §3.3.  The full partition function is a sum of the fixed-arrow-number sectors.
-/

@[expose] public section

open Finset Matrix Filter Topology PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

variable {N M : ℕ} {c : ℝ}

/-- The largest Perron root among the arrow-number blocks `V^[n]`, `0 ≤ n ≤ N`. -/
noncomputable def LambdaMax (c : ℝ) (N : ℕ) : ℝ :=
  (Finset.univ : Finset (Fin (N + 1))).sup' Finset.univ_nonempty
    (fun n => pfRoot (transferBlock N c n.val))

/-- Every block Perron root is bounded by `LambdaMax`. -/
theorem pfRoot_transferBlock_le_LambdaMax {n : ℕ} (hn : n ≤ N) :
    pfRoot (transferBlock N c n) ≤ LambdaMax c N := by
  unfold LambdaMax
  exact Finset.le_sup' (fun i : Fin (N + 1) => pfRoot (transferBlock N c i.val))
    (Finset.mem_univ (⟨n, Nat.lt_succ_of_le hn⟩ : Fin (N + 1)))

/-- `LambdaMax` is attained by one of the arrow-number blocks. -/
theorem exists_pfRoot_eq_LambdaMax :
    ∃ n ≤ N, pfRoot (transferBlock N c n) = LambdaMax c N := by
  have hself : LambdaMax c N ≤ LambdaMax c N := le_rfl
  unfold LambdaMax at hself
  obtain ⟨i, hi, hle⟩ := (Finset.le_sup'_iff (s := Finset.univ)
    (H := Finset.univ_nonempty) (f := fun n : Fin (N + 1) =>
      pfRoot (transferBlock N c n.val))).mp hself
  have hlow :=
    pfRoot_transferBlock_le_LambdaMax (N := N) (c := c)
      (Nat.lt_succ_iff.mp i.isLt)
  exact ⟨i.val, Nat.lt_succ_iff.mp i.isLt, le_antisymm hlow hle⟩

/-- Positivity of the maximal block Perron root. -/
theorem LambdaMax_pos (hc : 0 < c) : 0 < LambdaMax c N := by
  obtain ⟨n, hn, hmax⟩ := exists_pfRoot_eq_LambdaMax (c := c) (N := N)
  rw [← hmax]
  exact (transferBlock_perronFrobenius (N := N) hc hn).1

/-- The dimension of all fixed-cardinality state spaces sums to the dimension of the full state
space `Finset (Fin N)`, namely `2^N`. -/
noncomputable def stateCardEquiv (N : ℕ) :
    Finset (Fin N) ≃ Σ n : Fin (N + 1), State N n.val where
  toFun x := ⟨⟨x.card, by
      have hx := Finset.card_le_univ x
      rw [Fintype.card_fin] at hx
      exact Nat.lt_succ_of_le hx⟩, ⟨x, rfl⟩⟩
  invFun p := p.2.1
  left_inv _ := rfl
  right_inv p := by
    grind

theorem sum_state_card_eq_two_pow (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), Fintype.card (State N n)) = 2 ^ N := by
  have hcard := Fintype.card_congr (stateCardEquiv N)
  rw [Fintype.card_finset, Fintype.card_sigma] at hcard
  have hsum : (∑ i : Fin (N + 1), Fintype.card (State N i.val)) =
      ∑ n ∈ Finset.range (N + 1), Fintype.card (State N n) := by
    exact Fin.sum_univ_eq_sum_range (fun n => Fintype.card (State N n)) (N + 1)
  rw [Fintype.card_fin] at hcard
  calc
    (∑ n ∈ Finset.range (N + 1), Fintype.card (State N n)) =
        ∑ i : Fin (N + 1), Fintype.card (State N i.val) := hsum.symm
    _ = 2 ^ N := hcard.symm

/-- Every fixed-arrow-number sector is nonnegative when `c ≥ 0`. -/
theorem Z6Vn_nonneg (hc : 0 ≤ c) (M n : ℕ) : 0 ≤ Z6Vn c N M n := by
  unfold Z6Vn
  exact Finset.sum_nonneg fun ω _ => by
    unfold w6V1 w6V
    split_ifs <;> positivity

/-- A fixed-arrow-number sector is bounded above by its state-space dimension times the block
Perron root to the `M`-th power. -/
theorem Z6Vn_le_card_mul_pfRoot_pow (hc : 0 < c) (hN : 0 < N) (hM : 0 < M)
    {n : ℕ} (hn : n ≤ N) :
    Z6Vn c N M n ≤ (Fintype.card (State N n) : ℝ) *
      pfRoot (transferBlock N c n) ^ M := by
  rw [Z6Vn_eq_trace_block hN hM c n]
  let : Nonempty (State N n) := ⟨packed hn⟩
  exact trace_pow_le_card_mul_pfRoot_pow (transferBlock_isHermitian n)
    (transferBlock_nonneg hc.le n) M

/-- Every fixed-arrow-number sector with an admissible cardinality is strictly positive for
positive height. -/
theorem Z6Vn_pos (hc : 0 < c) (hN : 0 < N) (hM : 0 < M) {n : ℕ}
    (hn : n ≤ N) : 0 < Z6Vn c N M n := by
  rw [Z6Vn_eq_trace_block hN hM c n]
  exact transferBlock_trace_pos hc hn M

/-- The full partition function dominates each fixed-arrow-number sector. -/
theorem Z6Vn_le_Z6V (hc : 0 ≤ c) (hM : 0 < M) {n : ℕ} (hn : n ≤ N) :
    Z6Vn c N M n ≤ Z6V c N M := by
  rw [Z6V_eq_sum_Z6Vn hM c]
  exact Finset.single_le_sum (fun k _ => Z6Vn_nonneg (N := N) hc M k)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))

/-- The full six-vertex partition function has the uniform trace upper bound from the largest
block root. -/
theorem Z6V_le_two_pow_mul_LambdaMax_pow (hc : 0 < c) (hN : 0 < N) (hM : 0 < M) :
    Z6V c N M ≤ (2 ^ N : ℝ) * LambdaMax c N ^ M := by
  rw [Z6V_eq_sum_Z6Vn hM c]
  calc
    (∑ n ∈ Finset.range (N + 1), Z6Vn c N M n) ≤
        ∑ n ∈ Finset.range (N + 1),
          (Fintype.card (State N n) : ℝ) * LambdaMax c N ^ M := by
      apply Finset.sum_le_sum
      intro n hn
      have hnle : n ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
      have hbound := Z6Vn_le_card_mul_pfRoot_pow hc hN hM hnle
      have hroot := pfRoot_transferBlock_le_LambdaMax (N := N) (c := c) hnle
      have hρ := (transferBlock_perronFrobenius (N := N) hc hnle).1
      calc
        Z6Vn c N M n ≤ (Fintype.card (State N n) : ℝ) * pfRoot (transferBlock N c n) ^ M := hbound
        _ ≤ (Fintype.card (State N n) : ℝ) * LambdaMax c N ^ M := by
          gcongr
    _ = (∑ n ∈ Finset.range (N + 1), (Fintype.card (State N n) : ℝ)) *
        LambdaMax c N ^ M := by rw [Finset.sum_mul]
    _ = (2 ^ N : ℝ) * LambdaMax c N ^ M := by
      have hcard : (∑ n ∈ Finset.range (N + 1),
          (Fintype.card (State N n) : ℝ)) = (2 ^ N : ℝ) := by
        norm_cast
        exact sum_state_card_eq_two_pow N
      rw [hcard]

/-- The sector growth rate at a maximizing block gives the full six-vertex free-energy rate. -/
theorem tendsto_log_Z6V (hc : 0 < c) (hN : 0 < N) :
    Tendsto (fun M : ℕ => (1 / (M : ℝ)) * Real.log (Z6V c N M)) atTop
      (𝓝 (Real.log (LambdaMax c N))) := by
  obtain ⟨n, hn, hmax⟩ := exists_pfRoot_eq_LambdaMax (c := c) (N := N)
  have hsector := tendsto_log_Z6Vn (N := N) hc hN hn
  have hsector' : Tendsto (fun M : ℕ => (1 / (M : ℝ)) * Real.log (Z6Vn c N M n))
      atTop (𝓝 (Real.log (LambdaMax c N))) := by
    simp_all
  have hu := tendsto_scaled_log_mul_pow (C := 2 ^ N) (by positivity) (LambdaMax_pos (N := N) hc)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := fun M : ℕ => (1 / (M : ℝ)) * Real.log (Z6V c N M))
    (g := fun M : ℕ => (1 / (M : ℝ)) * Real.log (Z6Vn c N M n))
    (h := fun M : ℕ => (1 / (M : ℝ)) *
      Real.log ((2 ^ N : ℝ) * LambdaMax c N ^ M))
    hsector' hu
  · filter_upwards [eventually_gt_atTop 0] with M hM
    have hsectorpos := Z6Vn_pos (N := N) hc hN hM hn
    have hlog := Real.log_le_log hsectorpos (Z6Vn_le_Z6V (N := N) hc.le hM hn)
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  · filter_upwards [eventually_gt_atTop 0] with M hM
    have hsectorpos := Z6Vn_pos (N := N) hc hN hM hn
    have hfullpos := lt_of_lt_of_le hsectorpos
      (Z6Vn_le_Z6V (N := N) hc.le hM hn)
    have hup := Z6V_le_two_pow_mul_LambdaMax_pow (N := N) hc hN hM
    have hlog := Real.log_le_log hfullpos hup
    exact mul_le_mul_of_nonneg_left hlog (by positivity)

end PottsDiscontinuity.SixVertex
