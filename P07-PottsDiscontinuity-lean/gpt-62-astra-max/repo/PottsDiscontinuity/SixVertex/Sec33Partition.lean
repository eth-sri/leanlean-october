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
    pfRoot (transferBlock N c n) ≤ LambdaMax c N := Finset.le_sup' (fun i : Fin (N + 1) => pfRoot (transferBlock N c i.val))
    (Finset.mem_univ (⟨n, Nat.lt_succ_of_le hn⟩ : Fin (N + 1)))

/-- `LambdaMax` is attained by one of the arrow-number blocks. -/
theorem exists_pfRoot_eq_LambdaMax :
    ∃ n ≤ N, pfRoot (transferBlock N c n) = LambdaMax c N := by
  have hself : LambdaMax c N ≤ LambdaMax c N := le_rfl
  obtain ⟨i, hi, hle⟩ := (Finset.le_sup'_iff
    (H := Finset.univ_nonempty)).mp hself
  grind [pfRoot_transferBlock_le_LambdaMax]

/-- Positivity of the maximal block Perron root. -/
theorem LambdaMax_pos (hc : 0 < c) : 0 < LambdaMax c N := by
  obtain ⟨n, hn, hmax⟩ := exists_pfRoot_eq_LambdaMax
  rw [← hmax]
  exact (transferBlock_perronFrobenius hc hn).1

section
variable (N : ℕ)

/-- The dimension of all fixed-cardinality state spaces sums to the dimension of the full state
space `Finset (Fin N)`, namely `2^N`. -/
noncomputable def stateCardEquiv :
    Finset (Fin N) ≃ Σ n : Fin (N + 1), State N n.val where
  toFun x := ⟨⟨x.card, by
      have hx := Finset.card_le_univ x
      rw [Fintype.card_fin] at hx
      exact Nat.lt_succ_of_le hx⟩, ⟨x, rfl⟩⟩
  invFun p := p.2.1
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨⟨n, hn⟩, ⟨s, hs⟩⟩
    change s.card = n at hs
    subst n
    rfl

theorem sum_state_card_eq_two_pow :
    (∑ n ∈ Finset.range (N + 1), Fintype.card (State N n)) = 2 ^ N := by
  have hcard := Fintype.card_congr (stateCardEquiv N)
  rw [Fintype.card_finset, Fintype.card_sigma] at hcard
  have hsum := Fin.sum_univ_eq_sum_range (fun n => Fintype.card (State N n)) (N + 1)
  grind [Fintype.card_fin]

end

/-- For a symmetric nonnegative matrix, every trace power is bounded by its dimension times the
`M`-th power of its largest eigenvalue. -/
theorem trace_pow_le_card_mul_pfRoot_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hnn : ∀ i j, 0 ≤ A i j) (M : ℕ) :
    (A ^ M).trace ≤ (Fintype.card ι : ℝ) * pfRoot A ^ M := by
  rw [trace_pow_eq_sum hA]
  calc
    _ ≤ ∑ _i, pfRoot A ^ M := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ |hA.eigenvalues i| ^ M := by
          have := le_abs_self (hA.eigenvalues i ^ M)
          grind
        _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) (abs_le_pfRoot_of_mem_spectrum hA hnn (hA.eigenvalues_mem_spectrum_real i)) M
    _ = _ := by simp

/-- Powers of a matrix with nonnegative entries still have nonnegative entries. -/
theorem matrix_pow_entry_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 ≤ A i j) :
    ∀ k i j, 0 ≤ (A ^ k) i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      by_cases h : i = j <;> simp [h]
  | succ k ih =>
      intro i j
      exact Finset.sum_nonneg fun l _ => mul_nonneg (ih i l) (hA l j)

/-- Positive diagonal entries persist under every matrix power when all entries are
nonnegative. -/
theorem matrix_pow_diag_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 ≤ A i j) (hdiag : ∀ i, 0 < A i i) :
    ∀ k i, 0 < (A ^ k) i i := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      intro i
      exact Finset.sum_pos' (fun j _ => mul_nonneg (matrix_pow_entry_nonneg hA k i j) (hA j i)) ⟨i, Finset.mem_univ i, mul_pos (ih i) (hdiag i)⟩

/-- A symmetric or nonsymmetric matrix with nonnegative entries and positive diagonal has
positive trace in every power. -/
theorem trace_pow_pos_of_nonneg_pos_diag {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hdiag : ∀ i, 0 < A i i) (M : ℕ) : 0 < (A ^ M).trace := Finset.sum_pos (fun i _ => matrix_pow_diag_pos hA hdiag M i) Finset.univ_nonempty

/-- Every fixed-arrow-number sector is nonnegative when `c ≥ 0`. -/
theorem Z6Vn_nonneg (hc : 0 ≤ c) (M n : ℕ) : 0 ≤ Z6Vn c N M n := Finset.sum_nonneg fun ω _ => by
    unfold w6V1 w6V
    positivity

/-- A fixed-arrow-number sector is bounded above by its state-space dimension times the block
Perron root to the `M`-th power. -/
theorem Z6Vn_le_card_mul_pfRoot_pow (hc : 0 < c) (hN : 0 < N) (hM : 0 < M)
    {n : ℕ} (hn : n ≤ N) :
    Z6Vn c N M n ≤ (Fintype.card (State N n)) *
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
  let : Nonempty (State N n) := ⟨packed hn⟩
  exact trace_pow_pos_of_nonneg_pos_diag (transferBlock_nonneg hc.le n)
    (fun x => by norm_num) M

/-- The full partition function dominates each fixed-arrow-number sector. -/
theorem Z6Vn_le_Z6V (hc : 0 ≤ c) (hM : 0 < M) {n : ℕ} (hn : n ≤ N) :
    Z6Vn c N M n ≤ Z6V c N M := by
  rw [Z6V_eq_sum_Z6Vn hM c]
  exact Finset.single_le_sum (fun k _ => Z6Vn_nonneg hc M k)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))

/-- The full six-vertex partition function has the uniform trace upper bound from the largest
block root. -/
theorem Z6V_le_two_pow_mul_LambdaMax_pow (hc : 0 < c) (hN : 0 < N) (hM : 0 < M) :
    Z6V c N M ≤ (2 ^ N) * LambdaMax c N ^ M := by
  rw [Z6V_eq_sum_Z6Vn hM c]
  calc
    _ ≤
        ∑ n ∈ Finset.range (N + 1),
          (Fintype.card (State N n)) * LambdaMax c N ^ M := by
      apply Finset.sum_le_sum
      intro n hn
      have hnle := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
      have hroot := pfRoot_transferBlock_le_LambdaMax (c := c) hnle
      have hρ := (transferBlock_perronFrobenius hc hnle).1
      calc
        _ ≤ (Fintype.card (State N n)) * pfRoot (transferBlock N c n) ^ M := (Z6Vn_le_card_mul_pfRoot_pow hc hN hM hnle)
        _ ≤ _ := by
          gcongr
    _ = (∑ n ∈ Finset.range (N + 1), (Fintype.card (State N n) : ℝ)) *
        LambdaMax c N ^ M := by rw [Finset.sum_mul]
    _ = _ := by
      have hcard : (∑ n ∈ Finset.range (N + 1),
          (Fintype.card (State N n) : ℝ)) = (2 ^ N) := by
        norm_cast
        exact sum_state_card_eq_two_pow N
      grind

/-- The sector growth rate at a maximizing block gives the full six-vertex free-energy rate. -/
theorem tendsto_log_Z6V (hc : 0 < c) (hN : 0 < N) :
    Tendsto (fun M : ℕ => (1 / M) * Real.log (Z6V c N M)) atTop
      (𝓝 (Real.log (LambdaMax c N))) := by
  obtain ⟨n, hn, hmax⟩ := exists_pfRoot_eq_LambdaMax (c := c)
  have hsector := tendsto_log_Z6Vn hc hN hn
  have hsector' : Tendsto (fun M : ℕ => (1 / M) * Real.log (Z6Vn c N M n))
      atTop (𝓝 (Real.log (LambdaMax c N))) := by
    grind
  have hconst : 0 < (2 ^ N : ℝ) := by positivity
  have hsmall : Tendsto (fun M : ℕ => (1 / M) * Real.log (2 ^ N))
      atTop (𝓝 0) := by simpa using tendsto_one_div_atTop_nhds_zero_nat.mul_const (Real.log (2 ^ N))
  have hupper' : Tendsto (fun M : ℕ => Real.log (LambdaMax c N) +
      (1 / M) * Real.log (2 ^ N)) atTop
      (𝓝 (Real.log (LambdaMax c N))) := by
    simpa using tendsto_const_nhds.add hsmall
  have hupper : Tendsto (fun M : ℕ => (1 / M) *
      Real.log ((2 ^ N) * LambdaMax c N ^ M)) atTop
      (𝓝 (Real.log (LambdaMax c N))) := by
    refine hupper'.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with M hM
    rw [Real.log_mul hconst.ne' (pow_ne_zero _ (LambdaMax_pos (N := N) hc).ne')]
    simp only [Real.log_pow]
    field_simp
    ring_nf
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hsector' hupper
  · filter_upwards [eventually_gt_atTop 0] with M hM
    have hlog := Real.log_le_log (Z6Vn_pos hc hN hM hn) (Z6Vn_le_Z6V hc.le hM hn)
    gcongr
  · filter_upwards [eventually_gt_atTop 0] with M hM
    have hfullpos := lt_of_lt_of_le (Z6Vn_pos hc hN hM hn)
      (Z6Vn_le_Z6V hc.le hM hn)
    have hup := Z6V_le_two_pow_mul_LambdaMax_pow hc hN hM
    gcongr

end PottsDiscontinuity.SixVertex
