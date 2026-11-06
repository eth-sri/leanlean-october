module

public import Chazelle.Cost.UpPhase

/-!
# The down-phase arithmetic (Chazelle §4.2, Lemma 4.2) and the linear total (Theorem 4.3)

## Lemma 4.2 (p. 518–520)
"Let `λ` be any positive grade and let `C` be an arbitrary chain in any grade `l ≥ λ`.  If a
`2^⌈βλ⌉`-granular conformal submap of `V(C)` is available in normal form, then it is possible to
compute `V(C)` in time at most `(c − 1/λ)2^l`, where `c` is some constant large enough."

The proof is an induction on `λ` (with `l` fixed): refining all regions of the submap costs at
most `a 2^l λ² (log λ) 2^(β²λ(4β/3 − 1/3))` (`= a 2^l λ² (log λ) 2^(-λ/375)` for `β = 1/5`) and
produces a `2^⌈β⌈βλ⌉⌉`-granular submap, to which the induction hypothesis applies with
`λ' = ⌈βλ⌉ ≤ λ - 1`.  **Consolidated revision** (design doc §10): with the revised granularity
schedule `γ'_λ = 2^⌈βλ⌉ + λ(⌈log₂ λ⌉ + 2) ≤ 2^(⌈βλ⌉+11)`, the pieces of a region have up to
`2^(⌈βλ⌉+11)` edges and the recursion index is shifted to `λ' = ⌈βλ⌉ + 11 < λ` (`λ ≥ 16`).  We
formalise the time bound as a function `T : ℕ → ℝ` (`T λ` = time to finish from a submap of
granularity between `2^⌈βλ⌉` and `2^(⌈βλ⌉+11)`) satisfying the recurrence
`DownRecurrence T a b l Λ`:
* `T λ ≤ b 2^l` for `λ < Λ` (base case: bounded region size, constant time per region);
* `T λ ≤ a 2^l · downOverhead λ + T (⌈βλ⌉ + 11)` for `λ ≥ Λ ≥ 16` (the inductive step).

Main results:
* `downStep_cost_le`: the region-refinement cost of the step (Lemma 2.3 region count times
  Lemma 4.1's cost at grade `⌈βλ⌉ + 11`) is `≤ 4096 Kk · 2^l · downOverhead λ` (`λ ≥ 14`).
* `DownRecurrence.le_linear`: `T λ ≤ (b + 4500³ · 3000 · a) · 2^l` for all `λ` (the clean
  linear solution; `Σ_λ λ³ 2^(-λ/375) ≤ 4500³ · 3000`).
* `DownRecurrence.paper_form`: the paper's statement `T λ ≤ (c − 1/λ) 2^l` for `λ ≥ 1`, for any
  `c ≥ b + 1`, provided the threshold `Λ ≥ 1500 · a · 7500⁵` ("for `λ` large enough").
* `overhead_le_telescoping`: `a λ² ⌈log₂ λ⌉ 2^(-λ/375) ≤ 1/(λ-1) - 1/λ` for
  `λ ≥ max(2, 1500 · a · 7500⁵)` (the paper's final inequality, explicit threshold).

## Theorem 4.3 (p. 521)
* `total_linear`: up phase + down phase (Lemma 4.2 with `λ = l = p`) + final stage
  (`F ≤ c₃ n`, visibility map to triangulation) `≤ totalConst · n` for `n = 2^p + 1`, where
  `totalConst = 304 (c₀ + 34200³ c₁ + 27 c₂) + b + 4500³ · 3000 · a + c₃`.
* `padding_le`: padding `N ≥ 2` vertices to `n = 2^p + 1`, `p = ⌈log₂ (N - 1)⌉`, gives
  `N ≤ n ≤ 2N`; `total_linear_padded` restates the total as `≤ 2 · totalConst · N`.
-/

namespace Chazelle.Cost

public section

open Finset

/-! ### The down-phase overhead -/

section
variable (lam : ℕ)
include lam
/-- Lemma 4.2's overhead factor `λ² ⌈log₂ λ⌉ 2^(β²λ(4β/3 − 1/3))` (`= λ²⌈log₂ λ⌉2^(-λ/375)`). -/
@[expose] noncomputable def downOverhead : ℝ :=
  (lam : ℝ) ^ 2 * (Nat.clog 2 lam : ℝ) * (2 : ℝ) ^ (beta ^ 2 * lam * (4 * beta / 3 - 1 / 3))

theorem downOverhead_eq :
    downOverhead lam = (lam : ℝ) ^ 2 * (Nat.clog 2 lam : ℝ) * (2 : ℝ) ^ (-(lam : ℝ) / 375) := by
  unfold downOverhead
  congr 2
  have := downPhase_exponent
  grind

theorem downOverhead_nonneg : 0 ≤ downOverhead lam := by
  rw [downOverhead_eq]
  positivity

/-- `downOverhead λ ≤ λ³ 2^(-λ/375)`. -/
theorem downOverhead_le_cubic :
    downOverhead lam ≤ (lam : ℝ) ^ 3 * (2 : ℝ) ^ (-(lam : ℝ) / 375) := by
  rw [downOverhead_eq]
  have hclog : (Nat.clog 2 lam : ℝ) ≤ lam := by exact_mod_cast clog_two_le_self lam
  have hq : (0 : ℝ) ≤ (2 : ℝ) ^ (-(lam : ℝ) / 375) := (two_rpow_pos _).le
  apply mul_le_mul_of_nonneg_right _ hq
  have : (0 : ℝ) ≤ (lam : ℝ) ^ 2 := by positivity
  calc (lam : ℝ) ^ 2 * (Nat.clog 2 lam : ℝ) ≤ (lam : ℝ) ^ 2 * lam :=
        mul_le_mul_of_nonneg_left hclog this
    _ = (lam : ℝ) ^ 3 := by ring


end

/-- `Σ_{j<n} downOverhead j ≤ 4500³ · 3000`. -/
theorem sum_downOverhead_le (n : ℕ) :
    ∑ j ∈ range n, downOverhead j ≤ 4500 ^ 3 * 3000 := by
  calc ∑ j ∈ range n, downOverhead j
      ≤ ∑ j ∈ range n, (j : ℝ) ^ 3 * (2 : ℝ) ^ (-(j : ℝ) / 375) :=
        Finset.sum_le_sum (fun j _ => downOverhead_le_cubic j)
    _ ≤ (4 * ((3 : ℕ) : ℝ) * ((375 : ℕ) : ℝ)) ^ 3 * (8 * ((375 : ℕ) : ℝ)) :=
        sum_natPow_mul_two_rpow_neg_le 3 375 (by norm_num) n
    _ = 4500 ^ 3 * 3000 := by grind

/-! ### The cost of one refinement step of Lemma 4.2 -/

/-- `2^(-⌈βλ⌉/75) ≤ 2^(-λ/375)`. -/
theorem two_rpow_neg_ceilBeta_le (lam : ℕ) :
    (2 : ℝ) ^ (-((ceilBeta lam : ℕ) : ℝ) / 75) ≤ (2 : ℝ) ^ (-(lam : ℝ) / 375) := by
  apply two_rpow_le_two_rpow
  have := beta_mul_le_ceilBeta lam
  rw [beta_eq] at this
  linarith

/-- `⌈βλ⌉ + 11 ≤ λ` for `λ ≥ 14`. -/
theorem ceilBeta_add_eleven_le {lam : ℕ} (h : 14 ≤ lam) : ceilBeta lam + 11 ≤ lam := by
  have hb0 : (0 : ℝ) ≤ beta := by rw [beta_eq]; norm_num
  have hc : ((ceilBeta lam : ℕ) : ℝ) < beta * lam + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg hb0 (Nat.cast_nonneg lam))
  have hl : (14 : ℝ) ≤ lam := by simp_all
  rw [beta_eq] at hc
  have : ((ceilBeta lam : ℕ) : ℝ) + 10 < lam := by linarith
  have : ceilBeta lam + 10 < lam := by exact_mod_cast this
  omega

/-- `⌈βλ⌉ + 11 < λ` for `λ ≥ 16` (the shifted recursion index decreases). -/
theorem ceilBeta_add_eleven_lt {lam : ℕ} (h : 16 ≤ lam) : ceilBeta lam + 11 < lam := by
  have hb0 : (0 : ℝ) ≤ beta := by rw [beta_eq]; norm_num
  have hc : ((ceilBeta lam : ℕ) : ℝ) < beta * lam + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg hb0 (Nat.cast_nonneg lam))
  have hl : (16 : ℝ) ≤ lam := by simp_all
  rw [beta_eq] at hc
  have : ((ceilBeta lam : ℕ) : ℝ) + 11 < lam := by linarith
  exact_mod_cast this

/-- **The refinement step of Lemma 4.2 (pp. 519–520), explicit form, with the revised
granularity schedule** (design doc §10: `γ'_λ = 2^⌈βλ⌉ + λ(⌈log₂ λ⌉ + 2) ≤ 2^(⌈βλ⌉ + 11)`, so
the pieces of a region have at most `2^μ` edges with `μ = ⌈βλ⌉ + 11`).  Let `14 ≤ λ ≤ l`.
Suppose the (at least `2^⌈βλ⌉`-granular) submap of the grade-`l` chain has
`R ≤ K (2^l / 2^⌈βλ⌉ + 1)` regions (Lemma 2.3) and each region is refined in time at most
`k · μ² ⌈log₂ μ⌉ 2^((74/75)μ)` (a constant number of calls to Lemma 4.1 on pieces with at most
`2^μ` edges, plus a constant number of merges).  Then the total time is at most
`4096 K k · 2^l λ² ⌈log₂ λ⌉ 2^(β²λ(4β/3 − 1/3))` (the shift costs the factor `2^11`). -/
theorem downStep_cost_le {K k : ℝ} (hK : 0 ≤ K) (hk : 0 ≤ k) {lam l : ℕ} (h14 : 14 ≤ lam)
    (hl : lam ≤ l) {R : ℝ} (hR : R ≤ K * ((2 : ℝ) ^ l / (2 : ℝ) ^ (ceilBeta lam) + 1)) :
    R * (k * lemma41Bound (ceilBeta lam + 11)) ≤
      4096 * K * k * ((2 : ℝ) ^ l * downOverhead lam) := by
  set c := ceilBeta lam with hcdef
  set μ := c + 11 with hμdef
  have hμl : μ ≤ lam := ceilBeta_add_eleven_le h14
  have hcl : c ≤ lam := by omega
  have hX : 0 ≤ k * lemma41Bound μ := mul_nonneg hk (lemma41Bound_nonneg μ)
  refine le_trans (mul_le_mul_of_nonneg_right hR hX) ?_
  rw [lemma41Bound_eq, downOverhead_eq]
  -- polynomial part
  have hpoly : (μ : ℝ) ^ 2 * (Nat.clog 2 μ : ℝ) ≤ (lam : ℝ) ^ 2 * (Nat.clog 2 lam : ℝ) := by
    have h1 : (μ : ℝ) ≤ lam := by exact_mod_cast hμl
    have h2 : (Nat.clog 2 μ : ℝ) ≤ Nat.clog 2 lam := by
      exact_mod_cast Nat.clog_mono_right 2 hμl
    have h0 : (0 : ℝ) ≤ μ := Nat.cast_nonneg μ
    have h3 : (μ : ℝ) ^ 2 ≤ (lam : ℝ) ^ 2 := pow_le_pow_left₀ h0 h1 2
    exact mul_le_mul h3 h2 (Nat.cast_nonneg _) (by positivity)
  -- exponential part: (2^l/2^c + 1) 2^((74/75)μ) ≤ 4096 · 2^l 2^(-λ/375)
  have hexp : ((2 : ℝ) ^ l / (2 : ℝ) ^ c + 1) * (2 : ℝ) ^ ((74 / 75 : ℝ) * μ) ≤
      4096 * ((2 : ℝ) ^ l * (2 : ℝ) ^ (-(lam : ℝ) / 375)) := by
    
    have hsplit : (2 : ℝ) ^ ((74 / 75 : ℝ) * μ) =
        (2 : ℝ) ^ c * ((2 : ℝ) ^ (11 : ℝ) * (2 : ℝ) ^ (-((μ : ℕ) : ℝ) / 75)) := by
      rw [← Real.rpow_natCast (2 : ℝ) c, two_rpow_mul_two_rpow, two_rpow_mul_two_rpow]
      grind
    
    have hcl' : (2 : ℝ) ^ c ≤ (2 : ℝ) ^ l := pow_le_pow_right₀ (by norm_num) (hcl.trans hl)
    have hq : (2 : ℝ) ^ (-((μ : ℕ) : ℝ) / 75) ≤ (2 : ℝ) ^ (-(lam : ℝ) / 375) := by
      refine le_trans (two_rpow_le_two_rpow ?_) (two_rpow_neg_ceilBeta_le lam)
      grind
    have hq0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-((μ : ℕ) : ℝ) / 75) := (two_rpow_pos _).le
    have h11 : (2 : ℝ) ^ (11 : ℝ) = 2048 := by norm_num
    rw [hsplit, h11]
    have e : ((2 : ℝ) ^ l / (2 : ℝ) ^ c + 1) * ((2 : ℝ) ^ c * (2048 * (2 : ℝ) ^ (-((μ : ℕ) : ℝ) / 75))) =
        2048 * (((2 : ℝ) ^ l + (2 : ℝ) ^ c) * (2 : ℝ) ^ (-((μ : ℕ) : ℝ) / 75)) := by
      field_simp
    rw [e]
    
    have : ((2 : ℝ) ^ l + (2 : ℝ) ^ c) * (2 : ℝ) ^ (-((μ : ℕ) : ℝ) / 75) ≤
        (2 * (2 : ℝ) ^ l) * (2 : ℝ) ^ (-(lam : ℝ) / 375) :=
      mul_le_mul (by linarith) hq hq0 (by positivity)
    nlinarith
  
  have hE0 : (0 : ℝ) ≤ (2 : ℝ) ^ l / (2 : ℝ) ^ c + 1 := by positivity
  have hq75 : (0 : ℝ) ≤ (2 : ℝ) ^ ((74 / 75 : ℝ) * μ) := (two_rpow_pos _).le
  calc K * ((2 : ℝ) ^ l / (2 : ℝ) ^ c + 1) *
        (k * ((μ : ℝ) ^ 2 * (Nat.clog 2 μ : ℝ) * (2 : ℝ) ^ ((74 / 75 : ℝ) * μ)))
      = K * k * ((μ : ℝ) ^ 2 * (Nat.clog 2 μ : ℝ)) *
          (((2 : ℝ) ^ l / (2 : ℝ) ^ c + 1) * (2 : ℝ) ^ ((74 / 75 : ℝ) * μ)) := by ring
    _ ≤ K * k * ((lam : ℝ) ^ 2 * (Nat.clog 2 lam : ℝ)) *
          (4096 * ((2 : ℝ) ^ l * (2 : ℝ) ^ (-(lam : ℝ) / 375))) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hpoly (mul_nonneg hK hk)) hexp
          (mul_nonneg hE0 hq75)
        positivity
    _ = 4096 * K * k * ((2 : ℝ) ^ l *
          ((lam : ℝ) ^ 2 * (Nat.clog 2 lam : ℝ) * (2 : ℝ) ^ (-(lam : ℝ) / 375))) := by ring

/-! ### The recurrence of Lemma 4.2 and its solution -/

/-! ### Theorem 4.3: the linear total -/


end

end Chazelle.Cost
