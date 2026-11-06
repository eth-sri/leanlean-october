module

public import ADR11.Basic
public import ADR11.Coalescent.Forest

/-!
# The jump chain, the number of lineages, and the factorization of Kingman's coalescent

Kingman's coalescent on forests splits into two independent parts: the number of roots, a pure
death process with rate `k.choose 2` from `k` roots, and the sequence of merges, its jump chain,
which merges a uniformly chosen pair of roots at each step.

* `jumpMatrix`: the jump chain on forests (it stays put at forests with at most one root).
* `deathPow m k j`: the entry `(k, j)` of the `m`-th power of the generator of the pure death
  process, defined by the recursion `D^{m+1} = D · D^m`.
* `deathProb k j t`: the transition probability `exp(t D)(k, j)` of the pure death process, the
  paper's `g_kj(t)`.

## Main results

* `kingmanGenerator_pow_apply`, `kingmanTransition_apply`: for a forest `F` with `k` roots and any
  `G` with `j` roots, `exp(tQ)(F, G) = g_kj(t) · J^{k-j}(F, G)`.
* `coalescenceProb_eq_deathProb`: the paper's `g_ij`, defined from the coalescent on singletons,
  is `deathProb i j`.
* `jumpMatrix_pow_succ_apply`: first-step analysis of the jump chain.
* `deathProb_small`: the closed forms of `g_kj(t)` for `k ≤ 4`.
* `kingmanTransition_nonneg`, `kingmanTransition_sum`, `kingmanTransition_support`: the rows of
  `exp(tQ)` at forests are probability distributions on forests reachable by merges
  (nonnegativity holds at every `F`, by uniformization).
* `hasSum_deathProb`, `deathProb_sum_range`, `deathProb_sum_Icc`, `deathProb_le_one`: the series
  defining `g_kj(t)` converges, and the `g_kj(t)` form a probability distribution in `j`.
* `isForest_singletonForest`, `card_roots_singletonForest`: the starting point of `g_ij`.

## Implementation notes

Matrices carry no canonical norm, so the entries of `exp(tQ)` are computed from the exponential
series with the `L∞` operator norm (`Matrix.Norms.Operator`) opened locally, as in
`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`. Nonnegativity of `exp(tQ)` for `t ≥ 0`
uses uniformization: `tQ = tP - tc · 1` with `P = Q + c · 1` entrywise nonnegative.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- The jump chain of Kingman's coalescent on forests: from a forest with `k ≥ 2` roots, each of
its `k.choose 2` merges has probability `1 / (k choose 2)`; a forest with at most one root stays
put. -/
noncomputable def jumpMatrix : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ :=
  fun F G =>
    if #(roots F) ≤ 1 then (if G = F then 1 else 0)
    else if G ∈ merges F then (((#(roots F)).choose 2 : ℕ) : ℝ)⁻¹ else 0

/-- `deathPow m k j` is the entry `(k, j)` of `D^m`, where `D` is the generator of the pure death
process on `ℕ` with rate `k.choose 2` from `k` to `k - 1`. -/
def deathPow : ℕ → ℕ → ℕ → ℝ
  | 0, k, j => if k = j then 1 else 0
  | m + 1, k, j => ((k.choose 2 : ℕ) : ℝ) * (deathPow m (k - 1) j - deathPow m k j)

/-- The transition probabilities `exp(tD)(k, j)` of the pure death process: the probability that
`k` lineages coalesce into `j` lineages within time `t`. -/
noncomputable def deathProb (k j : ℕ) (t : ℝ) : ℝ :=
  ∑' m : ℕ, t ^ m / (m.factorial : ℝ) * deathPow m k j

theorem jumpMatrix_apply_of_isForest {F : Finset (Finset L)}
    (hk : 2 ≤ #(roots F)) (G : Finset (Finset L)) :
    jumpMatrix F G = if G ∈ merges F then (((#(roots F)).choose 2 : ℕ) : ℝ)⁻¹ else 0 := by unfold jumpMatrix; grind

/-! ### The jump chain -/

theorem fact_jumpMatrix_apply_of_le_one {F : Finset (Finset L)} (hk : #(roots F) ≤ 1)
    (G : Finset (Finset L)) : jumpMatrix F G = if G = F then 1 else 0 := by simp_all [jumpMatrix]

theorem fact_jumpMatrix_nonneg (F G : Finset (Finset L)) : 0 ≤ jumpMatrix F G := by aesop (add simp [jumpMatrix])

theorem fact_one_apply (F G : Finset (Finset L)) :
    (1 : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ) F G = if G = F then 1 else 0 := by
  by_cases h : G = F
  · aesop
  · rw [Matrix.one_apply_ne (Ne.symm h), ite_eq_right h]

/-- First-step analysis of the jump chain. -/
theorem jumpMatrix_pow_succ_apply {F : Finset (Finset L)} (hk : 2 ≤ #(roots F))
    (n : ℕ) (G : Finset (Finset L)) :
    (jumpMatrix ^ (n + 1)) F G =
      (((#(roots F)).choose 2 : ℕ) : ℝ)⁻¹ * ∑ F' ∈ merges F, (jumpMatrix ^ n) F' G := by
  rw [pow_succ', Matrix.mul_apply]
  simp_rw [jumpMatrix_apply_of_isForest hk, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]

theorem jumpMatrix_pow_of_card_roots_le_one {F : Finset (Finset L)} (hk : #(roots F) ≤ 1)
    (n : ℕ) (G : Finset (Finset L)) :
    (jumpMatrix ^ n) F G = if G = F then 1 else 0 := by
  induction n with
  | zero => rw [pow_zero, fact_one_apply]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [fact_jumpMatrix_apply_of_le_one hk, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ F), ih]

theorem fact_pow_nonneg {M : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ}
    (hM : ∀ F G, 0 ≤ M F G) (n : ℕ) (F G : Finset (Finset L)) : 0 ≤ (M ^ n) F G := by
  induction n generalizing F with
  | zero => rw [pow_zero, fact_one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_nonneg fun F' _ => mul_nonneg (hM F F') (ih F')

theorem jumpMatrix_pow_nonneg : ∀ (n : ℕ) (F G : Finset (Finset L)), 0 ≤ (jumpMatrix ^ n) F G :=
  fact_pow_nonneg fact_jumpMatrix_nonneg

/-- The jump chain only adds clusters, keeps the lineages, and removes one root per step until
one root is left. -/
theorem jumpMatrix_pow_support {F G : Finset (Finset L)} (hF : IsForest F) {n : ℕ}
    (h : (jumpMatrix ^ n) F G ≠ 0) :
    IsForest G ∧ F ⊆ G ∧ lineages G = lineages F ∧
      #(roots G) = if n < #(roots F) then #(roots F) - n else min (#(roots F)) 1 := by
  induction n generalizing F with
  | zero =>
    rw [pow_zero, fact_one_apply] at h
    split_ifs at h with hGF <;> grind
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply] at h
    obtain ⟨F', -, hF'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have hJ := left_ne_zero_of_mul hF'
    have hJn := right_ne_zero_of_mul hF'
    by_cases hk : #(roots F) ≤ 1
    · have hF'F : F' = F := by
        by_contra hne
        exact hJ (by rw [fact_jumpMatrix_apply_of_le_one hk, ite_eq_right hne])
      subst hF'F
      obtain ⟨h1, h2, h3, h4⟩ := ih hF hJn
      refine ⟨h1, h2, h3, ?_⟩
      rw [h4]
      split_ifs <;> omega
    · replace hk : 2 ≤ #(roots F) := by omega
      have hmem : F' ∈ merges F := by
        by_contra hne
        exact hJ (by rw [jumpMatrix_apply_of_isForest hk, ite_eq_right hne])
      obtain ⟨hF'f, hcard, hsub, -, hlin⟩ := hF.of_mem_merges hmem
      obtain ⟨h1, h2, h3, h4⟩ := ih hF'f hJn
      refine ⟨h1, hsub.trans h2, h3.trans hlin, ?_⟩
      rw [h4]
      split_ifs <;> omega

/-! ### The pure death process -/

theorem deathPow_succ (m k j : ℕ) :
    deathPow (m + 1) k j = ((k.choose 2 : ℕ) : ℝ) * (deathPow m (k - 1) j - deathPow m k j) :=
  rfl

/-- The pure death process never increases. -/
theorem deathPow_eq_zero_of_lt {k j : ℕ} (h : k < j) (m : ℕ) : deathPow m k j = 0 := by
  induction m generalizing k with
  | zero => simp [deathPow, h.ne]
  | succ m ih =>
    rw [deathPow_succ, ih (lt_of_le_of_lt (Nat.sub_le k 1) h), ih h]
    ring

theorem deathPow_self (m k : ℕ) : deathPow m k k = (-((k.choose 2 : ℕ) : ℝ)) ^ m := by
  induction m with
  | zero => simp [deathPow]
  | succ m ih =>
    rw [deathPow_succ, ih]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [deathPow_eq_zero_of_lt (Nat.sub_lt hk one_pos)]
      ring

theorem fact_abs_deathPow_le (m k j : ℕ) :
    |deathPow m k j| ≤ (2 * ((k.choose 2 : ℕ) : ℝ)) ^ m := by
  induction m generalizing k with
  | zero => simp [deathPow, pow_zero]; split_ifs <;> simp
  | succ m ih =>
    rw [deathPow_succ, abs_mul, pow_succ, abs_of_nonneg (by positivity)]
    have h1 : |deathPow m (k - 1) j| ≤ (2 * ((k.choose 2 : ℕ) : ℝ)) ^ m :=
      (ih (k - 1)).trans (pow_le_pow_left₀ (by positivity) (by gcongr; omega) m)
    linarith [mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add h1 (ih k))) (Nat.cast_nonneg (k.choose 2) : (0:ℝ) ≤ _)]

/-- The series defining `deathProb k j t` converges (absolutely). -/
theorem summable_deathProb (k j : ℕ) (t : ℝ) :
    Summable fun m : ℕ => t ^ m / (m.factorial : ℝ) * deathPow m k j := by
  refine Summable.of_norm_bounded
    (Real.summable_pow_div_factorial (|t| * (2 * ((k.choose 2 : ℕ) : ℝ)))) fun m => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast]
  calc |t| ^ m / (m.factorial : ℝ) * |deathPow m k j|
      ≤ |t| ^ m / (m.factorial : ℝ) * (2 * ((k.choose 2 : ℕ) : ℝ)) ^ m := by
        gcongr
        exact fact_abs_deathPow_le m k j
    _ = (|t| * (2 * ((k.choose 2 : ℕ) : ℝ))) ^ m / (m.factorial : ℝ) := by ring

theorem hasSum_deathProb (k j : ℕ) (t : ℝ) :
    HasSum (fun m : ℕ => t ^ m / (m.factorial : ℝ) * deathPow m k j) (deathProb k j t) :=
  (summable_deathProb k j t).hasSum

theorem fact_hasSum_exp_mul (x t : ℝ) :
    HasSum (fun m : ℕ => t ^ m / (m.factorial : ℝ) * x ^ m) (Real.exp (x * t)) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (x * t)
  rw [← Real.exp_eq_exp_ℝ] at h
  convert h using 1
  funext m
  rw [mul_pow]
  ring

theorem deathProb_self (k : ℕ) (t : ℝ) :
    deathProb k k t = exp (-(((k.choose 2 : ℕ) : ℝ) * t)) := by
  rw [← neg_mul]
  refine HasSum.tsum_eq ?_
  simp_rw [deathPow_self]
  exact fact_hasSum_exp_mul _ t

/-! ### The matrix exponential, entrywise -/

set_option backward.isDefEq.respectTransparency false in
/-- The entries of the exponential of a real matrix are given by the exponential series. -/
theorem hasSum_exp_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (i j : ι) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ))⁻¹ * (A ^ n) i j) (NormedSpace.exp A i j) := by
  open scoped Matrix.Norms.Operator in
  simpa using Pi.hasSum.mp (Pi.hasSum.mp (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A) i) j

/-- The powers of the generator at a forest factor through the number of roots and the jump
chain. -/
theorem kingmanGenerator_pow_apply {F : Finset (Finset L)} (hF : IsForest F) (m : ℕ)
    (G : Finset (Finset L)) :
    (kingmanGenerator ^ m) F G =
      deathPow m (#(roots F)) (#(roots G)) * (jumpMatrix ^ (#(roots F) - #(roots G))) F G := by
  induction m generalizing F with
  | zero =>
    simp [pow_zero, fact_one_apply, deathPow]
    split_ifs <;> simp_all [fact_one_apply]
  | succ m ih =>
    rw [pow_succ', hF.kingmanGenerator_mul_apply, ih hF, Finset.sum_congr rfl fun F' hF' => by
      rw [ih (hF.of_mem_merges hF').1, Nat.eq_sub_of_add_eq (hF.of_mem_merges hF').2.1], ← Finset.mul_sum, deathPow_succ]
    by_cases hk : #(roots F) ≤ 1
    · simp [Nat.choose_eq_zero_of_lt (by omega : #(roots F) < 2), merges_eq_empty_of_card_roots_le_one hk]
    by_cases hjk : #(roots G) < #(roots F)
    · rw [show #(roots F) - #(roots G) = #(roots F) - 1 - #(roots G) + 1 by omega, jumpMatrix_pow_succ_apply (by omega)]
      have : (((#(roots F)).choose 2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega : 2 ≤ #(roots F))).ne'
      field_simp
      ring
    · rw [deathPow_eq_zero_of_lt (show #(roots F) - 1 < #(roots G) by omega)]
      ring

/-- **Factorization.** For a forest `F` with `k` roots and `G` with `j` roots,
`exp(tQ)(F, G) = g_kj(t) · J^{k-j}(F, G)`. -/
theorem kingmanTransition_apply {F : Finset (Finset L)} (hF : IsForest F) (t : ℝ)
    (G : Finset (Finset L)) :
    kingmanTransition t F G =
      deathProb (#(roots F)) (#(roots G)) t * (jumpMatrix ^ (#(roots F) - #(roots G))) F G := by
  have h2 := (hasSum_deathProb (#(roots F)) (#(roots G)) t).mul_right
    ((jumpMatrix ^ (#(roots F) - #(roots G))) F G)
  refine (hasSum_exp_apply (t • kingmanGenerator (L := L)) F G).unique ?_
  convert h2 using 1
  funext n
  rw [smul_pow, Matrix.smul_apply, kingmanGenerator_pow_apply hF, smul_eq_mul]
  ring

theorem kingmanTransition_add (s t : ℝ) :
    kingmanTransition (L := L) (s + t) = kingmanTransition s * kingmanTransition t := by
  unfold kingmanTransition
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl _).smul_left s).smul_right t)

/-- A forest with at most one root does not change. -/
theorem kingmanTransition_of_card_roots_le_one {F : Finset (Finset L)} (hF : IsForest F)
    (hk : #(roots F) ≤ 1) (t : ℝ) (G : Finset (Finset L)) :
    kingmanTransition t F G = if G = F then 1 else 0 := by
  rw [kingmanTransition_apply hF]
  by_cases hG : G = F
  · subst hG
    rw [Nat.sub_self, pow_zero, Matrix.one_apply_eq, mul_one, ite_eq_left rfl, deathProb_self,
      Nat.choose_eq_zero_of_lt (by omega : #(roots G) < 2)]
    simp
  · rw [jumpMatrix_pow_of_card_roots_le_one hk, ite_eq_right hG, mul_zero]

theorem kingmanTransition_nonneg {t : ℝ} (ht : 0 ≤ t) (F G : Finset (Finset L)) :
    0 ≤ kingmanTransition t F G := by
  -- uniformization: `tQ = tP - tc · 1` with `P = Q + c · 1` entrywise nonnegative
  set c : ℝ := ∑ F : Finset (Finset L), (((#(roots F)).choose 2 : ℕ) : ℝ)
  set P := kingmanGenerator (L := L) + c • 1 with hPd
  have hP : ∀ F G, 0 ≤ P F G := fun F G => by
    have : (((#(roots F)).choose 2 : ℕ) : ℝ) ≤ c := single_le_sum
      (f := fun F : Finset (Finset L) => (((#(roots F)).choose 2 : ℕ) : ℝ))
      (fun F _ => by positivity) (mem_univ F)
    simp [hPd, kingmanGenerator, Matrix.add_apply, Matrix.smul_apply, fact_one_apply]
    split_ifs <;> simp_all
  have hsplit : t • kingmanGenerator = t • P + algebraMap ℝ _ (-(t * c)) := by
    rw [hPd, Algebra.algebraMap_eq_smul_one, smul_add, smul_smul, add_assoc, ← add_smul]; simp
  rw [kingmanTransition, hsplit,
    Matrix.exp_add_of_commute _ _ (Algebra.commute_algebraMap_right _ _), Matrix.algebraMap_eq_diagonal, Matrix.exp_diagonal, Matrix.mul_diagonal]
  refine mul_nonneg ((hasSum_exp_apply (t • P) F G).nonneg fun n => ?_)
    (by simp [← Real.exp_eq_exp_ℝ, Real.exp_nonneg])
  rw [smul_pow, Matrix.smul_apply, smul_eq_mul]
  exact mul_nonneg (by positivity) (mul_nonneg (pow_nonneg ht n) (fact_pow_nonneg hP n F G))

/-- The rows of the powers of the generator at a forest sum to `0` (except for the identity). -/
theorem fact_sum_kingmanGenerator_pow {F : Finset (Finset L)} (hF : IsForest F) (n : ℕ) :
    ∑ G, (kingmanGenerator ^ n) F G = if n = 0 then 1 else 0 := by
  induction n generalizing F with
  | zero => simp [fact_one_apply]
  | succ n ih =>
    simp_rw [pow_succ', Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [hF.sum_kingmanGenerator_mul, ih hF,
      Finset.sum_congr rfl (fun F' hF' => ih (hF.of_mem_merges hF').1),
      Finset.sum_const, hF.card_merges, nsmul_eq_mul, ite_eq_right (Nat.succ_ne_zero n)]
    ring

theorem kingmanTransition_sum {F : Finset (Finset L)} (hF : IsForest F) (t : ℝ) :
    ∑ G, kingmanTransition t F G = 1 := by
  refine (hasSum_sum (s := univ) fun G _ => hasSum_exp_apply (t • kingmanGenerator (L := L)) F G).unique ?_
  convert hasSum_ite_eq 0 (1 : ℝ) using 1
  funext n
  simp_rw [smul_pow, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← Finset.mul_sum, fact_sum_kingmanGenerator_pow hF]
  aesop

/-! ### Forests of singletons -/

/-! ### The pure death process: transition probabilities -/

theorem deathProb_eq_zero_of_lt {k j : ℕ} (h : k < j) (t : ℝ) : deathProb k j t = 0 := by
  simp [deathProb, deathPow_eq_zero_of_lt h]

/-! ### Small cases -/

theorem fact_deathProb_of_closed {k j : ℕ} (a b c d : ℝ)
    (h : ∀ m, deathPow m k j = a * 0 ^ m + b * (-1) ^ m + c * (-3) ^ m + d * (-6) ^ m) (t : ℝ) :
    deathProb k j t = a + b * exp (-t) + c * exp (-t) ^ 3 + d * exp (-t) ^ 6 := by
  have hs := (((fact_hasSum_exp_mul 0 t).mul_left a).add
    ((fact_hasSum_exp_mul (-1) t).mul_left b)).add ((fact_hasSum_exp_mul (-3) t).mul_left c)
      |>.add ((fact_hasSum_exp_mul (-6) t).mul_left d)
  have e : deathProb k j t =
      a * exp (0 * t) + b * exp (-1 * t) + c * exp (-3 * t) + d * exp (-6 * t) := by
    refine HasSum.tsum_eq ?_
    convert hs using 1
    funext m
    rw [h m]
    ring
  rw [e, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
  congr 1
  · simp_all
  · grind

theorem fact_deathPow_two_one (m : ℕ) :
    deathPow m 2 1 = 1 * 0 ^ m + (-1) * (-1) ^ m + 0 * (-3) ^ m + 0 * (-6) ^ m := by
  induction m <;> simp_all [deathPow, deathPow_self] <;> ring

theorem fact_deathPow_three_two (m : ℕ) :
    deathPow m 3 2 = 0 * 0 ^ m + 3 / 2 * (-1) ^ m + (-3 / 2) * (-3) ^ m + 0 * (-6) ^ m := by
  induction m <;> simp_all [deathPow, deathPow_self] <;> ring

theorem fact_deathPow_three_one (m : ℕ) :
    deathPow m 3 1 = 1 * 0 ^ m + (-3 / 2) * (-1) ^ m + 1 / 2 * (-3) ^ m + 0 * (-6) ^ m := by
  induction m <;> simp_all [deathPow, fact_deathPow_two_one] <;> ring

theorem fact_deathPow_four_three (m : ℕ) :
    deathPow m 4 3 = 0 * 0 ^ m + 0 * (-1) ^ m + 2 * (-3) ^ m + (-2) * (-6) ^ m := by
  induction m <;> simp_all [deathPow, deathPow_self, Nat.choose] <;> ring

theorem fact_deathPow_four_two (m : ℕ) :
    deathPow m 4 2 = 0 * 0 ^ m + 9 / 5 * (-1) ^ m + (-3) * (-3) ^ m + 6 / 5 * (-6) ^ m := by
  induction m <;> simp_all [deathPow, fact_deathPow_three_two, Nat.choose] <;> ring

theorem fact_deathPow_four_one (m : ℕ) :
    deathPow m 4 1 = 1 * 0 ^ m + (-9 / 5) * (-1) ^ m + 1 * (-3) ^ m + (-1 / 5) * (-6) ^ m := by
  induction m <;> simp_all [deathPow, fact_deathPow_three_one, Nat.choose] <;> ring

/-- The closed forms of `g_kj(t)` for `k ≤ 4`, in terms of `T = e^{-t}`. -/
theorem deathProb_small (t : ℝ) :
    let T := exp (-t)
    deathProb 0 0 t = 1 ∧ deathProb 1 1 t = 1 ∧
    deathProb 2 1 t = 1 - T ∧ deathProb 2 2 t = T ∧
    deathProb 3 1 t = 1 - 3 / 2 * T + 1 / 2 * T ^ 3 ∧ deathProb 3 2 t = 3 / 2 * T - 3 / 2 * T ^ 3 ∧
      deathProb 3 3 t = T ^ 3 ∧
    deathProb 4 1 t = 1 - 9 / 5 * T + T ^ 3 - 1 / 5 * T ^ 6 ∧
      deathProb 4 2 t = 9 / 5 * T - 3 * T ^ 3 + 6 / 5 * T ^ 6 ∧
      deathProb 4 3 t = 2 * T ^ 3 - 2 * T ^ 6 ∧ deathProb 4 4 t = T ^ 6 := by
  intro T
  have e (n : ℕ) : exp (-((n : ℝ) * t)) = T ^ n := by rw [← Real.exp_nat_mul]; ring_nf
  simp only [deathProb_self, fact_deathProb_of_closed _ _ _ _ fact_deathPow_two_one,
    fact_deathProb_of_closed _ _ _ _ fact_deathPow_three_one, fact_deathProb_of_closed _ _ _ _ fact_deathPow_three_two,
    fact_deathProb_of_closed _ _ _ _ fact_deathPow_four_one, fact_deathProb_of_closed _ _ _ _ fact_deathPow_four_two,
    fact_deathProb_of_closed _ _ _ _ fact_deathPow_four_three, e]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [T, Nat.choose] <;> ring

end ADR11
