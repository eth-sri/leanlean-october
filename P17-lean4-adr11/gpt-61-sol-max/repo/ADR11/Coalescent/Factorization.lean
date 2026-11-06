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

variable {F G : Family L} {n k j : ℕ}

/-- The jump chain of Kingman's coalescent on forests: from a forest with `k ≥ 2` roots, each of
its `k.choose 2` merges has probability `1 / (k choose 2)`; a forest with at most one root stays
put. -/
noncomputable def jumpMatrix : Matrix (Family L) (Family L) ℝ :=
  fun F G =>
    if #(roots F) ≤ 1 then (if G = F then 1 else 0)
    else if G ∈ merges F then ((#(roots F)).choose 2 : ℝ)⁻¹ else 0

/-- First-step analysis of the jump chain. -/
theorem jumpMatrix_pow_succ_apply (hk : 2 ≤ #(roots F))
    (n : ℕ) (G : Family L) :
    (jumpMatrix ^ (n + 1)) F G =
      ((#(roots F)).choose 2 : ℝ)⁻¹ * ∑ F' ∈ merges F, (jumpMatrix ^ n) F' G := by
  rw [pow_succ', Matrix.mul_apply]
  simp_rw [jumpMatrix, ite_eq_right (by omega : ¬ #(roots F) ≤ 1), ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]

theorem jumpMatrix_pow_of_card_roots_le_one (hk : #(roots F) ≤ 1)
    (n : ℕ) (G : Family L) :
    (jumpMatrix ^ n) F G = if G = F then 1 else 0 := by
  induction n with
  | zero => simp [Matrix.one_apply, eq_comm]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [jumpMatrix, ite_eq_left hk, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ F), ih]

/-- The jump chain only adds clusters, keeps the lineages, and removes one root per step until
one root is left. -/
theorem jumpMatrix_pow_support (hF : IsForest F) (h : (jumpMatrix ^ n) F G ≠ 0) :
    IsForest G ∧ F ⊆ G ∧ lineages G = lineages F ∧
      #(roots G) = if n < #(roots F) then #(roots F) - n else min (#(roots F)) 1 := by
  induction n generalizing F with
  | zero =>
    simp_all [Matrix.one_apply]
  | succ n ih =>
    by_cases hk : #(roots F) ≤ 1
    · have hGF : G = F := by simpa [jumpMatrix_pow_of_card_roots_le_one hk] using h
      subst G
      refine ⟨hF, subset_rfl, rfl, ?_⟩
      split_ifs <;> omega
    · rw [jumpMatrix_pow_succ_apply (by omega)] at h
      obtain ⟨F', hmem, hJn⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul h)
      obtain ⟨hF'f, hcard, hsub, -, hlin⟩ := hF.of_mem_merges hmem
      obtain ⟨h1, h2, h3, h4⟩ := ih hF'f hJn
      refine ⟨h1, hsub.trans h2, h3.trans hlin, ?_⟩
      rw [h4]
      split_ifs <;> omega

/-! ### The pure death process -/

def spectrum : ℕ → ℕ → List (ℚ × ℕ)
  | 0, j => if j = 0 then [(1, 0)] else []
  | k + 1, j =>
    if j = k + 1 then [(1, (k + 1).choose 2)] else if 0 < j ∧ j ≤ k then
      let s := (spectrum k j).map fun p =>
        (((k + 1).choose 2 : ℚ) / (((k + 1).choose 2 : ℚ) - p.2) * p.1, p.2)
      s ++ [(-(s.map Prod.fst).sum, (k + 1).choose 2)]
    else []

theorem spectrum_mem {p : ℚ × ℕ} (hp : p ∈ spectrum k j) :
    p.2 ≤ k.choose 2 := by
  induction k generalizing p with
  | zero => grind [spectrum]
  | succ k ih =>
    simp [spectrum] at hp
    split_ifs at hp <;> grind

theorem spectrum_of_lt (h : k < j) : spectrum k j = [] := by
  cases k with
  | zero => simp [spectrum, show j ≠ 0 by omega]
  | succ k => simp [spectrum, show j ≠ k + 1 by omega,
      show ¬ (0 < j ∧ j ≤ k) by omega]

theorem spectrum_self (k : ℕ) : spectrum k k = [(1, k.choose 2)] := by
  cases k <;> simp [spectrum]

theorem spectrum_initial (k j : ℕ) :
    ((spectrum k j).map fun p => (p.1 : ℝ)).sum = if k = j then 1 else 0 := by
  cases k <;> simp [spectrum] <;> split_ifs <;>
    simp_all [Function.comp_def]

noncomputable def spectrumMoment (n k j : ℕ) : ℝ :=
  ((spectrum k j).map fun p => (p.1 : ℝ) * (-(p.2 : ℝ)) ^ n).sum

theorem spectrumMoment_succ (n k j : ℕ) :
    spectrumMoment (n + 1) k j = (k.choose 2 : ℝ) *
      (spectrumMoment n (k - 1) j - spectrumMoment n k j) := by
  cases k with
  | zero => cases j <;> simp [spectrumMoment, spectrum]
  | succ k =>
    by_cases hj0 : j = 0
    · subst j
      cases k <;> simp [spectrumMoment, spectrum]
    by_cases hself : k + 1 = j
    · subst j
      simp [spectrumMoment, spectrum_self, spectrum_of_lt (show k < k + 1 by omega), pow_succ]
      ring
    by_cases hkj : k + 1 < j
    · simp [spectrumMoment, spectrum_of_lt hkj, spectrum_of_lt (show k < j by omega)]
    have hj : 0 < j := by omega
    have hjk' : j ≤ k := by omega
    symm
    simp only [spectrumMoment]
    simp only [spectrum, ite_eq_right (Ne.symm hself), ite_eq_left (And.intro hj hjk')]
    push_cast
    simp
    simp only [sub_eq_add_neg, ← List.sum_map_mul_left, ← List.sum_map_mul_right, List.sum_neg, List.map_map, Function.comp_def, ← List.sum_map_add]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    have hn : ((1 + k).choose 2 : ℝ) - p.2 ≠ 0 := by
      have := spectrum_mem hp
      have hs : (1 + k).choose 2 = k + k.choose 2 := by
        simpa [add_comm] using Nat.choose_succ_succ k 1
      have hlt : p.2 < (1 + k).choose 2 := by omega
      exact sub_ne_zero.mpr (by exact_mod_cast hlt.ne')
    push_cast
    ring_nf
    field_simp [hn]
    ring

noncomputable def spectrumValue (k j : ℕ) (t : ℝ) : ℝ :=
  ((spectrum k j).map fun p => (p.1 : ℝ) * exp (-t) ^ p.2).sum

theorem hasSum_spectrum (k j : ℕ) (t : ℝ) :
    HasSum (fun n : ℕ => t ^ n / (n.factorial : ℝ) * spectrumMoment n k j)
      (spectrumValue k j t) := by
  simp_rw [spectrumMoment, ← List.sum_map_mul_left]
  unfold spectrumValue
  induction spectrum k j with
  | nil => simp
  | cons p s ih =>
    simp_all
    apply HasSum.add ?_ ih
    have h := NormedSpace.expSeries_div_hasSum_exp (-((p.2 : ℝ) * t))
    rw [← Real.exp_eq_exp_ℝ] at h
    convert h.mul_left (p.1 : ℝ) using 1
    · funext n
      rw [neg_mul_eq_neg_mul, mul_pow]
      ring
    · simp_all [← Real.exp_nat_mul]

open Filter Topology

theorem tendsto_spectrum (k j : ℕ) (hk : 1 ≤ k) :
    Tendsto (spectrumValue k j) atTop (𝓝 (if j = 1 then 1 else 0)) := by
  unfold spectrumValue
  convert (tendsto_list_sum (spectrum k j) fun p _ =>
    ((Real.tendsto_exp_comp_nhds_zero.mpr tendsto_neg_atTop_atBot).pow p.2).const_mul (p.1 : ℝ)) using 2
  symm
  simp [zero_pow_eq]
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hj0 : j = 0
    · simp_all [spectrum]
    by_cases hself : j = k + 1
    · subst j
      simp [spectrum_self, Nat.choose_eq_zero_iff]
    by_cases hjk : j ≤ k
    · have hc : (k + 1).choose 2 ≠ 0 := (Nat.choose_pos (by omega)).ne'
      simpa (config := { contextual := true }) [spectrum, hself,
        show 0 < j ∧ j ≤ k by omega, hc,
        List.map_map, Function.comp_def] using ih (by omega)
    · simp [spectrum, hself, hjk, show j ≠ 1 by omega]

/-! ### The matrix exponential, entrywise -/

set_option backward.isDefEq.respectTransparency false in
/-- The entries of the exponential of a real matrix are given by the exponential series. -/
theorem hasSum_matrix_exp_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (i j : ι) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ))⁻¹ * (A ^ n) i j) (NormedSpace.exp A i j) := by
  open scoped Matrix.Norms.Operator in
  simpa using (Pi.hasSum.mp (Pi.hasSum.mp (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A) i) j)

/-- The powers of the generator at a forest factor through the number of roots and the jump
chain. -/
theorem kingmanGenerator_pow_apply (hF : IsForest F) (m : ℕ)
    (G : Family L) :
    (kingmanGenerator ^ m) F G =
      spectrumMoment m (#(roots F)) (#(roots G)) * (jumpMatrix ^ (#(roots F) - #(roots G))) F G := by
  induction m generalizing F with
  | zero =>
    aesop (add simp [spectrumMoment, spectrum_initial, Matrix.one_apply])
  | succ m ih =>
    rw [pow_succ', Matrix.mul_apply, hF.sum_kingmanGenerator_mul, ih hF]
    rw [Finset.sum_congr rfl (by
      intro F' hF'
      obtain ⟨hF'f, hcard, -⟩ := hF.of_mem_merges hF'
      rw [ih hF'f, show #(roots F') = #(roots F) - 1 by omega]
    ), ← Finset.mul_sum, spectrumMoment_succ]
    by_cases hk : #(roots F) ≤ 1
    · have hlt : #(roots F) < 2 := by omega
      simp [Nat.choose_eq_zero_of_lt hlt, merges, powersetCard_eq_empty.2 hlt]
    · replace hk : 2 ≤ #(roots F) := by omega
      by_cases hjk : #(roots G) < #(roots F)
      · have hstep := jumpMatrix_pow_succ_apply hk (#(roots F) - 1 - #(roots G)) G
        rw [show #(roots F) - 1 - #(roots G) + 1 = #(roots F) - #(roots G) by omega] at hstep
        have hC : ((#(roots F)).choose 2 : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.choose_pos hk).ne'
        rw [hstep]
        field_simp
        ring
      · simp only [spectrumMoment,
          spectrum_of_lt (show #(roots F) - 1 < #(roots G) by omega), List.map_nil, List.sum_nil]
        ring

/-- **Factorization.** For a forest `F` with `k` roots and `G` with `j` roots,
`exp(tQ)(F, G) = g_kj(t) · J^{k-j}(F, G)`. -/
theorem kingmanTransition_apply (hF : IsForest F) (t : ℝ)
    (G : Family L) :
    kingmanTransition t F G =
      spectrumValue (#(roots F)) (#(roots G)) t * (jumpMatrix ^ (#(roots F) - #(roots G))) F G := by
  refine (hasSum_matrix_exp_apply (t • kingmanGenerator (L := L)) F G).unique ?_
  convert (
    (hasSum_spectrum (#(roots F)) (#(roots G)) t).mul_right
      ((jumpMatrix ^ (#(roots F) - #(roots G))) F G)
  ) using 1
  funext n
  rw [smul_pow, Matrix.smul_apply, kingmanGenerator_pow_apply hF, smul_eq_mul]
  ring

theorem kingmanTransition_add (s t : ℝ) :
    kingmanTransition (L := L) (s + t) = kingmanTransition s * kingmanTransition t := by
  unfold kingmanTransition
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl _).smul_left s).smul_right t)

/-- A forest with at most one root does not change. -/
theorem kingmanTransition_of_card_roots_le_one (hF : IsForest F)
    (hk : #(roots F) ≤ 1) (t : ℝ) (G : Family L) :
    kingmanTransition t F G = if G = F then 1 else 0 := by
  rw [kingmanTransition_apply hF, jumpMatrix_pow_of_card_roots_le_one hk]
  by_cases hG : G = F
  · subst G
    simp [spectrumValue, spectrum_self, Nat.choose_eq_zero_of_lt (by omega : #(roots F) < 2)]
  · simp_all

theorem kingmanTransition_nonneg {t : ℝ} (ht : 0 ≤ t) (F G : Family L) :
    0 ≤ kingmanTransition t F G := by
  -- uniformization: `tQ = tP - tc · 1` with `P = Q + c · 1` entrywise nonnegative
  set Q := kingmanGenerator (L := L) with hQ
  set c : ℝ := ↑((Fintype.card (Finset L)).choose 2)
  set P : Matrix (Family L) (Family L) ℝ := Q + c • 1 with hPdef
  have hP : ∀ F G, 0 ≤ P F G := by
    intro F G
    rw [hPdef, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, hQ]
    unfold kingmanGenerator
    by_cases h : G = F
    · subst h
      simp
      have : ((#(roots G)).choose 2 : ℝ) ≤ c := by
        dsimp only [c]
        exact_mod_cast Nat.choose_le_choose 2 (card_le_univ (roots G))
      linarith
    · simp_all [ite_eq_right (Ne.symm h)]
      split_ifs <;> norm_num
  have hsplit : t • Q =
      t • P + (-(t * c)) • 1 := by
    dsimp only [P]
    module
  show 0 ≤ NormedSpace.exp (t • Q) F G
  rw [hsplit, Matrix.exp_add_of_commute _ _ ((Commute.one_right _).smul_right _),
    Matrix.smul_one_eq_diagonal, Matrix.exp_diagonal, Matrix.mul_diagonal]
  refine mul_nonneg ?_ (by simp_all [← Real.exp_eq_exp_ℝ]; positivity)
  refine (hasSum_matrix_exp_apply (t • P) F G).nonneg fun n => ?_
  rw [smul_pow, Matrix.smul_apply, smul_eq_mul]
  exact mul_nonneg (by positivity) (mul_nonneg (pow_nonneg ht n) (Matrix.pow_apply_nonneg hP n F G))

/-- The rows of the powers of the generator at a forest sum to `0` (except for the identity). -/
private theorem fact_sum_kingmanGenerator_pow (hF : IsForest F) (n : ℕ) :
    ∑ G, (kingmanGenerator ^ n) F G = if n = 0 then 1 else 0 := by
  induction n generalizing F with
  | zero => simp [Matrix.one_apply]
  | succ n ih =>
    simp_rw [pow_succ', Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [hF.sum_kingmanGenerator_mul, ih hF,
      Finset.sum_congr rfl (fun F' hF' => ih (hF.of_mem_merges hF').1),
      Finset.sum_const, hF.card_merges, nsmul_eq_mul, ite_eq_right (Nat.succ_ne_zero n)]
    ring

theorem kingmanTransition_sum (hF : IsForest F) (t : ℝ) :
    ∑ G, kingmanTransition t F G = 1 := by
  refine (
    hasSum_sum (s := univ) fun G _ =>
      hasSum_matrix_exp_apply (t • kingmanGenerator (L := L)) F G
  ).unique ?_
  convert hasSum_ite_eq 0 (1 : ℝ) using 1
  funext n
  simp [smul_pow]
  simp [← Finset.mul_sum]
  rw [fact_sum_kingmanGenerator_pow hF]
  split_ifs with hn
  · subst hn; simp
  · simp

/-! ### Forests of singletons -/

/-! ### The pure death process: transition probabilities -/

end ADR11
