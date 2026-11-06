module

public import ImprovedExponents.Pipeline.ExactTriangle
public import ImprovedExponents.Optimum.PerCDensity
public import ImprovedExponents.PrunedEncoding.Costs
public import ThreeSumApsp.TacticsShort

@[expose] public section

/-!
# The general theorems

Four statements about programs of upstream's word RAM, each for all parameters of its kind and
each concluding `AllSolved δ` (Exact Triangle in `O(n^a)` for `a > 3 - δ`, 3SUM for `a > 2 - δ/2`,
the (min,+)-product and APSP for `a > 3 - δ/3`).

* `allSolved_paper`: the paper's algorithm with the paper's analysis, at any ratios `c = a/b`,
  `θ = p/q` that the program's regime test admits and any rational exponents `d`, `η` of the
  reduction: every `δ < d min(η, min(γ, 1/2 - q) - η)` with the paper's `γ = θ ln(1/ρ_c)/ln 4`.
* `allSolved_exact`: the same with the exact count of the leaves: any `γ < γX(c, θ)`.
* `allSolved_full`: the exact count together with the reduction that passes the true size of the
  middle part: every `δ` below the optimum `S(c) = R_c(Γ(c)) Γ(c)/2` of the method at the ratio
  `c`, for every `c ≥ 20`. The solver tests `D^r ≤ N^s` with `r/s` between `A(c)/ln 4` and `1/ε`
  (`ImprovedExponents.Pipeline.RegimeRS`), so no condition ties `c` to the regime of upstream's
  test `D^18 ≤ N`.
* `allSolved_pruned_of_claim`: the same with the thinness bound of pruned encodings, `R'_c`, for
  every `c ≥ 21`, from the claim `PrunedEncoderClaim`: a thin-product solver that computes the
  encodings of the leaves with at most `m` symbols `P₀` only. Its mathematics is in
  `ImprovedExponents.PrunedEncoding`; the program is `ImprovedExponents.PrunedProgram`, and the
  claim is proved in `ImprovedExponents.Pipeline.PrunedClaim` (`prunedEncoderClaim`), where the
  theorem becomes `allSolved_pruned`, without hypothesis.

The last three come from `explicitFrom_of_rat_tuple`, `explicitFrom_full` and
`explicitFrom_pruned_of_claim`,
which conclude `ExplicitFrom M δ 1` for every time model `M` that detects Lop-AE-SparseTri as
`lightModel` does and has the host of Theorem 17 at the true size of the middle part
(`MidHostRat M`); `lightModel` is one.
-/

namespace ImprovedExponents

open ThreeSumApsp Light Real

/-! ## The reduction as printed -/

section printed

variable {a b p q : ℕ}

end printed

/-! ## The reduction charged at the true size of the middle part -/

/-- `R(γ) ≤ 1/k` if `A ≥ k ln 4`. -/
theorem thinR_le_inv {A γ k : ℝ} (hk : 0 < k) (hA : k * log 4 ≤ A) (hγ : 0 ≤ γ) :
    thinR A γ ≤ 1 / k := by
  have h4 := log_four_pos
  unfold thinR
  rw [div_le_div_iff₀ tac_nlinarith hk]
  nlinarith

/-- **From an admissible tuple of rational numbers**, given thin-product claims at the two ratios
for all exponents below the exact one: Exact Triangle in every model with the host at the true size
of the middle part. -/
theorem explicitFrom_of_rat_tuple {A δ : ℝ} {c θ σ ε : ℚ}
    (hadm : AdmissibleX A (c : ℝ) (θ : ℝ) (σ : ℝ) (ε : ℝ)) (hσ : (1 / 2 : ℝ) < σ)
    (hε : (ε : ℝ) ≤ 1 / 16)
    (hthin : ∀ {a b p q : ℕ}, 1 ≤ b → 1 ≤ q → 10 * b < a → 1 ≤ p → 10 * p < 9 * q →
      (c : ℝ) = (a : ℝ) / b → (θ : ℝ) = (p : ℝ) / q →
      ∀ γ : ℝ, 0 < γ → γ < gammaX ((a : ℝ) / b) ((p : ℝ) / q) →
        ThinClaim lightModel ε γ (qOf ((p : ℝ) / q)))
    (hδ0 : 0 ≤ δ) (hδ : δ < tupleSaving (c : ℝ) (θ : ℝ) (σ : ℝ) (ε : ℝ)) (M : DetTimeModel)
    (hM : M.lopDetect = lightModel.lopDetect) (hhost : MidHostRat M) : ExplicitFrom M δ 1 := by
  have hc0 : (0 : ℚ) ≤ c := by
    have h : (0 : ℝ) ≤ c := by linarith [hadm.c_gt]
    exact_mod_cast h
  have hθ0 : (0 : ℚ) < θ := by exact_mod_cast hadm.θ_pos
  have hc_eq := rat_eq_div hc0
  have hθ_eq := rat_eq_div hθ0.le
  have hcab := mul_den_lt_num hc0 (by exact_mod_cast hadm.c_gt)
  have hθpq : 10 * θ.num.toNat < 9 * θ.den :=
    mul_num_lt_mul_den hθ0.le tac_norm_num (by exact_mod_cast hadm.θ_lt)
  refine explicitFrom_tuple hadm hσ hε (fun γ hγ0 hγ => ?_) hδ0 hδ M hM hhost
  have h := hthin c.den_pos θ.den_pos hcab (one_le_num_toNat hθ0) hθpq hc_eq hθ_eq γ hγ0
    tac_rwa [← hc_eq, ← hθ_eq]
  rwa [← hθ_eq] at h

/-- The optimum `R(Γ) Γ/2` is at most `1/2`: `γ ln 4 ≤ A + γ ln 4`. -/
theorem savingF_le_half {A γ : ℝ} (hA : 0 ≤ A) (hγ : 0 ≤ γ) : savingF A γ ≤ 1 / 2 := by
  have h4 := log_four_pos
  unfold savingF thinR
  rcases eq_or_lt_of_le (add_nonneg hA (mul_nonneg hγ h4.le)) with h | h
  · rw [← h, div_zero, zero_mul, zero_div]
    norm_num
  · rw [div_mul_eq_mul_div, div_div, div_le_div_iff₀ tac_positivity tac_norm_num]
    nlinarith

/-! ## Pruned encodings: the conditional theorem -/

/-- **The claim on the pruned encoder**: a thin-product solver with pruned encodings.
For all ratios `c = a/b > 10` and `θ = p/q ∈ (0, 0.9)`, every exponent `γ` below the exact one and
every `ε < R'_c(γ)`, the thin product is solved within `N² (log D + 1)²/D^γ + w D^q (log D + 1)`
on the instances with `D ≤ N^ε`. It is `thinClaim_gammaX` with the thinness bound `R'_c` of pruned
encodings in place of `R_c`, and without the restriction to the regime of the existing program's
test. `ImprovedExponents.PrunedEncoding.pruned_encoding` has the mathematics of the encoder, and
`ImprovedExponents.Pipeline.PrunedClaim` proves the claim for the program
`ImprovedExponents.PrunedProgram`. -/
def PrunedEncoderClaim : Prop :=
  ∀ {a b p q : ℕ}, 1 ≤ b → 1 ≤ q → 10 * b < a → 1 ≤ p → 10 * p < 9 * q → ∀ γ ε : ℝ, 0 < γ →
    γ < gammaX ((a : ℝ) / b) ((p : ℝ) / q) → ε < RcP ((a : ℝ) / b) γ →
    ThinClaim lightModel ε γ (qOf ((p : ℝ) / q))

/-- `(c/2) H(1/c) + (c - 1) ln 3 ≥ 16 ln 4` for `c ≥ 21`: already `20 ln 3 + (ln 21)/2 ≥ 16 ln 4`.
-/
theorem basePruned_ge_16 {c : ℝ} (hc : 21 ≤ c) : 16 * log 4 ≤ basePruned c := by
  refine le_trans ?_ (basePruned_monotoneOn (Set.mem_Ici.2 tac_norm_num) (Set.mem_Ici.2
    tac_linarith) hc)
  rw [basePruned_eq tac_norm_num]
  -- `cEntropy 21 = 21 ln 21 - 20 ln 20 ≥ ln 21`
  have hent : log 21 ≤ cEntropy 21 := by
    have h20 : log 20 ≤ log 21 := log_le_log tac_norm_num tac_norm_num
    unfold cEntropy
    simp only [negMulLog]
    norm_num
    nlinarith
  -- `ln 21 + 40 ln 3 ≥ 32 ln 4`, as `21 · 3^40 ≥ 4^32`
  have hnum : 32 * log 4 ≤ log 21 + 40 * log 3 := by
    have h : (4 : ℝ) ^ 32 ≤ 21 * 3 ^ 40 := by norm_num
    have hlog := log_le_log tac_positivity h
    rwa [log_pow, log_mul tac_norm_num tac_positivity, log_pow] at hlog
  norm_num
  linarith

/-- **The method with pruned encodings**, from the claim `PrunedEncoderClaim`: every saving
below the optimum `R'_c(Γ(c)) Γ(c)/2` at the ratio `c ≥ 21`, in every model with the host at the
true size of the middle part. -/
theorem explicitFrom_pruned_of_claim (hEnc : PrunedEncoderClaim) {c δ : ℝ} (hc : 21 ≤ c)
    (hδ0 : 0 ≤ δ) (hδ : δ < savingF (basePruned c) (Gam c)) (M : DetTimeModel)
    (hM : M.lopDetect = lightModel.lopDetect) (hhost : MidHostRat M) : ExplicitFrom M δ 1 := by
  have hc10 : (10 : ℝ) < c := by linarith
  obtain ⟨c', θ', σ', ε', hc1, -, hσ', hadm, hs⟩ :=
    exists_rat_tuple_basePruned hc10 hδ (c + 1) tac_linarith
  have hc'10 : (10 : ℝ) < c' := by linarith
  have hγX0 : 0 ≤ gammaX (c' : ℝ) (θ' : ℝ) :=
    (gammaX_pos hc'10 hadm.θ_pos (by linarith [hadm.θ_lt])).le
  have hε16 : (ε' : ℝ) ≤ 1 / 16 :=
    hadm.thin.le.trans (thinR_le_inv tac_norm_num (basePruned_ge_16 tac_linarith) hγX0)
  refine explicitFrom_of_rat_tuple hadm hσ' hε16
    (fun {a b p q} hb hq hcab hp hθ hceq hθeq γ hγ0 hγ => ?_) hδ0 hs M hM hhost
  refine hEnc hb hq hcab hp hθ γ ε' hγ0 hγ ?_
  have h2 : thinR (basePruned (c' : ℝ)) (gammaX (c' : ℝ) (θ' : ℝ))
      ≤ thinR (basePruned (c' : ℝ)) γ :=
    (thinR_strictAntiOn (basePruned_pos tac_linarith)).antitoneOn (Set.mem_Ici.2 hγ0.le)
      (Set.mem_Ici.2 hγX0) (by rw [hceq, hθeq]; exact hγ.le)
  rw [RcP, ← hceq]
  exact hadm.thin.trans_le h2

/-- **The method with pruned encodings**, from the claim `PrunedEncoderClaim`: every saving
below the optimum `R'_c(Γ(c)) Γ(c)/2` at the ratio `c`, for `c ≥ 21`. -/
theorem allSolved_pruned_of_claim (hEnc : PrunedEncoderClaim) {c δ : ℝ} (hc : 21 ≤ c) (hδ0 : 0 ≤ δ)
    (hδ : δ < savingF (basePruned c) (Gam c)) : AllSolved δ := by
  have hδ1 : δ ≤ 1 := by
    have h := savingF_le_half (basePruned_pos (c := c) tac_linarith).le
      (Gam_pos (c := c) tac_linarith).le
    linarith
  exact allSolved_of_explicitFrom hδ0 hδ1
    (explicitFrom_pruned_of_claim hEnc hc hδ0 hδ lightModel rfl midHostRat_light)

end ImprovedExponents