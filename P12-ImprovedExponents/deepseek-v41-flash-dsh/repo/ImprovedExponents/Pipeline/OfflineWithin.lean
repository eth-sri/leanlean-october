module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.RealParameters
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Program
public import ThreeSumApsp.TacticsShort

@[expose] public section

/-!
# The time of the offline routine of Section 4, as one statement

The offline routine `offline32` of the upstream program `program31 G` preprocesses and then answers
one query for each wanted position. Its parameters `G : RatParams` are in the program text: the
ratios `c = a/b` and `θ = p/q` and the threshold `m₀` below which it computes inner products.

`OfflineWithinT t ε γ q` says that a routine with the running time `t N D w` takes, on every
instance with `1 ≤ D ≤ N^ε`, at most a constant times

  `N² (log D + 1)²/D^γ + w D^q (log D + 1)`

steps, `w` being the number of wanted positions; `OfflineWithin G ε γ q` is this for the time of
`offline32`. This is the only fact about running times that the solver built on a routine needs
(`ImprovedExponents.Pipeline.ThinClaim`).

Upstream proves it with the paper's exponent `γ = θ ln(1/ρ_c)/ln 4` (`offlineWithin_gammaOf`, a
restatement of `Light.Sec4.exists_ratParams` for parameters that are given rather than chosen).
-/

namespace ImprovedExponents

open Light.Sec4

/-- A routine with the running time `t N D w` takes at most a constant times
`N² (log D + 1)²/D^γ + w D^q (log D + 1)` steps (400 further steps included) on every instance with
`1 ≤ D ≤ N^ε`. -/
def OfflineWithinT (t : ℕ → ℕ → ℕ → ℕ) (ε γ q : ℝ) : Prop :=
  ∃ A : ℝ, ∀ N D₀ w : ℕ, 1 ≤ N → 1 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
    (t N D₀ w : ℝ) + 400 ≤ A * (preBound31 γ N D₀ + (w : ℝ) * queryBound31 q D₀)

section bounds

variable {N D₀ : ℕ}

-- The next six lemmas are adapted from upstream
-- `ThreeSumApsp/Programs/Sec4/ChoosingParameters/RealParameters.lean`, where they are private.

/-- `D ≤ N^ε` with `ε ≤ 1` gives `D ≤ N`. -/
theorem le_of_le_rpow {ε : ℝ} (hN : 1 ≤ N) (hε : ε ≤ 1) (h : (D₀ : ℝ) ≤ (N : ℝ) ^ ε) :
    D₀ ≤ N := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have : (D₀ : ℝ) ≤ (N : ℝ) :=
    h.trans ((Real.rpow_le_rpow_of_exponent_le hNR hε).trans_eq (Real.rpow_one _))
  exact_mod_cast this

/-- `D ≤ N^ε` with `ε γ ≤ 1` gives `D^γ ≤ N²`. -/
theorem rpow_le_sq {ε γ : ℝ} (hN : 1 ≤ N) (hγ : 0 ≤ γ) (hεγ : ε * γ ≤ 1)
    (h : (D₀ : ℝ) ≤ (N : ℝ) ^ ε) : (D₀ : ℝ) ^ γ ≤ (N : ℝ) ^ 2 := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc (D₀ : ℝ) ^ γ ≤ ((N : ℝ) ^ ε) ^ γ := Real.rpow_le_rpow tac_positivity h hγ
    _ = (N : ℝ) ^ (ε * γ) := by rw [← Real.rpow_mul tac_positivity]
    _ ≤ (N : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNR tac_linarith
    _ = (N : ℝ) ^ 2 := by norm_cast

/-- The bound on the preprocessing is at least 1 if `D^γ ≤ N²`. -/
theorem one_le_preBound31 {γ : ℝ} (hD : 1 ≤ D₀) (h : (D₀ : ℝ) ^ γ ≤ (N : ℝ) ^ 2) :
    1 ≤ preBound31 γ N D₀ := by
  have hDR : (1 : ℝ) ≤ D₀ := by exact_mod_cast hD
  have hlog := Real.log_nonneg hDR
  unfold preBound31
  rw [le_div_iff₀ (Real.rpow_pos_of_pos tac_linarith _), one_mul]
  exact h.trans (le_mul_of_one_le_right tac_positivity (one_le_pow₀ tac_linarith))

/-- The bound on a query is at least 1. -/
theorem one_le_queryBound31 {q : ℝ} (hD : 1 ≤ D₀) (hq : 0 ≤ q) : 1 ≤ queryBound31 q D₀ := by
  have hDR : (1 : ℝ) ≤ D₀ := by exact_mod_cast hD
  have hlog := Real.log_nonneg hDR
  exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hDR hq) tac_linarith

/-- A larger exponent of `D` in the denominator, and `log D` in place of `log D + 1`, make the
bound on the preprocessing smaller. -/
theorem le_preBound31 {γ γ' : ℝ} (hD : 1 ≤ D₀) (hγ : γ ≤ γ') :
    (N : ℝ) ^ 2 * Real.log (D₀ : ℝ) ^ 2 / (D₀ : ℝ) ^ γ' ≤ preBound31 γ N D₀ := by
  have hDR : (1 : ℝ) ≤ D₀ := by exact_mod_cast hD
  have hlog := Real.log_nonneg hDR
  have hsq : Real.log (D₀ : ℝ) ^ 2 ≤ (Real.log D₀ + 1) ^ 2 := pow_le_pow_left₀ hlog tac_linarith 2
  exact div_le_div₀ tac_positivity (mul_le_mul_of_nonneg_left hsq tac_positivity)
    (Real.rpow_pos_of_pos tac_linarith _) (Real.rpow_le_rpow_of_exponent_le hDR hγ)

/-- A smaller exponent of `D`, and `log D` in place of `log D + 1`, make the bound on a query
smaller. -/
theorem le_queryBound31 {q q' : ℝ} (hD : 1 ≤ D₀) (hq : q' ≤ q) :
    (D₀ : ℝ) ^ q' * Real.log (D₀ : ℝ) ≤ queryBound31 q D₀ := by
  have hDR : (1 : ℝ) ≤ D₀ := by exact_mod_cast hD
  have hlog := Real.log_nonneg hDR
  exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le hDR hq) tac_linarith hlog tac_positivity

end bounds

end ImprovedExponents