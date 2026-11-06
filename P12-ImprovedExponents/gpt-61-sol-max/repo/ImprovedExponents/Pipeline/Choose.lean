module

public import Mathlib.Tactic
public import ImprovedExponents.Pipeline.ThinClaim
public import ImprovedExponents.Optimum.PerCBasic

@[expose] public section

/-!
# Choosing parameters below a saving

Small facts used when the parameters of the programs are fitted to a target saving `δ`.

* A thin-product claim stays true for a smaller exponent `γ` (`ThinClaim.mono_gamma`).
* A nonnegative rational is the quotient of two natural numbers (`rat_eq_div`), which is how
  rational exponents enter the program text.
* If `δ` is below the saving `ε min(u, min(γ, s) - u)`, it is still below it after `γ` is lowered a
  little and `ε` is replaced by a suitable smaller rational (`exists_gamma_rat_of_lt`).
* `min(2σ - 1, 1 - σ) ≤ 1/3`, which bounds every saving by `ε/3` (`min_le_third`).
-/

namespace ImprovedExponents

open Light.Sec4

/-- A thin-product claim with the exponent `γ` gives the claim with every smaller exponent. -/
theorem ThinClaim.mono_gamma {M} {ε γ γ' q} (h : ThinClaim M ε γ q)
    (hγ : γ' ≤ γ) : ThinClaim M ε γ' q := by
  obtain ⟨C, T, hT, hb⟩ := h
  refine ⟨max C 0, T, hT, fun N D w u hN hD hDN => ?_⟩
  have hDR : (1 : ℝ) ≤ D := mod_cast hD
  have  : preBound31 γ N D ≤ preBound31 γ' N D := by
    unfold preBound31
    exact div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos (by linarith) _)
      (Real.rpow_le_rpow_of_exponent_le hDR hγ)


  calc T N D w u ≤ C * (preBound31 γ N D + (w : ℝ) * queryBound31 q D) := hb N D w u hN hD hDN
    _ ≤ max C 0 * (preBound31 γ N D + (w : ℝ) * queryBound31 q D) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg (by unfold preBound31; positivity) (by unfold queryBound31; positivity))
    _ ≤ max C 0 * (preBound31 γ' N D + (w : ℝ) * queryBound31 q D) :=
        mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _)

variable {r : ℚ} (hr : 0 ≤ r)

include r hr in
/-- A nonnegative rational number is the quotient of two natural numbers. -/
theorem rat_eq_div  : (r : ℝ) = (r.num.toNat : ℝ) / (r.den : ℝ) := by

  rw [(mod_cast congrArg (Int.cast : ℤ → ℝ) (Int.toNat_of_nonneg (Rat.num_nonneg.2 hr)) : (r.num.toNat : ℝ) = (r.num : ℝ)), Rat.cast_def]

include r hr in
/-- `r < k/l` for natural `k`, `l` gives `l · num < k · den`. -/
theorem mul_num_lt_mul_den  {k l : ℕ} (hl : 0 < l)
    (h : (r : ℝ) < (k : ℝ) / l) : l * r.num.toNat < k * r.den := by


  rw [rat_eq_div hr, div_lt_div_iff₀ (mod_cast r.den_pos) (mod_cast hl)] at h

  exact_mod_cast (by linarith : (l : ℝ) * (r.num.toNat : ℝ) < (k : ℝ) * (r.den : ℝ))

end ImprovedExponents
