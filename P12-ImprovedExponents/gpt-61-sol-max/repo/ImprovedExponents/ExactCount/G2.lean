module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.RamArith
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

@[expose] public section

/-!
# The exact exponent of the leaf counts

For the recursion with `L = c m` levels, `m` of them inner, the number of leaves of order `d = δ m`
in a tile, relative to the number `M` of output strings, is `e^{m g₂(c, δ)}` up to a factor
polynomial in `L`. Here

  `g₂(c, δ) = ψ(c - 1) - ψ(c - 1 + δ) - ψ(1 - δ) + δ ln 9`,   `ψ(x) = x ln x`,

which is `c H((1 - δ)/c) - c H(1/c) + δ ln 9` with the entropy function `H`.
The paper bounds this count by `ρ_c^δ = (9/(c-1))^δ`, the tangent of `g₂(c, ·)` at `δ = 0`.

This file has the function `g₂`, its monotonicity in both arguments, and its value at the parameters
of a recursion: `e^{m g₂(L/m, t/m)}` is a quotient of powers of natural numbers.
-/

namespace ImprovedExponents

open Real Set

/-- The exponent `g₂(c, δ) = ψ(c - 1) - ψ(c - 1 + δ) - ψ(1 - δ) + δ ln 9` with `ψ(x) = x ln x`,
written with Mathlib's `Real.negMulLog x = -x ln x`. -/
noncomputable def g2 c δ :=
  negMulLog (c - 1 + δ) - negMulLog (c - 1) + negMulLog (1 - δ) + δ * log 9

/-- `g₂(c, ·)` is continuous. -/
theorem continuous_g2_right c : Continuous (g2 c) := by
  unfold g2
  fun_prop

/-- `g₂(·, δ)` is continuous. -/
theorem continuous_g2_left δ : Continuous fun c => g2 c δ := by
  unfold g2
  fun_prop

/-- `∂g₂/∂δ = ln(9 (1 - δ)/(c - 1 + δ))`. -/
theorem hasDerivAt_g2_right {c δ} (hc : 1 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    HasDerivAt (g2 c) (log (9 * (1 - δ) / (c - 1 + δ))) δ := by

  have h1 :=
    (hasDerivAt_negMulLog (by linarith : 0 < c - 1 + δ).ne').comp δ ((hasDerivAt_id δ).const_add (c - 1))
  have h2 :=
    (hasDerivAt_negMulLog (sub_pos.2 hδ1).ne').comp δ ((hasDerivAt_id δ).const_sub 1)
  have h3 :=
    (hasDerivAt_id δ).mul_const (log 9)

  refine (((h1.sub_const (negMulLog (c - 1))).add h2).add h3).congr_deriv ?_
  grind [log_div, log_mul]

/-- `∂g₂/∂c = ln((c - 1)/(c - 1 + δ))`. -/
theorem hasDerivAt_g2_left {c δ} (hc : 1 < c) (hδ : 0 ≤ δ) :
    HasDerivAt (fun c => g2 c δ) (log ((c - 1) / (c - 1 + δ))) c := by
  have hpos : 0 < c - 1 + δ := by linarith
  have h1 :=
    (hasDerivAt_negMulLog hpos.ne').comp c (((hasDerivAt_id c).sub_const 1).add_const δ)
  have h2 :=
    (hasDerivAt_negMulLog (sub_pos.2 hc).ne').comp c ((hasDerivAt_id c).sub_const 1)
  have h :=
    ((h1.sub h2).add_const (negMulLog (1 - δ))).add_const (δ * log 9)
  refine h.congr_deriv ?_
  rw [log_div (sub_pos.2 hc).ne' hpos.ne']
  ring

/-- `g₂(c, ·)` decreases on `[0, 1]` when `c ≥ 10`: its derivative `ln(9 (1 - δ)/(c - 1 + δ))` is
not positive. -/
theorem g2_antitoneOn_right {c} (hc : 10 ≤ c) : AntitoneOn (g2 c) (Icc 0 1) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) (continuous_g2_right c).continuousOn ?_ ?_
  · intro δ hδ
    rw [interior_Icc] at hδ
    exact (hasDerivAt_g2_right (by linarith) hδ.1 hδ.2).differentiableAt.differentiableWithinAt
  · intro δ hδ
    rw [interior_Icc] at hδ
    obtain ⟨hδ0, hδ1⟩ := hδ
    rw [(hasDerivAt_g2_right (by linarith) hδ0 hδ1).deriv]
    bound

/-- `g₂(·, δ)` decreases on `[1, ∞)` for `δ ≥ 0`: its derivative is
`ln((c - 1)/(c - 1 + δ)) ≤ 0`. -/
theorem g2_antitoneOn_left {δ} (hδ : 0 ≤ δ) : AntitoneOn (fun c => g2 c δ) (Ici 1) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 1) (continuous_g2_left δ).continuousOn ?_ ?_
  · intro c hc
    rw [interior_Ici] at hc
    exact (hasDerivAt_g2_left hc hδ).differentiableAt.differentiableWithinAt
  · intro c hc
    rw [interior_Ici] at hc
    have hc' : 1 < c := hc
    rw [(hasDerivAt_g2_left hc' hδ).deriv]
    bound

/-! ### The value at the parameters of a recursion -/

/-- `e^{ψ(n)} = n^n` for a natural number `n`. -/
theorem exp_neg_negMulLog_natCast (n : ℕ) : exp (-negMulLog n) = (n : ℝ) ^ n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · have hn' : (0 : ℝ) < n := mod_cast hn
    rw [negMulLog, neg_mul, neg_neg, exp_nat_mul, exp_log hn']

/-- `m ψ(x/m) = ψ(x) - x ln m`, as `m negMulLog(x/m) = negMulLog x + x ln m`. -/
theorem mul_negMulLog_div {m} (hm : 0 < m) x :
    m * negMulLog (x / m) = negMulLog x + x * log m := by
  grind [negMulLog_mul, negMulLog, log_inv]

variable {L m t : ℕ} (hm : 1 ≤ m) (hmL : m ≤ L) (ht : t ≤ m)

include L m t hm hmL ht in
/-- `m g₂(L/m, t/m)` in terms of `ψ` at natural numbers. -/
theorem mul_g2_div  :
    (m : ℝ) * g2 (L / m) (t / m)
      = negMulLog (L - m + t : ℕ) - negMulLog (L - m : ℕ) + negMulLog (m - t : ℕ)
        - negMulLog m + t * log 9 := by
  have hm0 : (0 : ℝ) < m := mod_cast hm
  have e1 : (L : ℝ) / m - 1 + t / m = ((L - m + t : ℕ) : ℝ) / m := by
    push_cast [Nat.cast_sub hmL]
    field_simp




  rw [g2, e1, (by
    grind
   : (L : ℝ) / m - 1 = ((L - m : ℕ) : ℝ) / m), (by
    ram_safe
   : 1 - (t : ℝ) / m = ((m - t : ℕ) : ℝ) / m), mul_add, mul_add, mul_sub, mul_negMulLog_div hm0, mul_negMulLog_div hm0,
    mul_negMulLog_div hm0, (by rw [negMulLog]; ring : negMulLog m = -((m : ℝ) * log m))]

  rw [(by field_simp : (m : ℝ) * ((t : ℝ) / m * log 9) = t * log 9)]
  linear_combination log m * (by
    simp_all
   : ((L - m + t : ℕ) : ℝ) - ((L - m : ℕ) : ℝ) + ((m - t : ℕ) : ℝ) = m)

include L m t hm hmL ht in
/-- `e^{m g₂(L/m, t/m)}` is a quotient of powers of natural numbers. -/
theorem exp_mul_g2_div  :
    exp (m * g2 (L / m) (t / m))
      = (9 : ℝ) ^ t * ((m : ℝ) ^ m * ((L - m : ℕ) : ℝ) ^ (L - m))
        / (((m - t : ℕ) : ℝ) ^ (m - t) * ((L - m + t : ℕ) : ℝ) ^ (L - m + t)) := by





  rw [mul_g2_div hm hmL ht, ← exp_neg_negMulLog_natCast (L - m + t), ← exp_neg_negMulLog_natCast (L - m), ← exp_neg_negMulLog_natCast (m - t), ← exp_neg_negMulLog_natCast m, ← (by
    rw [exp_nat_mul, exp_log (by norm_num)]
   : exp (t * log 9) = (9 : ℝ) ^ t), ← exp_add, ← exp_add, ← exp_add,
    ← exp_sub]
  congr 1
  ring

end ImprovedExponents
