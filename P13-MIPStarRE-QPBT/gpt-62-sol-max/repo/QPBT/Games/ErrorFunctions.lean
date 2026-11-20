module

public import MIPStarRE.LDT.Basic.ParametersBase
public import Mathlib.Analysis.MeanInequalitiesPow

/-! # Polynomial error predicates

Shared quantitative predicates for the polynomial-error bounds in QPBT
chapters 12, 14, and 15.

## References

These are formalization-only auxiliaries for polynomially small QPBT error
functions. The one-parameter form includes the explicit square-root witnesses
in paper chapter 14; the two-parameter form is used by `lem:pasting` in paper
chapter 6.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open scoped BigOperators

/-- A nonnegative one-parameter error function bounded by a positive real power.

**Local fix:** The prefactor and exponent are quantified separately. Paper
chapter 14 explicitly obtains `sqrt ε` at
`14_analysis_of_the_pauli_basis_test.tex:508-520,649-676`, which the coupled
constant in the shorthand at `04_preliminaries.tex:26-29` cannot bound on all
positive inputs. The correction is documented in
`docs/paper-gaps/qpbt_polynomial-error-square-root.tex` and tracked by issue
Dengnifer/MIPStarRE-QPBT-bak#16. -/
def IsPolyErr (f : ℝ → ℝ) : Prop :=
  ∃ C r : ℝ, 1 ≤ C ∧ 0 < r ∧ ∀ x, 0 ≤ x →
    0 ≤ f x ∧ f x ≤ C * Real.rpow x r

/-- A nonnegative two-parameter error function bounded by a sum of positive
real powers.

**Local fix:** The prefactor and the two exponents are quantified separately,
and the bound is imposed on the closed nonnegative quadrant. The shorthand at
`04_preliminaries.tex:22-29` reads `poly` of several arguments as a single
power of their product, which forces the pasting error of `lem:pasting` at
`06_nonlocal_games_and_mipstar.tex:504-525` to tend to zero with the collision
error at every fixed positive consistency error; a two-dimensional strategy
refutes the resulting statement. A sum of separate positive powers vanishes
exactly when both errors vanish, and bounds the terms the imported proof of
Fact 4.35 produces. The correction is documented in
`docs/paper-gaps/qpbt_pasting-product-error.tex` and tracked by issue
Dengnifer/MIPStarRE-QPBT-bak#196. -/
def IsPolyErr₂ (f : ℝ → ℝ → ℝ) : Prop :=
  ∃ C r s : ℝ, 1 ≤ C ∧ 0 < r ∧ 0 < s ∧ ∀ x y, 0 ≤ x → 0 ≤ y →
    0 ≤ f x y ∧ f x y ≤ C * (Real.rpow x r + Real.rpow y s)

section

variable (q : ℕ)
include q

/-- The noise, field size, and finite-degree contributions to the two soundness errors. -/
noncomputable abbrev soundnessTail (n b ε : ℝ) : ℝ :=
  ε ^ b + (q : ℝ) ^ (-b) + (2 : ℝ) ^ (-(b * n))

theorem soundnessTail_nonneg (n b : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ soundnessTail q n b ε := by positivity

theorem rpow_noise_le_soundnessTail (n b ε : ℝ) :
    ε ^ b ≤ soundnessTail q n b ε := by
  exact le_add_of_nonneg_right (by positivity) |>.trans (le_add_of_nonneg_right (by positivity))

theorem rpow_field_le_soundnessTail (n b : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    (q : ℝ) ^ (-b) ≤ soundnessTail q n b ε :=
  (le_add_of_nonneg_left (Real.rpow_nonneg hε b)).trans (le_add_of_nonneg_right (by positivity))

end

theorem size_le_power_prefactor {n a : ℝ} (hn : 1 ≤ n) (ha : 1 ≤ a) : n ≤ a * n ^ a :=
  (Real.self_le_rpow_of_one_le hn ha).trans (le_mul_of_one_le_left (by positivity) ha)

/-- Taking a small power preserves the soundness envelope, scaling the noise exponent. -/
theorem rpow_soundnessEnvelope_le (q : ℕ) (n b : ℝ) {C ε t : ℝ}
    (hC : 1 ≤ C) (hε : 0 ≤ ε) (ht : 0 ≤ t) (ht₁ : t ≤ 1) :
    (C * soundnessTail q n b ε) ^ t ≤ C * soundnessTail q n (b * t) ε := by
  rw [Real.mul_rpow (by positivity) (soundnessTail_nonneg q n b hε)]
  gcongr
  · exact Real.rpow_le_self_of_one_le hC ht₁
  · unfold soundnessTail
    have h₁ := Real.rpow_nonneg hε b
    have h₂ := Real.rpow_nonneg (Nat.cast_nonneg q) (-b)
    have h₃ := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(b * n))
    refine (Real.rpow_add_le_add_rpow (add_nonneg h₁ h₂) h₃ ht ht₁).trans ?_
    grw [Real.rpow_add_le_add_rpow h₁ h₂ ht ht₁]
    rw [← Real.rpow_mul hε, ← Real.rpow_mul (Nat.cast_nonneg q),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [neg_mul, mul_right_comm b n t, le_refl]

end MIPStarRE.QPBT
