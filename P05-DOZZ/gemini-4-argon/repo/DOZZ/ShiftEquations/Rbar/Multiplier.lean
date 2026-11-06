/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfUnitCrossingMultiplier
public import DOZZ.Statements.Defs.LFun
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The analytic γ/2-crossing multiplier on the diagonal

Along `α' = α = a` the Gauss parameters of the γ/2 crossing (`χ = γ/2`) are
`A = (γ/4)(2a + ε - Q - γ) - 1/2`, `B = (γ/4)(ε - γ/2)`, `C = 1 - (γ/2)(Q - a)`,
`A + B - C = y = γε/2 - γ²/4 - 1` and `2 + γ²/4 - γε/2 = 1 - y`. With `x = (2a + ε - γ/2 - 2Q)/γ`
one has `A = (γ²/4) x`, so on the crossing region `x > 0`
`Γ(x+1)/Γ(x) · l(A) = (4/γ²) Γ(A+1)/Γ(1-A)` and `l(y) l(1-y) = 1`. The multiplier
`gammaHalfUnitCrossingMultiplier` is therefore the restriction of the function
`T(z) = -(4π/γ²) Γ(A(z)+1) Γ(1-A(z))⁻¹ l(B) l(C(z))⁻¹ (l(-γ²/4) l(γε/2))⁻¹`, which is holomorphic on
`γ/2 < Re z < Q` (in particular across the crossing edge `x = 0`, where the real formula takes the
value `0/0`). As `ε ↓ γ/2`, `(ε - γ/2) l(B) → 4/γ`.
-/

@[expose] public section

open Filter Topology Set

namespace DOZZ.Proofs

/-- The Gauss parameter `A` on the diagonal, as a function of the charge. -/
noncomputable def crossA (γ ε : ℝ) (z : ℂ) : ℂ :=
  (γ / 4 : ℂ) * (2 * z + ε - Q γ - γ) - 1 / 2

/-- The Gauss parameter `C` on the diagonal. -/
noncomputable def crossC (γ : ℝ) (z : ℂ) : ℂ := 1 - (γ / 2 : ℂ) * (Q γ - z)

/-- The analytic γ/2-crossing multiplier on the diagonal. -/
noncomputable def crossingMultiplierDiag (γ ε : ℝ) (z : ℂ) : ℂ :=
  -(4 * Real.pi / γ ^ 2 : ℂ) * Complex.Gamma (crossA γ ε z + 1) *
    (Complex.Gamma (1 - crossA γ ε z))⁻¹ * lFun ((γ / 4 * (ε - γ / 2) : ℝ) : ℂ) *
    (lFun (crossC γ z))⁻¹ * (lFun (-(γ : ℂ) ^ 2 / 4) * lFun ((γ : ℂ) * ε / 2))⁻¹

/-- `l` at a real point is the real ratio of Gamma values. -/
theorem lFun_ofReal (r : ℝ) :
    lFun (r : ℂ) = ((Real.Gamma r / Real.Gamma (1 - r) : ℝ) : ℂ) := by
  unfold lFun
  rw [show (1 : ℂ) - r = ((1 - r : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal]
  push_cast
  ring

theorem lFun_ofReal_re (r : ℝ) : (lFun (r : ℂ)).re = Real.Gamma r / Real.Gamma (1 - r) := by
  rw [lFun_ofReal, Complex.ofReal_re]

/-- A real number strictly between two consecutive integers is not a non-positive integer. -/
theorem real_ne_neg_nat_of_frac {r} {k : ℤ} (h1 : (k : ℝ) < r) (h2 : r < k + 1) :
    ∀ m : ℕ, r ≠ -m := by
  intro m hm
  rw [hm] at h1 h2
  have : k < -(m : ℤ) := by exact_mod_cast h1
  have h4 : -(m : ℤ) < k + 1 := by exact_mod_cast h2
  omega


/-- The real `l`-function `l(r) = Γ(r)/Γ(1-r)`. -/
noncomputable def lR (r : ℝ) : ℝ := Real.Gamma r / Real.Gamma (1 - r)

theorem lFun_ofReal_eq_lR (r : ℝ) : lFun (r : ℂ) = (lR r : ℂ) := lFun_ofReal r

theorem lFun_ofReal_re_eq_lR (r : ℝ) : (lFun (r : ℂ)).re = lR r := lFun_ofReal_re r

/-- `l` is nonzero on `(0, 1)`. -/
theorem lR_ne_zero_of_mem_unit {r} (h0 : 0 < r) (h1 : r < 1) : lR r ≠ 0 :=
  div_ne_zero (Real.Gamma_pos_of_pos h0).ne' (Real.Gamma_pos_of_pos (by linarith)).ne'

/-- `l` is nonzero on `(-1, 0)`. -/
theorem lR_ne_zero_of_mem_neg {r} (h0 : -1 < r) (h1 : r < 0) : lR r ≠ 0 := by
  refine div_ne_zero (Real.Gamma_ne_zero (real_ne_neg_nat_of_frac (k := -1) ?_ ?_))
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  · push_cast
    linarith
  · push_cast
    linarith

/-- `l(y) l(1-y) = 1` on `(-1, 0)`. -/
theorem lR_mul_lR_one_sub {y} (h0 : -1 < y) (h1 : y < 0) : lR y * lR (1 - y) = 1 := by
  have : Real.Gamma (1 - y) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have := Real.Gamma_ne_zero (real_ne_neg_nat_of_frac (k := -1) (by push_cast; linarith) (by push_cast; linarith))
  unfold lR
  rw [sub_sub_cancel]
  field_simp

/-- The pure algebra of the multiplier identity, over opaque values. -/
theorem multiplier_algebra {μ π x γ GA1 G1A lA lB lC ly l1y lm le : ℝ} (hμ : μ ≠ 0)
    (hly : ly * l1y = 1) (hlA : x * lA = 4 / γ ^ 2 * (GA1 / G1A)) :
    μ⁻¹ * x * (-μ * π * (lA * lB) / (lC * ly * lm * le * l1y)) =
      -(4 * π / γ ^ 2) * GA1 * G1A⁻¹ * lB * lC⁻¹ * (lm * le)⁻¹ := by
  rw [(show lC * ly * lm * le * l1y = lC * lm * le * (ly * l1y) by ring), hly, mul_one]
  calc μ⁻¹ * x * (-μ * π * (lA * lB) / (lC * lm * le))
      = μ⁻¹ * μ * (-π * (x * lA) * lB / (lC * lm * le)) := by ring
    _ = -π * (4 / γ ^ 2 * (GA1 / G1A)) * lB / (lC * lm * le) := by
        rw [inv_mul_cancel₀ hμ, one_mul, hlA]
    _ = _ := by
        rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_inv]
        ring

/-- The bounds on the diagonal parameters. -/
theorem cross_bounds {γ ε : ℝ} (hγ : 0 < γ) (hε₁ : γ / 2 < ε)
    (hε₂ : ε < 2 / γ) :
    (-1 < γ * ε / 2 - γ ^ 2 / 4 - 1 ∧ γ * ε / 2 - γ ^ 2 / 4 - 1 < 0) ∧
      (0 < γ * ε / 2 ∧ γ * ε / 2 < 1) ∧ (-1 < -(γ ^ 2) / 4 ∧ -(γ ^ 2) / 4 < 0) ∧
      (0 < γ / 4 * (ε - γ / 2) ∧ γ / 4 * (ε - γ / 2) < 1) := by
  have h1 := mul_lt_mul_of_pos_left hε₁ hγ
  have h2 : γ * ε / 2 < 1 := by
    have := mul_lt_mul_of_pos_left hε₂ hγ
    rw [mul_div_assoc', mul_div_cancel_left₀ _ hγ.ne'] at this
    linarith
  have : 0 < γ ^ 2 := by positivity
  have h4 : γ ^ 2 < 4 := by nlinarith
  refine ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, h2⟩, ⟨by linarith, by linarith⟩,
    ⟨by nlinarith, by nlinarith⟩⟩



/-- The real closed form of the analytic multiplier at a real charge. -/
noncomputable def crossingMultiplierReal (γ ε a : ℝ) : ℝ :=
  -(4 * Real.pi / γ ^ 2) * Real.Gamma (γ ^ 2 / 4 * ((2 * a + ε - γ / 2 - 2 * Q γ) / γ) + 1) *
    (Real.Gamma (1 - γ ^ 2 / 4 * ((2 * a + ε - γ / 2 - 2 * Q γ) / γ)))⁻¹ *
    lR (γ / 4 * (ε - γ / 2)) * (lR (1 - γ / 2 * (Q γ - a)))⁻¹ *
    (lR (-(γ ^ 2) / 4) * lR (γ * ε / 2))⁻¹


/-- **The analytic multiplier at a real charge is the real closed form.** -/
theorem crossingMultiplierDiag_ofReal {γ} (hγ : 0 < γ) (ε a : ℝ) :
    crossingMultiplierDiag γ ε (a : ℂ) = (crossingMultiplierReal γ ε a : ℂ) := by
  have crossA_ofReal ε (a : ℝ) : crossA γ ε (a : ℂ) = ((γ ^ 2 / 4 * ((2 * a + ε - γ / 2 - 2 * Q γ) / γ) : ℝ) : ℂ) := by
    unfold crossA
    have := Complex.ofReal_ne_zero.mpr hγ.ne'
    rw [Q]
    push_cast
    field_simp
    ring
  unfold crossingMultiplierDiag crossingMultiplierReal crossC
  rw [crossA_ofReal, show (1 : ℂ) - (γ / 2 : ℂ) * (Q γ - (a : ℂ)) =
      ((1 - γ / 2 * (Q γ - a) : ℝ) : ℂ) by push_cast; ring,
    show (-(γ : ℂ) ^ 2 / 4) = ((-(γ ^ 2) / 4 : ℝ) : ℂ) by push_cast; ring,
    show ((γ : ℂ) * ε / 2) = ((γ * ε / 2 : ℝ) : ℂ) by push_cast; ring,
    lFun_ofReal_eq_lR, lFun_ofReal_eq_lR, lFun_ofReal_eq_lR, lFun_ofReal_eq_lR,
    show ((γ ^ 2 / 4 * ((2 * a + ε - γ / 2 - 2 * Q γ) / γ) : ℝ) : ℂ) + 1 =
      ((γ ^ 2 / 4 * ((2 * a + ε - γ / 2 - 2 * Q γ) / γ) + 1 : ℝ) : ℂ) by push_cast; ring,
    show (1 : ℂ) - ((γ ^ 2 / 4 * ((2 * a + ε - γ / 2 - 2 * Q γ) / γ) : ℝ) : ℂ) =
      ((1 - γ ^ 2 / 4 * ((2 * a + ε - γ / 2 - 2 * Q γ) / γ) : ℝ) : ℂ) by push_cast; ring,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal]
  push_cast
  ring

/-- **On the crossing region the unit multiplier is the analytic one.** -/
theorem gammaHalfUnitCrossingMultiplier_eq_diag {γ μ ε a : ℝ} (hγ : 0 < γ) (hμ : 0 < μ)
    (hε₁ : γ / 2 < ε) (hε₂ : ε < 2 / γ) (hx : 0 < (2 * a + ε - γ / 2 - 2 * Q γ) / γ) :
    (gammaHalfUnitCrossingMultiplier γ μ a ε a : ℂ) = crossingMultiplierDiag γ ε a := by
  have gammaHalfUnitCrossingMultiplier_diag_real : gammaHalfUnitCrossingMultiplier γ μ a ε a = -(4 * Real.pi / γ ^ 2) * Real.Gamma (γ ^ 2 / 4 * ((2 * a + ε - γ / 2 - 2 * Q γ) / γ) + 1) * (Real.Gamma (1 - γ ^ 2 / 4 * ((2 * a + ε - γ / 2 - 2 * Q γ) / γ)))⁻¹ * lR (γ / 4 * (ε - γ / 2)) * (lR (1 - γ / 2 * (Q γ - a)))⁻¹ * (lR (-(γ ^ 2) / 4) * lR (γ * ε / 2))⁻¹ := by
    have gaussParameters_diag {γ : ℝ} {ε : ℝ} {a : ℝ} (hγ : 0 < γ) : gaussParameterA γ (γ / 2) a ε a = γ ^ 2 / 4 * ((2 * a + ε - γ / 2 - 2 * Q γ) / γ) ∧ gaussParameterB γ (γ / 2) a ε a = γ / 4 * (ε - γ / 2) ∧ gaussParameterC γ (γ / 2) a = 1 - γ / 2 * (Q γ - a) ∧ gaussParameterA γ (γ / 2) a ε a + gaussParameterB γ (γ / 2) a ε a - gaussParameterC γ (γ / 2) a = γ * ε / 2 - γ ^ 2 / 4 - 1 := by
      unfold gaussParameterA gaussParameterB gaussParameterC Q
      refine ⟨by field_simp; ring, by field_simp; ring, by ring, by field_simp; ring⟩
    obtain ⟨hA, hB, hC, hy⟩ := gaussParameters_diag (ε := ε) (a := a) hγ
    obtain ⟨hyb, -, -, -⟩ := cross_bounds hγ hε₁ hε₂
    unfold gammaHalfUnitCrossingMultiplier gammaHalfCrossingMultiplier
    rw [(show (a + a + ε + γ / 2 - 2 * Q γ) / γ = (2 * a + ε - γ / 2 - 2 * Q γ) / γ + 1 by field_simp; ring), (show (a + a + ε - γ / 2 - 2 * Q γ) / γ = (2 * a + ε - γ / 2 - 2 * Q γ) / γ by ring_nf), (show Real.Gamma ((2 * a + ε - γ / 2 - 2 * Q γ) / γ + 1) / Real.Gamma ((2 * a + ε - γ / 2 - 2 * Q γ) / γ) = (2 * a + ε - γ / 2 - 2 * Q γ) / γ by rw [Real.Gamma_add_one hx.ne', mul_div_assoc, div_self (Real.Gamma_pos_of_pos hx).ne', mul_one]), hy, hA, hB, hC, (show 2 + γ ^ 2 / 4 - γ * ε / 2 = 1 - (γ * ε / 2 - γ ^ 2 / 4 - 1) by ring)]
    simp only [lFun_ofReal_re_eq_lR]
    exact multiplier_algebra hμ.ne' (lR_mul_lR_one_sub hyb.1 hyb.2) (by unfold lR; rw [Real.Gamma_add_one (show 0 < γ ^ 2 / 4 * ((2 * a + ε - γ / 2 - 2 * Q γ) / γ) by positivity).ne']; field_simp)
  rw [crossingMultiplierDiag_ofReal hγ,
    gammaHalfUnitCrossingMultiplier_diag_real]
  rfl

/-- The strip `γ/2 < Re z < Q` of the reflection charges. -/
def reflectionStrip (γ : ℝ) : Set ℂ := {z | γ / 2 < z.re ∧ z.re < Q γ}

theorem isOpen_reflectionStrip γ : IsOpen (reflectionStrip γ) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

/-- A complex number of positive real part is not a non-positive integer. -/
theorem ne_neg_nat_of_re_pos {w : ℂ} (h : 0 < w.re) : ∀ m : ℕ, w ≠ -m := by
  intro m hm
  rw [hm] at h
  simp only [Complex.neg_re, Complex.natCast_re] at h
  linarith


theorem one_sub_crossC_re γ (z : ℂ) : (1 - crossC γ z).re = γ / 2 * (Q γ - z.re) := by
  unfold crossC
  simp [Complex.mul_re]

/-- `l(w)⁻¹ = Γ(1-w) Γ(w)⁻¹`. -/
theorem lFun_inv w : (lFun w)⁻¹ = Complex.Gamma (1 - w) * (Complex.Gamma w)⁻¹ := by
  unfold lFun
  rw [inv_div, div_eq_mul_inv]

/-- **The analytic multiplier is holomorphic on the reflection strip** (for `ε > γ/2`). -/
theorem differentiableOn_crossingMultiplierDiag {γ ε} (hγ : 0 < γ) (hε₁ : γ / 2 < ε) :
    DifferentiableOn ℂ (crossingMultiplierDiag γ ε) (reflectionStrip γ) := by
  have crossA_add_one_re γ ε (z : ℂ) : (crossA γ ε z + 1).re = γ / 4 * (2 * z.re + ε - Q γ - γ) + 1 / 2 := by
    unfold crossA
    simp [Complex.mul_re]
    ring
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  have hApos : 0 < (crossA γ ε z + 1).re := by
    rw [crossA_add_one_re]
    have : γ / 4 * (2 * (γ / 2) + ε - Q γ - γ) < γ / 4 * (2 * z.re + ε - Q γ - γ) :=
      mul_lt_mul_of_pos_left (by linarith [hz.1]) (by positivity)
    have : γ / 4 * (2 * (γ / 2) + ε - Q γ - γ) + 1 / 2 = γ / 4 * (ε - γ / 2) := by
      rw [Q]
      field_simp
      ring
    have h3 : 0 < γ / 4 * (ε - γ / 2) := mul_pos (by positivity) (by linarith)
    linarith
  show DifferentiableAt ℂ (fun w => crossingMultiplierDiag γ ε w) z
  unfold crossingMultiplierDiag
  exact ((((differentiableAt_const _).mul ((Complex.differentiableAt_Gamma _ (ne_neg_nat_of_re_pos hApos)).comp z (by unfold crossA; fun_prop))).mul (by exact (Complex.differentiable_one_div_Gamma _).comp z (by unfold crossA; fun_prop))).mul (differentiableAt_const _)).mul
    (by simp_rw [lFun_inv]; exact ((Complex.differentiableAt_Gamma _ (ne_neg_nat_of_re_pos (by rw [one_sub_crossC_re]; exact mul_pos (by positivity) (by linarith [hz.2])))).comp z (show DifferentiableAt ℂ (fun w => 1 - crossC γ w) z by unfold crossC; fun_prop)).mul ((Complex.differentiable_one_div_Gamma _).comp z (by unfold crossC; fun_prop))) |>.mul (differentiableAt_const _)

end DOZZ.Proofs

end
