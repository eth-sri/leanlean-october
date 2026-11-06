module

public import Mathlib

/-!
# The Bethe phase `Θ` for `Δ < -1`

Source: arXiv:1611.09877v2, equation (1.8) and footnote 2.  For `Δ < -1` the paper defines `Θ`
as "the unique continuous function `ℝ² → ℝ` with `Θ(0,0) = 0` and
`exp(-iΘ(x,y)) = e^{i(x-y)} (e^{-ix} + e^{iy} - 2Δ) / (e^{ix} + e^{-iy} - 2Δ)`".

Here `Θ` is given an explicit closed form.  Since `e^{ix} + e^{-iy} - 2Δ = a + ib` with
`a = cos x + cos y - 2Δ > 0` and `b = sin x - sin y`, and `e^{-ix} + e^{iy} - 2Δ` is its complex
conjugate, the phase `-arg` of the right-hand side of (1.8) is `y - x + 2 arg (a + ib)` with
`arg (a + ib) = arctan (b / a)` because `a > 0`:

  `Θ(Δ, x, y) = y - x + 2 arctan ((sin x - sin y) / (cos x + cos y - 2Δ))`.

The characterization in the source (continuity, `Θ(0,0) = 0`, the exponential identity (1.8),
uniqueness) is then proved as separate theorems:

* `theta_isBethePhase`, `eq_theta_of_isBethePhase`, `existsUnique_isBethePhase`;
* `analyticAt_theta` (joint real analyticity in `(Δ, x, y)` for `Δ < -1`) and consequences;
* the listed properties: antisymmetries, `Θ(x,x) = 0`, the `2π` period shifts in both variables,
  `Θ(π,y) - Θ(-π,y) = -2π`, and the limit `Δ → -∞` (`Θ(x,y) → y - x`).
-/

@[expose] public noncomputable section

open Complex Filter Topology

namespace PottsDiscontinuity.Bethe

/-! ### Generic helper lemmas -/

/-- `exp (2 i arctan t) = (1 + i t) / (1 - i t)`. -/
theorem exp_two_arctan_mul_I (t : ℝ) :
    Complex.exp (((2 * Real.arctan t : ℝ) : ℂ) * I) = (1 + (t : ℂ) * I) / (1 - (t : ℂ) * I) := by
  have hs : (0:ℝ) < 1 + t ^ 2 := by positivity
  have h1 : (1 - (t : ℂ) * I) ≠ 0 := fun h => by simpa using congrArg Complex.re h
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_two_mul, Real.sin_two_mul, Real.cos_arctan, Real.sin_arctan, eq_div_iff h1]
  have h4 : (1 + (t:ℂ)^2) ≠ 0 := by exact_mod_cast hs.ne'
  field_simp
  rw [Real.sq_sqrt hs.le]
  push_cast
  field_simp
  ring_nf
  simp
  ring

section
variable (x : ℝ)
/-- `exp (i x) = cos x + i sin x` for real `x`, with the factor `I` on the left. -/
theorem exp_I_mul_ofReal  :
    Complex.exp (I * (x : ℂ)) = (Real.cos x : ℂ) + (Real.sin x : ℂ) * I := by
  rw [mul_comm, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

/-- `exp (-(i x)) = cos x - i sin x` for real `x`. -/
theorem exp_neg_I_mul_ofReal  :
    Complex.exp (-(I * (x : ℂ))) = (Real.cos x : ℂ) - (Real.sin x : ℂ) * I := by
  simpa [sub_eq_add_neg] using exp_I_mul_ofReal (-x)
end

/-- Uniqueness of continuous lifts: two continuous real functions on a preconnected space with
the same `x ↦ exp (i x)` which agree at one point are equal. -/
theorem eq_of_exp_eq {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] {f g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ p, Complex.exp ((f p : ℂ) * I) = Complex.exp ((g p : ℂ) * I)) (p₀ : X)
    (h0 : f p₀ = g p₀) : f = g := by
  funext p
  have := (isPreconnected_univ (α := X)).constant_of_mapsTo Int.isClosedEmbedding_coe_real.isEmbedding.isInducing.isDiscrete_range (by fun_prop : Continuous (fun p => (f p - g p) / (2 * Real.pi))).continuousOn
    (fun p _ => by
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (h p)
      refine ⟨n, ?_⟩
      have := congrArg Complex.im hn
      simp at this
      field_simp; linarith) (Set.mem_univ p) (Set.mem_univ p₀)
  grind [Real.pi, absurd]

/-- `Real.arctan` is real analytic everywhere. -/
@[fun_prop] theorem analyticAt_real_arctan {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {z : E} (hf : AnalyticAt ℝ f z) : AnalyticAt ℝ (fun x => Real.arctan (f x)) z := by
  have h1 : AnalyticAt ℂ Complex.arctan (f z : ℂ) := by
    unfold Complex.arctan
    have hden : (1 - (f z:ℂ) * I) ≠ 0 := fun h => by simpa using congrArg Complex.re h
    have : ((1 + (f z:ℂ) * I) / (1 - (f z:ℂ) * I)) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      by_cases ht : f z = 0
      · simp [ht]
      · right; simp [Complex.div_im, Complex.normSq]; field_simp; grind
    fun_prop
  exact (by simpa [← Complex.ofReal_arctan] using h1.re_ofReal : AnalyticAt ℝ Real.arctan (f z)).comp hf

attribute [fun_prop] analyticAt_fst analyticAt_snd

/-! ### Definition of `Θ` -/

section
variable (Δ x y : ℝ)
/-- The Bethe phase `Θ_Δ(x, y)` of arXiv:1611.09877v2, (1.8), for `Δ < -1` (the formula is
total in `Δ`, but it is the Bethe phase only for `Δ < -1`; see `theta_isBethePhase`):
`Θ(Δ, x, y) = y - x + 2 arctan ((sin x - sin y) / (cos x + cos y - 2Δ))`. -/
def theta  : ℝ :=
  y - x + 2 * Real.arctan ((Real.sin x - Real.sin y) / (Real.cos x + Real.cos y - 2 * Δ))

/-- The right-hand side of (1.8):
`e^{i(x-y)} (e^{-ix} + e^{iy} - 2Δ) / (e^{ix} + e^{-iy} - 2Δ)`. -/
def thetaRhs  : ℂ :=
  Complex.exp (I * ((x : ℂ) - y)) *
    ((Complex.exp (-(I * x)) + Complex.exp (I * y) - 2 * (Δ : ℂ)) /
      (Complex.exp (I * x) + Complex.exp (-(I * y)) - 2 * (Δ : ℂ)))
end

section
variable {Δ : ℝ} (hΔ : Δ < -1)
include hΔ
/-- The denominator `cos x + cos y - 2Δ = Re (e^{ix} + e^{-iy} - 2Δ)` is positive for `Δ < -1`. -/
theorem cos_add_cos_sub_pos (x y : ℝ) :
    0 < Real.cos x + Real.cos y - 2 * Δ := by
  have := Real.neg_one_le_cos x
  have := Real.neg_one_le_cos y
  linarith

/-- Continuity of `Θ_Δ` on `ℝ²` for fixed `Δ < -1`. -/
theorem continuous_theta  :
    Continuous (fun p : ℝ × ℝ => theta Δ p.1 p.2) := by
  unfold theta; fun_prop (disch := exact fun p => (cos_add_cos_sub_pos hΔ p.1 p.2).ne')

/-- The exponential identity (1.8): `exp (-i Θ(x,y)) = e^{i(x-y)} (e^{-ix} + e^{iy} - 2Δ) /
(e^{ix} + e^{-iy} - 2Δ)` for `Δ < -1`. -/
theorem exp_neg_I_theta (x y : ℝ) :
    Complex.exp (-(I * (theta Δ x y : ℂ))) = thetaRhs Δ x y := by
  have ha : ((Real.cos x + Real.cos y - 2 * Δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (cos_add_cos_sub_pos hΔ x y).ne'
  rw [show -(I * (theta Δ x y : ℂ)) = I * (x - y) - ((2 * Real.arctan ((Real.sin x - Real.sin y) / (Real.cos x + Real.cos y - 2 * Δ)) : ℝ) : ℂ) * I by simp [theta]; ring, Complex.exp_sub, exp_two_arctan_mul_I, thetaRhs]
  simp only [exp_I_mul_ofReal, exp_neg_I_mul_ofReal]
  push_cast at ha ⊢
  field_simp
  ring
end

/-! ### Analyticity -/

section
variable {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ)
include hΔ
/-- Joint real analyticity of `(Δ, x, y) ↦ Θ_Δ(x, y)` at every point with `Δ < -1`. -/
theorem analyticAt_theta  :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => theta p.1 p.2.1 p.2.2) (Δ, x, y) := by
  unfold theta; fun_prop (disch := exact (cos_add_cos_sub_pos hΔ x y).ne')

/-- For fixed `Δ < -1`, `(x, y) ↦ Θ_Δ(x, y)` is real analytic. -/
theorem analyticAt_theta_xy  :
    AnalyticAt ℝ (fun p : ℝ × ℝ => theta Δ p.1 p.2) (x, y) := by
  unfold theta; fun_prop (disch := exact (cos_add_cos_sub_pos hΔ x y).ne')

/-- `Θ_Δ(·, y)` is analytic in the first variable (needed for the partial derivative `∂₁Θ`). -/
theorem analyticAt_theta_left  :
    AnalyticAt ℝ (fun s : ℝ => theta Δ s y) x := by
  unfold theta; fun_prop (disch := exact (cos_add_cos_sub_pos hΔ x y).ne')

/-- `Θ_Δ(x, ·)` is analytic in the second variable (needed for the partial derivative `∂₂Θ`). -/
theorem analyticAt_theta_right  :
    AnalyticAt ℝ (fun t : ℝ => theta Δ x t) y := by
  unfold theta; fun_prop (disch := exact (cos_add_cos_sub_pos hΔ x y).ne')
end

/-! ### Symmetries and period shifts -/

section
variable (Δ x y : ℝ)
/-- Antisymmetry under point reflection: `Θ(-x,-y) = -Θ(x,y)`. -/
theorem theta_neg_neg  : theta Δ (-x) (-y) = -theta Δ x y := by
  have := Real.arctan_neg ((Real.sin x - Real.sin y) / (Real.cos x + Real.cos y - 2 * Δ))
  simp only [theta, Real.sin_neg, Real.cos_neg]; ring_nf at this ⊢; linarith

/-- Antisymmetry under swapping the variables: `Θ(y,x) = -Θ(x,y)`. -/
theorem theta_swap  : theta Δ y x = -theta Δ x y := by
  have := Real.arctan_neg ((Real.sin x - Real.sin y) / (Real.cos x + Real.cos y - 2 * Δ))
  simp only [theta, add_comm (Real.cos y)]; ring_nf at this ⊢; linarith

/-- The equivalent form `Θ(x,-y) = -Θ(-x,y)` of the antisymmetry. -/
theorem theta_neg_right  : theta Δ x (-y) = -theta Δ (-x) y := by
  simpa using theta_neg_neg Δ (-x) y
end

/-- `Θ` vanishes on the diagonal: `Θ(x,x) = 0`. -/
theorem theta_self (Δ x : ℝ) : theta Δ x x = 0 := by
  simp [theta]

/-- `Θ(x + 2π, y) - Θ(x, y) = -2π`. -/
theorem theta_add_two_pi_left (Δ x y : ℝ) :
    theta Δ (x + 2 * Real.pi) y = theta Δ x y - 2 * Real.pi := by
  simp only [theta, Real.sin_add_two_pi, Real.cos_add_two_pi]
  ring

/-! ### Derivative consequences -/

/-- `∂₂Θ(x,-y) = ∂₂Θ(-x,y)`, a consequence of `Θ(x,-y) = -Θ(-x,y)`. -/
theorem deriv_theta_right_neg (Δ x y : ℝ) :
    deriv (fun t => theta Δ x t) (-y) = deriv (fun t => theta Δ (-x) t) y := by
  simpa [theta_neg_right] using (deriv_comp_neg (fun t => theta Δ x t) y).symm

/-- On the diagonal `(∂₁Θ + ∂₂Θ)(x,x) = 0`. -/
theorem deriv_theta_diag {Δ : ℝ} (hΔ : Δ < -1) (x : ℝ) :
    deriv (fun s => theta Δ s x) x + deriv (fun t => theta Δ x t) x = 0 := by
  have hF := (analyticAt_theta_xy hΔ x x).differentiableAt.hasFDerivAt
  rw [show deriv (fun s => theta Δ s x) x = _ from (hF.comp_hasDerivAt (f := fun s : ℝ => ((s, x) : ℝ × ℝ)) x ((hasDerivAt_id x).prodMk (hasDerivAt_const x x))).deriv, show deriv (fun t => theta Δ x t) x = _ from (hF.comp_hasDerivAt (f := fun t : ℝ => ((x, t) : ℝ × ℝ)) x ((hasDerivAt_const x x).prodMk (hasDerivAt_id x))).deriv, ← map_add]
  simpa using (hF.comp_hasDerivAt (f := fun s : ℝ => ((s, s) : ℝ × ℝ)) x ((hasDerivAt_id x).prodMk (hasDerivAt_id x))).unique ((hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq (by simp [theta_self, Function.comp_def]))

/-! ### The limit `Δ → -∞` -/

/-! ### Analyticity in `1/Δ` at `Δ = -∞` -/

/-- `Θ` as a function of `ε = 1/Δ`:
`Θ^{inv}(ε, x, y) = y - x + 2 arctan (ε (sin x - sin y) / (ε (cos x + cos y) - 2))`.
For `Δ < -1` one has `Θ_Δ = Θ^{inv}(1/Δ, ·, ·)` (`theta_eq_thetaInv`), and `ε = 0`
corresponds to `Δ = -∞`, where `Θ_{-∞}(x,y) = y - x` (`thetaInv_zero`). -/
def thetaInv (ε x y : ℝ) : ℝ :=
  y - x + 2 * Real.arctan
    (ε * (Real.sin x - Real.sin y) / (ε * (Real.cos x + Real.cos y) - 2))

theorem thetaInv_zero (x y : ℝ) : thetaInv 0 x y = y - x := by
  simp [thetaInv]

theorem theta_eq_thetaInv {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    theta Δ x y = thetaInv (1 / Δ) x y := by
  grind [Real.cos, cos_add_cos_sub_pos, theta, thetaInv]

/-- `(ε, x, y) ↦ Θ^{inv}(ε, x, y)` is real analytic for `|ε| < 1`; in particular at `ε = 0`
(`Δ = -∞`), which is the sense of footnote 8 of the source. -/
theorem analyticAt_thetaInv {ε : ℝ} (hε : |ε| < 1) (x y : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => thetaInv p.1 p.2.1 p.2.2) (ε, x, y) := by
  have := (abs_add_le (Real.cos x) (Real.cos y)).trans (add_le_add (Real.abs_cos_le_one x) (Real.abs_cos_le_one y))
  have h : |ε * (Real.cos x + Real.cos y)| < 2 := by rw [abs_mul]; nlinarith [abs_nonneg ε]
  unfold thetaInv; fun_prop (disch := exact (by linarith [abs_lt.1 h] : _ < (0:ℝ)).ne)

end PottsDiscontinuity.Bethe
