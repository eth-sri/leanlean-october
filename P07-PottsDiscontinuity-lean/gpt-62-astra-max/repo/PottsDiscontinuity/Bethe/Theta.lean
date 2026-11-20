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

@[expose] public section

open Complex Filter Topology

namespace PottsDiscontinuity.Bethe

/-! ### Generic helper lemmas -/

/-- `exp (2 i arctan t) = (1 + i t) / (1 - i t)`. -/
theorem exp_two_arctan_mul_I (t : ℝ) :
    Complex.exp (↑(2 * Real.arctan t) * I) = (1 + t * I) / (1 - t * I) := by
  have hs : 0 < 1 + t ^ 2 := by positivity
  have hc : Real.cos (Real.arctan t) ^ 2 = 1 / (1 + t ^ 2) := by
    simp [Real.cos_arctan, div_pow, Real.sq_sqrt hs.le]
  have h2 : Real.cos (Real.arctan t) * Real.sin (Real.arctan t) = t / (1 + t ^ 2) := by
    grind [Real.cos_arctan, Real.sin_arctan, Real.sq_sqrt hs.le]
  have hcos : Real.cos (2 * Real.arctan t) = (1 - t ^ 2) / (1 + t ^ 2) := by
    rw [Real.cos_two_mul, hc]; field_simp; ring
  have hsin : Real.sin (2 * Real.arctan t) = 2 * t / (1 + t ^ 2) := by
    grind [Real.sin_two_mul]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hcos, hsin]
  push_cast
  grind [Complex.I_sq]

section
variable (x : ℝ)

/-- `exp (i x) = cos x + i sin x` for real `x`, with the factor `I` on the left. -/
theorem exp_I_mul_ofReal :
    Complex.exp (I * x) = (Real.cos x) + (Real.sin x) * I := by
  rw [mul_comm, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

/-- `exp (-(i x)) = cos x - i sin x` for real `x`. -/
theorem exp_neg_I_mul_ofReal :
    Complex.exp (-(I * x)) = (Real.cos x) - (Real.sin x) * I := by
  have := exp_I_mul_ofReal (-x)
  rw [show I * (-x : ℝ) = -(I * x) by push_cast; ring] at this
  rw [this]; simp [Real.cos_neg, Real.sin_neg]; ring

end

/-- Uniqueness of continuous lifts: two continuous real functions on a preconnected space with
the same `x ↦ exp (i x)` which agree at one point are equal. -/
theorem eq_of_exp_eq {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] {f g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ p, Complex.exp ((f p) * I) = Complex.exp ((g p) * I)) {p₀ : X}
    (h0 : f p₀ = g p₀) : f = g := by
  have key : ∀ p, ((f p - g p) / (2 * Real.pi)) ∈ Set.range ((↑) : ℤ → ℝ) := by
    intro p
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (h p)
    refine ⟨n, ?_⟩
    have h1 : ((f p : ℂ) - g p) = n * (2 * Real.pi) := mul_right_cancel₀ Complex.I_ne_zero (by linear_combination hn)
    have h3 : f p - g p = n * (2 * Real.pi) := by exact_mod_cast h1
    simp_all
  have hc : Continuous (fun p => (f p - g p) / (2 * Real.pi)) :=
    (hf.sub hg).div_const _
  funext p
  have := (isPreconnected_univ (α := X)).constant_of_mapsTo Int.isClosedEmbedding_coe_real.isEmbedding.isInducing.isDiscrete_range hc.continuousOn
    (fun p _ => key p) (Set.mem_univ p) (Set.mem_univ p₀)
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  grind

/-- `Real.arctan` is real analytic everywhere. -/
theorem analyticAt_real_arctan (t : ℝ) : AnalyticAt ℝ Real.arctan t := by
  have h1 : AnalyticAt ℂ Complex.arctan t := by
    unfold Complex.arctan
    have hden : (1 - t * I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
    have hslit : ((1 + t * I) / (1 - t * I)) ∈ Complex.slitPlane := by
      have : ((1 + t * I) / (1 - t * I)) =
          ((1 - t^2) / (1 + t^2) : ℝ) + ((2 * t) / (1 + t^2) : ℝ) * I := by
        push_cast
        grind [Complex.I_sq]
      by_cases ht : t = 0
      · simp_all
      · right
        have hv : ((2 * t) / (1 + t^2)) ≠ 0 := by positivity
        rw [this]
        generalize (2 * t) / (1 + t^2) = v at *
        generalize (1 - t^2) / (1 + t^2) = u at *
        simpa using hv
    fun_prop
  have h2 : Real.arctan = fun x : ℝ => (Complex.arctan x).re := by
    funext x; rw [← Complex.ofReal_arctan, Complex.ofReal_re]
  rw [h2]
  exact h1.re_ofReal

/-! ### Definition of `Θ` -/

/-- The Bethe phase `Θ_Δ(x, y)` of arXiv:1611.09877v2, (1.8), for `Δ < -1` (the formula is
total in `Δ`, but it is the Bethe phase only for `Δ < -1`; see `theta_isBethePhase`):
`Θ(Δ, x, y) = y - x + 2 arctan ((sin x - sin y) / (cos x + cos y - 2Δ))`. -/
noncomputable def theta (Δ x y : ℝ) : ℝ :=
  y - x + 2 * Real.arctan ((Real.sin x - Real.sin y) / (Real.cos x + Real.cos y - 2 * Δ))

/-- The right-hand side of (1.8):
`e^{i(x-y)} (e^{-ix} + e^{iy} - 2Δ) / (e^{ix} + e^{-iy} - 2Δ)`. -/
noncomputable def thetaRhs (Δ x y : ℝ) : ℂ :=
  Complex.exp (I * (x - y)) *
    ((Complex.exp (-(I * x)) + Complex.exp (I * y) - 2 * Δ) /
      (Complex.exp (I * x) + Complex.exp (-(I * y)) - 2 * Δ))

section
variable {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ)
include hΔ

/-- The denominator `cos x + cos y - 2Δ = Re (e^{ix} + e^{-iy} - 2Δ)` is positive for `Δ < -1`. -/
theorem cos_add_cos_sub_pos :
    0 < Real.cos x + Real.cos y - 2 * Δ := by
  have := Real.neg_one_le_cos x
  have := Real.neg_one_le_cos y
  linarith

/-- Continuity of `Θ_Δ` on `ℝ²` for fixed `Δ < -1`. -/
theorem continuous_theta :
    Continuous (fun p : ℝ × ℝ => theta Δ p.1 p.2) := by
  refine (continuous_snd.sub continuous_fst).add (continuous_const.mul
    (Real.continuous_arctan.comp ?_))
  refine ((Real.continuous_sin.comp continuous_fst).sub (Real.continuous_sin.comp
    continuous_snd)).div (by fun_prop) ?_
  intro p
  exact (cos_add_cos_sub_pos hΔ p.1 p.2).ne'

/-- The exponential identity (1.8): `exp (-i Θ(x,y)) = e^{i(x-y)} (e^{-ix} + e^{iy} - 2Δ) /
(e^{ix} + e^{-iy} - 2Δ)` for `Δ < -1`. -/
theorem exp_neg_I_theta :
    Complex.exp (-(I * (theta Δ x y))) = thetaRhs Δ x y := by
  set a : ℝ := Real.cos x + Real.cos y - 2 * Δ with ha
  set b : ℝ := Real.sin x - Real.sin y with hb
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast (cos_add_cos_sub_pos hΔ x y).ne'
  have hD1 : Complex.exp (I * x) + Complex.exp (-(I * y)) - 2 * Δ =
      a + b * I := by
    rw [exp_I_mul_ofReal, exp_neg_I_mul_ofReal, ha, hb]; push_cast; ring
  have hD2 : Complex.exp (-(I * x)) + Complex.exp (I * y) - 2 * Δ =
      a - b * I := by
    rw [exp_neg_I_mul_ofReal, exp_I_mul_ofReal, ha, hb]; push_cast; ring
  have hth : theta Δ x y = y - x + 2 * Real.arctan (b / a) := rfl
  have hinv : Complex.exp (-(I * (theta Δ x y))) =
      Complex.exp (I * (x - y)) *
        (Complex.exp (-(↑(2 * Real.arctan (b / a)) * I))) := by
    rw [← Complex.exp_add, hth]
    congr 1
    push_cast
    ring
  rw [hinv, thetaRhs, hD1, hD2, Complex.exp_neg, exp_two_arctan_mul_I]
  congr 1
  push_cast
  field_simp

end

/-! ### Analyticity -/

section
variable {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ)
include hΔ

/-- Joint real analyticity of `(Δ, x, y) ↦ Θ_Δ(x, y)` at every point with `Δ < -1`. -/
theorem analyticAt_theta :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => theta p.1 p.2.1 p.2.2) (Δ, x, y) := by
  have hX : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.1) (Δ, x, y) :=
    analyticAt_fst.comp analyticAt_snd
  have hY : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.2) (Δ, x, y) :=
    analyticAt_snd.comp analyticAt_snd
  have hq :=
    ((Real.analyticAt_sin.comp hX).sub (Real.analyticAt_sin.comp hY)).div (((Real.analyticAt_cos.comp hX).add (Real.analyticAt_cos.comp hY)).sub (analyticAt_const.mul analyticAt_fst)) (cos_add_cos_sub_pos hΔ x y).ne'
  exact (hY.sub hX).add (analyticAt_const.mul ((analyticAt_real_arctan _).comp hq))

/-- For fixed `Δ < -1`, `(x, y) ↦ Θ_Δ(x, y)` is real analytic. -/
theorem analyticAt_theta_xy :
    AnalyticAt ℝ (fun p : ℝ × ℝ => theta Δ p.1 p.2) (x, y) := AnalyticAt.comp (analyticAt_theta hΔ x y) (AnalyticAt.prod analyticAt_const (AnalyticAt.prod analyticAt_fst analyticAt_snd))

/-- `Θ_Δ(·, y)` is analytic in the first variable (needed for the partial derivative `∂₁Θ`). -/
theorem analyticAt_theta_left :
    AnalyticAt ℝ (fun s : ℝ => theta Δ s y) x := by
  exact AnalyticAt.comp
    (f := fun s : ℝ => (s, y)) (analyticAt_theta_xy hΔ x y) (analyticAt_id.prod analyticAt_const)

/-- `Θ_Δ(x, ·)` is analytic in the second variable (needed for the partial derivative `∂₂Θ`). -/
theorem analyticAt_theta_right :
    AnalyticAt ℝ (fun t : ℝ => theta Δ x t) y := AnalyticAt.comp (analyticAt_theta_xy hΔ x y) (AnalyticAt.prod analyticAt_const analyticAt_id)

end

/-! ### Symmetries and period shifts -/

section
variable (Δ x y : ℝ)

/-- Antisymmetry under point reflection: `Θ(-x,-y) = -Θ(x,y)`. -/
theorem theta_neg_neg : theta Δ (-x) (-y) = -theta Δ x y := by
  simp only [theta, Real.sin_neg, Real.cos_neg]
  have : (-Real.sin x - -Real.sin y) = -(Real.sin x - Real.sin y) := by ring
  rw [this, neg_div, Real.arctan_neg]
  ring

/-- Antisymmetry under swapping the variables: `Θ(y,x) = -Θ(x,y)`. -/
theorem theta_swap : theta Δ y x = -theta Δ x y := by
  simp only [theta]
  have h1 : Real.sin y - Real.sin x = -(Real.sin x - Real.sin y) := by ring
  have h2 : Real.cos y + Real.cos x - 2 * Δ = Real.cos x + Real.cos y - 2 * Δ := by ring
  rw [h1, h2, neg_div, Real.arctan_neg]
  ring

/-- The equivalent form `Θ(x,-y) = -Θ(-x,y)` of the antisymmetry. -/
theorem theta_neg_right : theta Δ x (-y) = -theta Δ (-x) y := by
  have := theta_neg_neg Δ (-x) y
  simp_all

/-- `Θ` vanishes on the diagonal: `Θ(x,x) = 0`. -/
theorem theta_self (Δ x : ℝ) : theta Δ x x = 0 := by
  simp [theta]

/-- `Θ(x + 2π, y) - Θ(x, y) = -2π`. -/
theorem theta_add_two_pi_left :
    theta Δ (x + 2 * Real.pi) y = theta Δ x y - 2 * Real.pi := by
  grind [theta, Real.sin_add_two_pi, Real.cos_add_two_pi]

end

/-! ### Derivative consequences -/

/-- `∂₂Θ(x,-y) = ∂₂Θ(-x,y)`, a consequence of `Θ(x,-y) = -Θ(-x,y)`. -/
theorem deriv_theta_right_neg (Δ x y : ℝ) :
    deriv (fun t => theta Δ x t) (-y) = deriv (fun t => theta Δ (-x) t) y := by
  have h :=
    funext fun t => theta_neg_right Δ x t
  have h1 :=
    deriv_comp_neg (fun t => theta Δ x t) y
  simp_all

/-- On the diagonal `(∂₁Θ + ∂₂Θ)(x,x) = 0`. -/
theorem deriv_theta_diag {Δ : ℝ} (hΔ : Δ < -1) (x : ℝ) :
    deriv (fun s => theta Δ s x) x + deriv (fun t => theta Δ x t) x = 0 := by
  have hF :=
    (analyticAt_theta_xy hΔ x x).differentiableAt
  have h6 : HasDerivAt (fun s : ℝ => theta Δ s s) 0 x := by
    rw [(funext fun s => theta_self Δ s)]; exact hasDerivAt_const x 0
  have h7 := (HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => (s, s)) x hF.hasFDerivAt ((hasDerivAt_id x).prodMk (hasDerivAt_id x))).unique h6
  have hF1 := hF.hasFDerivAt
  have h8 : deriv (fun s => theta Δ s x) x =
      fderiv ℝ (fun p : ℝ × ℝ => theta Δ p.1 p.2) (x, x) (1, 0) := (HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => (s, x)) x hF1 ((hasDerivAt_id x).prodMk (hasDerivAt_const x x))).deriv
  have h9 : deriv (fun t => theta Δ x t) x =
      fderiv ℝ (fun p : ℝ × ℝ => theta Δ p.1 p.2) (x, x) (0, 1) := HasDerivAt.deriv (HasFDerivAt.comp_hasDerivAt x hF1 (HasDerivAt.prodMk (hasDerivAt_const x x) (hasDerivAt_id x)))
  rw [h8, h9, ← map_add]
  simp_all

/-! ### The limit `Δ → -∞` -/

/-! ### Analyticity in `1/Δ` at `Δ = -∞` -/

/-- `Θ` as a function of `ε = 1/Δ`:
`Θ^{inv}(ε, x, y) = y - x + 2 arctan (ε (sin x - sin y) / (ε (cos x + cos y) - 2))`.
For `Δ < -1` one has `Θ_Δ = Θ^{inv}(1/Δ, ·, ·)` (`theta_eq_thetaInv`), and `ε = 0`
corresponds to `Δ = -∞`, where `Θ_{-∞}(x,y) = y - x` (`thetaInv_zero`). -/
noncomputable def thetaInv (ε x y : ℝ) : ℝ :=
  y - x + 2 * Real.arctan
    (ε * (Real.sin x - Real.sin y) / (ε * (Real.cos x + Real.cos y) - 2))

variable {ε : ℝ} (hε : |ε| < 1) {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ)

theorem thetaInv_zero : thetaInv 0 x y = y - x := by
  simp [thetaInv]

include hΔ in
theorem theta_eq_thetaInv :
    theta Δ x y = thetaInv (1 / Δ) x y := by
  grind [theta, thetaInv]

include hε in
/-- `(ε, x, y) ↦ Θ^{inv}(ε, x, y)` is real analytic for `|ε| < 1`; in particular at `ε = 0`
(`Δ = -∞`), which is the sense of footnote 8 of the source. -/
theorem analyticAt_thetaInv :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => thetaInv p.1 p.2.1 p.2.2) (ε, x, y) := by
  have hE : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.1) (ε, x, y) := analyticAt_fst
  have hX : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.1) (ε, x, y) :=
    analyticAt_fst.comp analyticAt_snd
  have hY : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.2) (ε, x, y) :=
    analyticAt_snd.comp analyticAt_snd
  have hden0 : ε * (Real.cos x + Real.cos y) - 2 ≠ 0 := by
    have hc : |Real.cos x + Real.cos y| ≤ 2 := by
      grind [Real.abs_cos_le_one]
    have h3 : |ε * (Real.cos x + Real.cos y)| < 2 := by
      rw [abs_mul]
      nlinarith [abs_nonneg ε, abs_nonneg (Real.cos x + Real.cos y)]
    grind
  have hq :=
    (hE.mul ((Real.analyticAt_sin.comp hX).sub (Real.analyticAt_sin.comp hY))).div ((hE.mul ((Real.analyticAt_cos.comp hX).add (Real.analyticAt_cos.comp hY))).sub analyticAt_const) hden0
  exact (hY.sub hX).add (analyticAt_const.mul ((analyticAt_real_arctan _).comp hq))

end PottsDiscontinuity.Bethe
