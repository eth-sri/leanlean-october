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
    Complex.exp (((2 * Real.arctan t : ℝ) : ℂ) * I) = (1 + (t : ℂ) * I) / (1 - (t : ℂ) * I) := by
  have hs : (0:ℝ) < 1 + t ^ 2 := by positivity
  have hc : Real.cos (Real.arctan t) ^ 2 = 1 / (1 + t ^ 2) := by
    rw [Real.cos_arctan, div_pow, Real.sq_sqrt hs.le]; simp
  have h2 : Real.cos (Real.arctan t) * Real.sin (Real.arctan t) = t / (1 + t ^ 2) := by
    grind only [Real.cos_arctan, Real.sin_arctan]
  have hcos : Real.cos (2 * Real.arctan t) = (1 - t ^ 2) / (1 + t ^ 2) := by
    rw [Real.cos_two_mul, hc]; field_simp; ring
  have hsin : Real.sin (2 * Real.arctan t) = 2 * t / (1 + t ^ 2) := by
    rw [Real.sin_two_mul]; linear_combination 2 * h2
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hcos, hsin]
  have h1 : (1 - (t : ℂ) * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have h3 : (1 + (t : ℂ) * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have h4 : (1 + (t:ℂ)^2) ≠ 0 := by exact_mod_cast hs.ne'
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq]
  ring

/-- The half-angle quotient is homogeneous in the real and imaginary parts. -/
theorem exp_two_arctan_div_mul_I {a b : ℝ} (ha : a ≠ 0) :
    Complex.exp (((2 * Real.arctan (b / a) : ℝ) : ℂ) * I) =
      ((a : ℂ) + (b : ℂ) * I) / ((a : ℂ) - (b : ℂ) * I) := by
  rw [exp_two_arctan_mul_I]
  push_cast
  have h : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  field_simp

/-- `exp (i x) = cos x + i sin x` for real `x`, with the factor `I` on the left. -/
theorem exp_I_mul_ofReal (x : ℝ) :
    Complex.exp (I * (x : ℂ)) = (Real.cos x : ℂ) + (Real.sin x : ℂ) * I := by
  rw [mul_comm, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

/-- `exp (-(i x)) = cos x - i sin x` for real `x`. -/
theorem exp_neg_I_mul_ofReal (x : ℝ) :
    Complex.exp (-(I * (x : ℂ))) = (Real.cos x : ℂ) - (Real.sin x : ℂ) * I := by
  have := exp_I_mul_ofReal (-x)
  aesop

/-- Uniqueness of continuous lifts: two continuous real functions on a preconnected space with
the same `x ↦ exp (i x)` which agree at one point are equal. -/
theorem eq_of_exp_eq {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] {f g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ p, Complex.exp ((f p : ℂ) * I) = Complex.exp ((g p : ℂ) * I)) (p₀ : X)
    (h0 : f p₀ = g p₀) : f = g := by
  have key : ∀ p, ((f p - g p) / (2 * Real.pi)) ∈ Set.range ((↑) : ℤ → ℝ) := by
    intro p
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (h p)
    refine ⟨n, ?_⟩
    have h1 : ((f p : ℂ) - g p) = (n : ℂ) * (2 * Real.pi) := by
      have h2 : ((f p : ℂ) - g p) * I = (n : ℂ) * (2 * Real.pi) * I := by
        linear_combination hn
      exact mul_right_cancel₀ Complex.I_ne_zero h2
    have h3 : f p - g p = (n : ℝ) * (2 * Real.pi) := by exact_mod_cast h1
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    field_simp
    linarith
  have hd : IsDiscrete (Set.range ((↑) : ℤ → ℝ)) :=
    Int.isClosedEmbedding_coe_real.isEmbedding.isInducing.isDiscrete_range
  have hc : Continuous (fun p => (f p - g p) / (2 * Real.pi)) :=
    (hf.sub hg).div_const _
  funext p
  have := (isPreconnected_univ (α := X)).constant_of_mapsTo hd hc.continuousOn
    (fun p _ => key p) (Set.mem_univ p) (Set.mem_univ p₀)
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have h4 : (f p - g p) / (2 * Real.pi) = 0 := by rw [this, h0]; simp
  rw [div_eq_zero_iff] at h4
  rcases h4 with h4 | h4
  · linarith
  trivial

/-- `Real.arctan` is real analytic everywhere. -/
theorem analyticAt_real_arctan (t : ℝ) : AnalyticAt ℝ Real.arctan t := by
  have hc := (Real.cos_arctan_pos t).ne'
  let d := 1 / Real.cos (Real.arctan t) ^ 2
  have hd : d ≠ 0 := by positivity
  rw [← Real.coe_tanPartialHomeomorph_symm]
  apply Real.tanPartialHomeomorph.analyticAt_symm (i := .unitsEquivAut ℝ (.mk0 d hd)) (by trivial)
  · rw [Real.coe_tanPartialHomeomorph, Real.coe_tanPartialHomeomorph_symm,
      show Real.tan = Real.sin / Real.cos from funext Real.tan_eq_sin_div_cos]
    exact Real.analyticAt_sin.div Real.analyticAt_cos hc
  · rw [Real.coe_tanPartialHomeomorph, Real.coe_tanPartialHomeomorph_symm,
      (Real.hasDerivAt_tan hc).hasFDerivAt.fderiv]
    ext x
    simp [d]

/-! ### Definition of `Θ` -/

/-- The Bethe phase `Θ_Δ(x, y)` of arXiv:1611.09877v2, (1.8), for `Δ < -1` (the formula is
total in `Δ`, but it is the Bethe phase only for `Δ < -1`; see `theta_isBethePhase`):
`Θ(Δ, x, y) = y - x + 2 arctan ((sin x - sin y) / (cos x + cos y - 2Δ))`. -/
noncomputable def theta (Δ x y : ℝ) : ℝ :=
  y - x + 2 * Real.arctan ((Real.sin x - Real.sin y) / (Real.cos x + Real.cos y - 2 * Δ))

/-- The right-hand side of (1.8):
`e^{i(x-y)} (e^{-ix} + e^{iy} - 2Δ) / (e^{ix} + e^{-iy} - 2Δ)`. -/
noncomputable def thetaRhs (Δ x y : ℝ) : ℂ :=
  Complex.exp (I * ((x : ℂ) - y)) *
    ((Complex.exp (-(I * x)) + Complex.exp (I * y) - 2 * (Δ : ℂ)) /
      (Complex.exp (I * x) + Complex.exp (-(I * y)) - 2 * (Δ : ℂ)))

/-- The denominator `cos x + cos y - 2Δ = Re (e^{ix} + e^{-iy} - 2Δ)` is positive for `Δ < -1`. -/
theorem cos_add_cos_sub_pos {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    0 < Real.cos x + Real.cos y - 2 * Δ := by
  have := Real.neg_one_le_cos x
  have := Real.neg_one_le_cos y
  linarith

/-- The exponential identity (1.8): `exp (-i Θ(x,y)) = e^{i(x-y)} (e^{-ix} + e^{iy} - 2Δ) /
(e^{ix} + e^{-iy} - 2Δ)` for `Δ < -1`. -/
theorem exp_neg_I_theta {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    Complex.exp (-(I * (theta Δ x y : ℂ))) = thetaRhs Δ x y := by
  let a := Real.cos x + Real.cos y - 2 * Δ
  let b := Real.sin x - Real.sin y
  have he : -(I * (theta Δ x y : ℂ)) = I * ((x : ℂ) - y) - (((2 * Real.arctan (b / a) : ℝ) : ℂ) * I) := by
    simp [theta, a, b]; ring
  rw [he, Complex.exp_sub, exp_two_arctan_div_mul_I (b := b) (cos_add_cos_sub_pos hΔ x y).ne', div_div_eq_mul_div]
  unfold thetaRhs
  rw [exp_I_mul_ofReal x, exp_neg_I_mul_ofReal x, exp_I_mul_ofReal y, exp_neg_I_mul_ofReal y]
  dsimp [a, b]
  push_cast
  ring

/-! ### Symmetries and period shifts -/

/-- Antisymmetry under point reflection: `Θ(-x,-y) = -Θ(x,y)`. -/
theorem theta_neg_neg (Δ x y : ℝ) : theta Δ (-x) (-y) = -theta Δ x y := by
  simp only [theta, Real.sin_neg, Real.cos_neg]
  have : (-Real.sin x - -Real.sin y) = -(Real.sin x - Real.sin y) := by ring
  rw [this, neg_div, Real.arctan_neg]
  ring

/-- Antisymmetry under swapping the variables: `Θ(y,x) = -Θ(x,y)`. -/
theorem theta_swap (Δ x y : ℝ) : theta Δ y x = -theta Δ x y := by
  simp only [theta]
  have h1 : Real.sin y - Real.sin x = -(Real.sin x - Real.sin y) := by ring
  have h2 : Real.cos y + Real.cos x - 2 * Δ = Real.cos x + Real.cos y - 2 * Δ := by ring
  rw [h1, h2, neg_div, Real.arctan_neg]
  ring

/-- `Θ` vanishes on the diagonal: `Θ(x,x) = 0`. -/
theorem theta_self (Δ x : ℝ) : theta Δ x x = 0 := by
  simp [theta]

/-- `Θ(x + 2π, y) - Θ(x, y) = -2π`. -/
theorem theta_add_two_pi_left (Δ x y : ℝ) :
    theta Δ (x + 2 * Real.pi) y = theta Δ x y - 2 * Real.pi := by
  simp only [theta, Real.sin_add_two_pi, Real.cos_add_two_pi]
  ring

/-- `Θ` as a function of `ε = 1/Δ`:
`Θ^{inv}(ε, x, y) = y - x + 2 arctan (ε (sin x - sin y) / (ε (cos x + cos y) - 2))`.
For `Δ < -1` one has `Θ_Δ = Θ^{inv}(1/Δ, ·, ·)` (`theta_eq_thetaInv`), and `ε = 0`
corresponds to `Δ = -∞`, where `Θ_{-∞}(x,y) = y - x` (`thetaInv_zero`). -/
noncomputable def thetaInv (ε x y : ℝ) : ℝ :=
  y - x + 2 * Real.arctan
    (ε * (Real.sin x - Real.sin y) / (ε * (Real.cos x + Real.cos y) - 2))

theorem thetaInv_zero (x y : ℝ) : thetaInv 0 x y = y - x := by
  simp [thetaInv]

theorem theta_eq_thetaInv {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    theta Δ x y = thetaInv (1 / Δ) x y := by
  grind only [theta, thetaInv]

/-- `(ε, x, y) ↦ Θ^{inv}(ε, x, y)` is real analytic for `|ε| < 1`; in particular at `ε = 0`
(`Δ = -∞`), which is the sense of footnote 8 of the source. -/
theorem analyticAt_thetaInv {ε : ℝ} (hε : |ε| < 1) (x y : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => thetaInv p.1 p.2.1 p.2.2) (ε, x, y) := by
  have hX : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.1) (ε, x, y) := analyticAt_fst.comp analyticAt_snd
  have hY : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.2) (ε, x, y) := analyticAt_snd.comp analyticAt_snd
  have hden0 : ε * (Real.cos x + Real.cos y) - 2 ≠ 0 := by
    have hc := (abs_add_le (Real.cos x) (Real.cos y)).trans
      (add_le_add (Real.abs_cos_le_one _) (Real.abs_cos_le_one _))
    have h : |ε * (Real.cos x + Real.cos y)| < 2 := by
      rw [abs_mul]
      nlinarith [abs_nonneg ε]
    grind
  have hq := (analyticAt_fst.mul ((Real.analyticAt_sin.comp hX).sub (Real.analyticAt_sin.comp hY))).div
    ((analyticAt_fst.mul ((Real.analyticAt_cos.comp hX).add (Real.analyticAt_cos.comp hY))).sub analyticAt_const) hden0
  exact (hY.sub hX).add (analyticAt_const.mul ((analyticAt_real_arctan _).comp hq))

theorem abs_inverse_parameter_lt_one {Δ : ℝ} (hΔ : Δ < -1) : |1 / Δ| < 1 := by
  rw [abs_div, abs_one]
  have habs : 1 < |Δ| := by grind
  exact (div_lt_one (by linarith : 0 < |Δ|)).2 habs

/-- Joint real analyticity follows by substituting `ε = 1/Δ`. -/
theorem analyticAt_theta {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => theta p.1 p.2.1 p.2.2) (Δ, x, y) := by
  have hf : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => ((1 / p.1, p.2) : ℝ × ℝ × ℝ)) (Δ, x, y) :=
    (analyticAt_const.div analyticAt_fst (by linarith : Δ ≠ 0)).prod analyticAt_snd
  refine (AnalyticAt.comp (x := (Δ, x, y)) (f := fun p : ℝ × ℝ × ℝ => (1 / p.1, p.2))
    (analyticAt_thetaInv (abs_inverse_parameter_lt_one hΔ) x y) hf).congr ?_
  filter_upwards [continuous_fst.continuousAt.eventually_lt continuousAt_const hΔ] with p hp
  exact (theta_eq_thetaInv hp p.2.1 p.2.2).symm

/-- For fixed `Δ < -1`, `(x, y) ↦ Θ_Δ(x, y)` is real analytic. -/
theorem analyticAt_theta_xy {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ => theta Δ p.1 p.2) (x, y) := by
  have h1 : AnalyticAt ℝ (fun p : ℝ × ℝ => ((Δ, p.1, p.2) : ℝ × ℝ × ℝ)) (x, y) :=
    (analyticAt_const (v := Δ)).prod (analyticAt_fst.prod analyticAt_snd)
  exact AnalyticAt.comp (g := fun p : ℝ × ℝ × ℝ => theta p.1 p.2.1 p.2.2)
    (f := fun p : ℝ × ℝ => ((Δ, p.1, p.2) : ℝ × ℝ × ℝ)) (analyticAt_theta hΔ x y) h1

/-- `Θ_Δ(·, y)` is analytic in the first variable (needed for the partial derivative `∂₁Θ`). -/
theorem analyticAt_theta_left {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => theta Δ s y) x := by
  have h1 : AnalyticAt ℝ (fun s : ℝ => ((s, y) : ℝ × ℝ)) x :=
    analyticAt_id.prod analyticAt_const
  exact AnalyticAt.comp (g := fun p : ℝ × ℝ => theta Δ p.1 p.2)
    (f := fun s : ℝ => ((s, y) : ℝ × ℝ)) (analyticAt_theta_xy hΔ x y) h1

/-- `Θ_Δ(x, ·)` is analytic in the second variable (needed for the partial derivative `∂₂Θ`). -/
theorem analyticAt_theta_right {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    AnalyticAt ℝ (fun t : ℝ => theta Δ x t) y := by
  have h1 : AnalyticAt ℝ (fun t : ℝ => ((x, t) : ℝ × ℝ)) y :=
    analyticAt_const.prod analyticAt_id
  exact AnalyticAt.comp (g := fun p : ℝ × ℝ => theta Δ p.1 p.2)
    (f := fun t : ℝ => ((x, t) : ℝ × ℝ)) (analyticAt_theta_xy hΔ x y) h1
/-- Continuity of `Θ_Δ` on `ℝ²` for fixed `Δ < -1`. -/
theorem continuous_theta {Δ : ℝ} (hΔ : Δ < -1) :
    Continuous (fun p : ℝ × ℝ => theta Δ p.1 p.2) :=
  continuous_iff_continuousAt.mpr fun p => (analyticAt_theta_xy hΔ p.1 p.2).continuousAt

end PottsDiscontinuity.Bethe
