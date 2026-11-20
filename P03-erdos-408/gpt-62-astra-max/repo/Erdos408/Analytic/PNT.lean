module

public import Erdos408.Analytic.PrimeTwist
public import Erdos408.Hypotheses
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import PrimeNumberTheoremAnd.PerronFormula

/-!
# The prime number theorem in progressions with a power saving

AC0 of `blueprint/rectangle_input.md` §3:
`ψ(y, χ) = [χ = 1] y + O(k^C y^{1-c})` for every Dirichlet character `χ` of
modulus `k`, from a smoothed Perron formula shifted into the zero-free
half-plane `re s > 7/8`.

* The smoothed sum `∑_{m ≤ x} Λ(m) χ(m) (1 - m / x)` is the vertical integral on
  `re s = 2` of `-(L'/L)(s, χ) x^s / (s (s + 1))`; truncating at height `x²`
  costs `O(1)`. This is the zero-frequency case of the twisted Perron formula.
* Shift to `re s = 15/16` across the rectangle `[15/16, 2] × [-x², x²]`. No zero
  lies inside, so only the pole of the principal character at `s = 1`
  contributes, with residue `x / 2`.
* On the left edge, `L'/L ≪ log (k (|t| + 3))` away from `s = 1`, by
  `Erdos408.Analytic.Core`. Near `s = 1`, Borel–Carathéodory on discs centred at
  `2 + it` bounds `L'/L` for `χ ≠ 1`, and `L'/L + 1/(s - 1)` for the principal
  character through the entire function `(s - 1) L(s, χ₀)`, by `O(k)`.
* So the smoothed sum is `[χ = 1] x / 2 + O(k x^{15/16})`. Differencing the
  weighted sums `∑_{n ≤ z} Λ(n) χ(n) (z - n)` at `z = ⌊y⌋ + 1/2` and `z + h`,
  with `h ≈ y^{31/32}`, gives the theorem with `c = 1/64` and `C = O(1)`.
-/

@[expose] public section

namespace Erdos408

open Filter Classical

namespace PNT

/-! ### The smoothed Perron formula -/

section Perron

open Complex ArithmeticFunction DirichletCharacter

/-- The integrand `-(L'/L)(s, χ) x^s / (s (s + 1))` of the smoothed explicit
formula. -/
noncomputable def perronIntegrand {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ)
    (s : ℂ) : ℂ :=
  -(deriv (LFunction χ) s / LFunction χ s) * ((x : ℂ) ^ s / (s * (s + 1)))

open scoped LSeries.notation

/-- The ordinary integrand is the zero-frequency twisted integrand. -/
private lemma perron_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ) :
    perronIntegrand χ x = PrimeTwist.twistIntegrand χ 0 x := by
  ext s
  simp [perronIntegrand, PrimeTwist.twistIntegrand, Perron.f]

theorem verticalIntegral_perronIntegrand {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {x : ℝ} (hx : 1 < x) (hxN : ∀ m : ℕ, (m : ℝ) ≠ x) :
    VerticalIntegral (perronIntegrand χ x) 2 =
      2 * Real.pi * I * ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Λ m : ℂ) * χ m * (1 - m / x) := by
  rw [perron_zero]
  simpa [PrimeTwist.twistCoeff, mul_comm] using
    PrimeTwist.verticalIntegral_twistIntegrand χ 0 hx hxN

end Perron

/-! ### Bounds on the kernel and on the edges -/

section Edges

open Complex

/-- To the right of `1/16`, `‖s (s + 1)‖` is at least `(1 + |im s|)² / 64`. -/
lemma one_add_abs_im_sq_le_norm_mul {s : ℂ} (hs : 1 / 16 ≤ s.re) :
    (1 + |s.im|) ^ 2 ≤ 64 * ‖s * (s + 1)‖ := by
  have h₁ : |s.im| ≤ ‖s‖ := abs_im_le_norm s
  have h₂  := re_le_norm s
  have h₃ : |(s + 1).im| ≤ ‖s + 1‖ := abs_im_le_norm _
  have h₄ : (s + 1).re ≤ ‖s + 1‖ := re_le_norm _
  simp only [add_im, one_im, add_zero, add_re, one_re] at h₃ h₄
  have h₅ : 1 + |s.im| ≤ 32 * ‖s‖ := by linarith
  have h₆ : 1 + |s.im| ≤ 2 * ‖s + 1‖ := by linarith
  calc _ ≤ (32 * ‖s‖) * (2 * ‖s + 1‖) := by
        rw [sq]; exact mul_le_mul h₅ h₆ (by positivity) (by positivity)
    _ = _ := by rw [norm_mul]; ring

/-- To the right of `1/16`, `‖x^s / (s (s + 1))‖ ≤ 64 x^{re s} / (1 + |im s|)²`. -/
lemma norm_cpow_div_le {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 1 / 16 ≤ s.re) :
    ‖(x : ℂ) ^ s / (s * (s + 1))‖ ≤ 64 * x ^ s.re / (1 + |s.im|) ^ 2 := by
  have h := one_add_abs_im_sq_le_norm_mul hs
  have hpos : 0 < ‖s * (s + 1)‖ := by
    have : 0 < (1 + |s.im|) ^ 2 := by positivity
    linarith
  rw [norm_div, norm_cpow_eq_rpow_re_of_pos hx, div_le_div_iff₀ hpos (by positivity)]
  have := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hx.le s.re)
  linarith

/-- Off the real axis, `‖x^s / (s (s + 1))‖ ≤ x^{re s} / (im s)²`. -/
lemma norm_cpow_div_le_of_im_ne_zero {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s.im ≠ 0) :
    ‖(x : ℂ) ^ s / (s * (s + 1))‖ ≤ x ^ s.re / s.im ^ 2 := by
  have h₁ : |s.im| ≤ ‖s‖ := abs_im_le_norm s
  have h₃ : |(s + 1).im| ≤ ‖s + 1‖ := abs_im_le_norm _
  simp only [add_im, one_im, add_zero] at h₃
  have h : s.im ^ 2 ≤ ‖s * (s + 1)‖ := by
    rw [norm_mul, ← sq_abs, sq]
    exact mul_le_mul h₁ h₃ (abs_nonneg _) (norm_nonneg _)
  have hpos : 0 < s.im ^ 2 := by positivity
  rw [norm_div, norm_cpow_eq_rpow_re_of_pos hx]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) hpos h

/-- `1 + log (|t| + 3) ≤ 5 (1 + |t|)^{1/2}`. -/
lemma one_add_log_le_rpow (t : ℝ) :
    1 + Real.log (|t| + 3) ≤ 5 * (1 + |t|) ^ (1 / 2 : ℝ) := by
  have hu : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  have h₁ : Real.log (|t| + 3) ≤ Real.log 3 + Real.log (1 + |t|) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by positivity) (by linarith [abs_nonneg t])
  have h₂ : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have h₃ : Real.log (1 + |t|) ≤ (1 + |t|) ^ (1 / 2 : ℝ) / (1 / 2) :=
    Real.log_le_rpow_div (by linarith) (by norm_num)
  have h₄ : 1 ≤ (1 + |t|) ^ (1 / 2 : ℝ) := Real.one_le_rpow hu (by norm_num)
  linarith

/-- A vertical segment integral is at most `c ∫ (1 + |t|)^{-3/2} dt` when the integrand is
dominated by `c (1 + |t|)^{-3/2}`. -/
lemma norm_vIntegral_le {F : ℂ → ℂ} {σ T c : ℝ} (hT : 0 ≤ T)
    (hF : ∀ t : ℝ, ‖F (σ + t * I)‖ ≤ c * (1 + |t|) ^ (-(3 / 2) : ℝ)) :
    ‖VIntegral F σ (-T) T‖ ≤ c * ∫ t : ℝ, (1 + |t|) ^ (-(3 / 2) : ℝ) := by
  have hint : MeasureTheory.Integrable fun t : ℝ ↦ c * (1 + |t|) ^ (-(3 / 2) : ℝ) := by
    have h := integrable_one_add_norm (E := ℝ) (μ := MeasureTheory.volume) (r := 3 / 2)
      (by simp; norm_num)
    simpa [Real.norm_eq_abs] using h.const_mul c
  have hc : 0 ≤ c := by simpa using (norm_nonneg _).trans (hF 0)
  rw [VIntegral, norm_smul, norm_I, one_mul, ← MeasureTheory.integral_const_mul]
  calc _
      ≤ ∫ t in -T..T, c * (1 + |t|) ^ (-(3 / 2) : ℝ) :=
        intervalIntegral.norm_integral_le_of_norm_le (by linarith)
          (Filter.Eventually.of_forall fun t _ ↦ hF t) hint.intervalIntegrable
    _ ≤ _ := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact MeasureTheory.setIntegral_le_integral hint
          (Filter.Eventually.of_forall fun t ↦ by positivity)

end Edges

/-! ### Logarithmic derivatives near `s = 1` -/

section NearOne

open Complex DirichletCharacter Metric

open scoped LSeries.notation

/-- `log (k (|t| + 3)) ≤ 6 k (1 + |t|)^{1/2}`. -/
lemma log_mul_le_mul_rpow {k : ℝ} (hk : 1 ≤ k) (t : ℝ) :
    Real.log (k * (|t| + 3)) ≤ 6 * k * (1 + |t|) ^ (1 / 2 : ℝ) := by
  have h₁ := one_add_log_le_rpow t
  have h₂ : Real.log k ≤ k := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have h₃ : 1 ≤ (1 + |t|) ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith [abs_nonneg t])
    (by norm_num)
  rw [Real.log_mul (by linarith) (by linarith [abs_nonneg t])]
  nlinarith

/-- On the line `re s = 15/16`, `‖L'/L(s, χ)‖ ≤ A k (1 + |t|)^{1/2}`. -/
theorem exists_norm_logDeriv_le_left : ∃ A : ℝ, ∀ (k : ℕ) [NeZero k]
    (χ : DirichletCharacter ℂ k) (t : ℝ),
    ‖deriv (LFunction χ) (15 / 16 + t * I) / LFunction χ (15 / 16 + t * I)‖ ≤
      A * k * (1 + |t|) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC⟩ := norm_logDeriv_LFunction_le
  refine ⟨6 * |C|, fun k _ χ t ↦ ?_⟩
  have hd := abs_re_le_norm ((15 / 16 + t * I : ℂ) - 1)
  norm_num at hd
  have h := hC k χ (15 / 16 + t * I) (by simp) (by norm_num) hd
  have hi : (15 / 16 + t * I).im = t := by norm_num
  rw [hi] at h
  have hk : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr (NeZero.pos k)
  refine h.trans ((mul_le_mul (le_abs_self _) (log_mul_le_mul_rpow hk t)
    (Real.log_nonneg (by nlinarith [abs_nonneg t])) (abs_nonneg _)).trans_eq ?_)
  ring

end NearOne

/-! ### The smoothed sum -/

section Smoothed

open Complex ArithmeticFunction DirichletCharacter

/-- The rectangle integral recovers the right edge from the other three. -/
lemma vIntegral_eq_rectangleIntegral (F : ℂ → ℂ) (U : ℝ) :
    VIntegral F 2 (-U) U = RectangleIntegral F (15 / 16 - U * I) (2 + U * I) -
      HIntegral F (15 / 16) 2 (-U) + HIntegral F (15 / 16) 2 U +
        VIntegral F (15 / 16) (-U) U := by
  simp only [RectangleIntegral, sub_re, add_re, sub_im, add_im, mul_re, mul_im, ofReal_re,
    ofReal_im, I_re, I_im]
  norm_num
  abel

/-- The kernel `x^s / (s (s + 1))` is holomorphic on `re s > 0`. -/
lemma differentiableOn_kernel {x : ℝ} (hx : 0 < x) :
    DifferentiableOn ℂ (fun s : ℂ ↦ (x : ℂ) ^ s / (s * (s + 1))) {s : ℂ | 0 < s.re} := by
  intro s hs
  have hs₀ : s ≠ 0 := fun h ↦ by simp [h] at hs
  have hs₁ : s + 1 ≠ 0 := fun h ↦ by
    have := congrArg re h
    simp at this hs
    linarith
  have h₁ : DifferentiableAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ s) s :=
    DifferentiableAt.const_cpow differentiableAt_id (Or.inl (ofReal_ne_zero.mpr hx.ne'))
  have h₂ : DifferentiableAt ℂ (fun s : ℂ ↦ s * (s + 1)) s := by fun_prop
  exact (h₁.div h₂ (mul_ne_zero hs₀ hs₁)).differentiableWithinAt

/-- The rectangle `[15/16, 2] × [-U, U]` lies in the zero-free half-plane `re s > 7/8`. -/
lemma rectangle_subset_re_gt (U : ℝ) :
    Rectangle (15 / 16 - U * I) (2 + U * I) ⊆ {s : ℂ | 7 / 8 < s.re} := by
  intro s hs
  rw [Rectangle, mem_reProdIm] at hs
  have h := hs.1
  simp only [sub_re, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im] at h
  norm_num [Set.uIcc_of_le] at h
  exact lt_of_lt_of_le (by norm_num) h.1

/-- Across the rectangle `[15/16, 2] × [-U, U]`, the Perron integrand picks up only the
residue `x / 2` of the principal character at `s = 1`. -/
theorem rectangleIntegral_perronIntegrand {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k)
    {x : ℝ} (hx : 0 < x) {U : ℝ} (hU : 0 < U) :
    RectangleIntegral (perronIntegrand χ x) (15 / 16 - U * I) (2 + U * I) =
      if χ = 1 then 2 * Real.pi * I * (x / 2) else 0 := by
  set K : ℂ → ℂ := fun s ↦ (x : ℂ) ^ s / (s * (s + 1))
  have hKd := differentiableOn_kernel hx
  have hKΩ : ∀ s : ℂ, 7 / 8 < s.re → DifferentiableAt ℂ K s := fun s hs ↦
    hKd.differentiableAt ((isOpen_lt continuous_const continuous_re).mem_nhds
      (show (0 : ℝ) < s.re by linarith))
  split_ifs with hχ
  · subst hχ
    set g := LFunctionTrivChar₁ k
    have hg := differentiable_LFunctionTrivChar₁ k
    set H : ℂ → ℂ := fun s ↦ -(deriv g s / g s) * K s + dslope K 1 s
    have hre : (15 / 16 - U * I : ℂ).re ≤ (2 + U * I : ℂ).re := by simp; norm_num
    have him : (15 / 16 - U * I : ℂ).im ≤ (2 + U * I : ℂ).im := by simp; linarith
    have hnhds : Rectangle (15 / 16 - U * I) (2 + U * I) ∈ nhds (1 : ℂ) := by
      rw [rectangle_mem_nhds_iff, mem_reProdIm, Set.uIoo_of_le hre, Set.uIoo_of_le him]
      simp only [sub_re, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, sub_im, add_im,
        mul_im, one_re, one_im]
      norm_num
      exact hU
    have hH : HolomorphicOn H (Rectangle (15 / 16 - U * I) (2 + U * I)) := by
      intro s hs
      have hs' : 7 / 8 < s.re := rectangle_subset_re_gt U hs
      have hdg : DifferentiableAt ℂ (deriv g) s := ((hg.analyticAt s).deriv).differentiableAt
      have hslope : DifferentiableAt ℂ (dslope K 1) s := by
        have h₁ : {s : ℂ | 0 < s.re} ∈ nhds (1 : ℂ) :=
          (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
        exact ((differentiableOn_dslope h₁).mpr hKd).differentiableAt
          ((isOpen_lt continuous_const continuous_re).mem_nhds
            (show (0 : ℝ) < s.re by linarith))
      exact (((hdg.div (hg s) (regTriv_ne_zero hs')).neg.mul (hKΩ s hs')).add
        hslope).differentiableWithinAt
    have hpart : Set.EqOn (perronIntegrand (1 : DirichletCharacter ℂ k) x - fun s ↦ K 1 / (s - 1)) H
        (Rectangle (15 / 16 - U * I) (2 + U * I) \ {1}) := by
      intro s ⟨hs, hs₁⟩
      have hs' : 7 / 8 < s.re := rectangle_subset_re_gt U hs
      have hs₁' : s ≠ 1 := hs₁
      have hL : LFunction (1 : DirichletCharacter ℂ k) s ≠ 0 :=
        LFunction_ne_zero_of_seven_eighths_lt_re 1 hs' fun h ↦ hs₁' h.2
      have hsub  := sub_ne_zero.mpr hs₁'
      simp only [Pi.sub_apply, perronIntegrand, H, logDeriv_one_eq_regTriv hs' hs₁',
        dslope_of_ne _ hs₁', slope_def_field]
      change -(deriv g s / g s - 1 / (s - 1)) * K s - K 1 / (s - 1) = _
      field_simp
      ring
    have h := ResidueTheoremOnRectangleWithSimplePole hre him hnhds hH hpart
    rw [RectangleIntegral', smul_eq_mul] at h
    have hπ : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    have hK1 : K 1 = x / 2 := by simp [K]; ring
    rw [← hK1, ← h]
    field_simp
  · have hF : HolomorphicOn (perronIntegrand χ x) {s : ℂ | 7 / 8 < s.re} := by
      intro s hs
      have hs'  := hs
      have hLd := differentiable_LFunction hχ
      have hdL  :=
        ((hLd.analyticAt s).deriv).differentiableAt
      have hL  :=
        LFunction_ne_zero_of_seven_eighths_lt_re χ hs' fun h ↦ hχ h.1
      exact ((hdL.div (hLd s) hL).neg.mul (hKΩ s hs')).differentiableWithinAt
    exact hF.vanishesOnRectangle (rectangle_subset_re_gt U)

/-- The smoothed twisted prime sum:
`∑_{m ≤ x} Λ(m) χ(m) (1 - m / x) = [χ = 1] x / 2 + O(k x^{15/16})`. -/
theorem exists_norm_smoothed_sub_le : ∃ B : ℝ, ∀ (k : ℕ) [NeZero k]
    (χ : DirichletCharacter ℂ k) (x : ℝ), 2 ≤ x → (∀ m : ℕ, (m : ℝ) ≠ x) →
      ‖∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Λ m : ℂ) * χ m * (1 - m / x) -
          (if χ = 1 then (x : ℂ) / 2 else 0)‖ ≤ B * k * x ^ (15 / 16 : ℝ) := by
  obtain ⟨C₁, hC₁⟩ := PrimeTwist.exists_norm_verticalIntegral_twist_sub_le
  obtain ⟨C₂, hC₂⟩ := norm_logDeriv_LFunction_le
  obtain ⟨A, hA⟩ := exists_norm_logDeriv_le_left
  set I₀ := ∫ t : ℝ, (1 + |t|) ^ (-(3 / 2) : ℝ)
  have hI₀ : 0 ≤ I₀ := MeasureTheory.integral_nonneg fun t ↦ by positivity
  refine ⟨|C₁| + 12 * |C₂| + 64 * |A| * I₀, ?_⟩
  intro k _ χ x hx hxN
  set U := x ^ 2 with hUdef
  set L := LFunction χ
  set F := perronIntegrand χ x
  set Kx : ℂ → ℂ := fun s ↦ (x : ℂ) ^ s / (s * (s + 1))
  set S := ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Λ m : ℂ) * χ m * (1 - m / x)
  set P : ℂ := if χ = 1 then (x : ℂ) / 2 else 0
  have hx₀ : 0 < x := by linarith
  have hk : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr (NeZero.pos k)
  have hU : 4 ≤ U := by nlinarith
  have hnormF : ∀ s, ‖F s‖ = ‖deriv L s / L s‖ * ‖Kx s‖ := fun s ↦ by
    simp only [F, perronIntegrand, norm_mul, norm_neg, L, Kx]
  -- the rectangle picks up the residue
  have hR : RectangleIntegral F (15 / 16 - U * I) (2 + U * I) = 2 * Real.pi * I * P := by
    rw [rectangleIntegral_perronIntegrand χ hx₀ (by linarith)]
    split_ifs <;> simp [P, *]
  -- the horizontal edges at height `±U`
  have hH : ∀ τ ∈ ({U, -U} : Set ℝ), ‖HIntegral F (15 / 16) 2 τ‖ ≤ 6 * |C₂| * k := by
    intro τ hτ
    have hτ₂ : |τ| = U := by
      rcases hτ with rfl | rfl
      · exact abs_of_pos (by linarith)
      · rw [abs_neg]; exact abs_of_pos (by linarith)
    have hlog : Real.log (k * (U + 3)) ≤ 3 * k * U := by
      rw [Real.log_mul (by linarith) (by linarith)]
      have h₁ : Real.log k ≤ k := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
      have h₂ : Real.log (U + 3) ≤ U + 2 :=
        (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
      nlinarith
    have hpt : ∀ σ ∈ Set.Icc (15 / 16 : ℝ) 2, ‖F (σ + τ * I)‖ ≤ 3 * |C₂| * k := by
      intro σ hσ
      have hre : (σ + τ * I : ℂ).re = σ := by simp
      have him : (σ + τ * I : ℂ).im = τ := by simp
      have hfar : 1 ≤ ‖(σ + τ * I : ℂ) - 1‖ := by
        have := abs_im_le_norm ((σ + τ * I : ℂ) - 1)
        rw [sub_im, him, one_im, sub_zero, hτ₂] at this
        linarith
      have h₁ := hC₂ k χ (σ + τ * I) (by rw [hre]; exact hσ.1) (by rw [hre]; exact hσ.2) (by linarith)
      rw [him, hτ₂] at h₁
      have h₂ : ‖Kx (σ + τ * I)‖ ≤ 1 / U := by
        have h := norm_cpow_div_le_of_im_ne_zero hx₀ (s := σ + τ * I)
          (by rw [him]; intro h; rw [h, abs_zero] at hτ₂; linarith)
        rw [hre, him] at h
        have hxσ : x ^ σ ≤ x ^ 2 := by
          have := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ x) hσ.2
          rwa [Real.rpow_two] at this
        refine h.trans ?_
        rw [← sq_abs τ, hτ₂, hUdef, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have hlog₀ : 0 ≤ Real.log (k * (U + 3)) := Real.log_nonneg (by nlinarith)
      rw [hnormF]
      calc _
          ≤ (|C₂| * (3 * k * U)) * (1 / U) := by
            refine mul_le_mul (h₁.trans ?_) h₂ (norm_nonneg _) (by positivity)
            exact mul_le_mul (le_abs_self _) hlog hlog₀ (abs_nonneg _)
        _ = _ := by field_simp
    refine (PrimeTwist.norm_hIntegral_le (by norm_num) hpt).trans ?_
    have : 0 ≤ |C₂| * k := by positivity
    nlinarith
  -- the left edge `re s = 15/16`
  have hV : ‖VIntegral F (15 / 16) (-U) U‖ ≤ 64 * |A| * k * x ^ (15 / 16 : ℝ) * I₀ := by
    refine norm_vIntegral_le (by linarith) fun t ↦ ?_
    have hs : (((15 / 16 : ℝ) : ℂ) + t * I) = 15 / 16 + t * I := by push_cast; ring
    have h₁ := (hA k χ t).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)) (by positivity))
    have hre : (15 / 16 + t * I : ℂ).re = 15 / 16 := by simp
    have him : (15 / 16 + t * I : ℂ).im = t := by simp
    have h₂ := norm_cpow_div_le hx₀ (s := 15 / 16 + t * I) (by rw [hre]; norm_num)
    rw [hre, him] at h₂
    have hu : 0 < 1 + |t| := by positivity
    have h₃ : (1 + |t|) ^ (-(3 / 2) : ℝ) = (1 + |t|) ^ (1 / 2 : ℝ) / (1 + |t|) ^ 2 := by
      rw [show (-(3 / 2) : ℝ) = 1 / 2 - (2 : ℕ) by norm_num, Real.rpow_sub hu,
        Real.rpow_natCast]
    rw [hs, hnormF, h₃]
    calc _
        ≤ (|A| * k * (1 + |t|) ^ (1 / 2 : ℝ)) * (64 * x ^ (15 / 16 : ℝ) / (1 + |t|) ^ 2) :=
          mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)
      _ = _ := by
          ring
  -- truncating the vertical integral at height `U`
  have hC : ‖VerticalIntegral F 2 - VIntegral F 2 (-U) U‖ ≤ |C₁| := by
    rw [show F = PrimeTwist.twistIntegrand χ 0 x from perron_zero χ x]
    refine (hC₁ χ 0 (by linarith) (by linarith)).trans ?_
    rw [← hUdef, mul_div_assoc, div_self (by positivity), mul_one]
    exact le_abs_self _
  -- assembling the pieces
  have hS  :=
    verticalIntegral_perronIntegrand χ (by linarith) hxN
  have hsplit : 2 * Real.pi * I * (S - P) = (VerticalIntegral F 2 - VIntegral F 2 (-U) U) +
      (-HIntegral F (15 / 16) 2 (-U) + HIntegral F (15 / 16) 2 U +
        VIntegral F (15 / 16) (-U) U) := by
    rw [vIntegral_eq_rectangleIntegral, hR, hS]
    ring
  have hnorm : ‖2 * Real.pi * I * (S - P)‖ = 2 * Real.pi * ‖S - P‖ := by
    simp [abs_of_pos Real.pi_pos]
  have hle : ‖2 * Real.pi * I * (S - P)‖ ≤
      |C₁| + (6 * |C₂| * k + 6 * |C₂| * k + 64 * |A| * k * x ^ (15 / 16 : ℝ) * I₀) := by
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add hC ?_)
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add ?_ (hH U (by simp)))) hV)
    rw [norm_neg]
    exact hH (-U) (by simp)
  have hxr : 1 ≤ x ^ (15 / 16 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have h₄ : ‖S - P‖ ≤ 2 * Real.pi * ‖S - P‖ :=
    le_mul_of_one_le_left (norm_nonneg _) (by linarith [Real.two_le_pi])
  have h₅ : |C₁| ≤ |C₁| * k * x ^ (15 / 16 : ℝ) := by
    have  := one_le_mul_of_one_le_of_one_le hk hxr
    nlinarith [abs_nonneg C₁]
  have h₆ : 12 * |C₂| * k ≤ 12 * |C₂| * k * x ^ (15 / 16 : ℝ) := by
    have : 0 ≤ 12 * |C₂| * k := by positivity
    nlinarith
  have h₇ : (|C₁| + 12 * |C₂| + 64 * |A| * I₀) * k * x ^ (15 / 16 : ℝ) =
      |C₁| * k * x ^ (15 / 16 : ℝ) + 12 * |C₂| * k * x ^ (15 / 16 : ℝ) +
        64 * |A| * k * x ^ (15 / 16 : ℝ) * I₀ := by ring
  rw [h₇]
  linarith

end Smoothed

end PNT

open Complex PNT

/-- The prime number theorem in progressions with a power saving (AC0):
`∑_{n ≤ y} Λ(n) χ(n) = [χ = 1] y + O(k^C y^{1-c})`. -/
theorem sum_vonMangoldt_mul_char_sub_le : ∃ c > (0 : ℝ), ∃ C : ℝ, ∀ (k : ℕ) [NeZero k]
    (χ : DirichletCharacter ℂ k) (y : ℝ), 2 ≤ y →
    ‖∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n -
        (if χ = 1 then (y : ℂ) else 0)‖ ≤ C * (k : ℝ) ^ C * y ^ (1 - c) := by
  obtain ⟨B, hB⟩ := exists_norm_smoothed_sub_le
  set C₀ := 32 * |B| + 520
  refine ⟨1 / 64, by norm_num, C₀, fun k _ χ y hy ↦ ?_⟩
  set a : ℕ → ℂ := fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ) * χ n
  have ha : ∀ n, ‖a n‖ ≤ Real.log n := fun n ↦ by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact (mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
      (DirichletCharacter.norm_le_one χ n)).trans ArithmeticFunction.vonMangoldt_le_log
  set I₁ : ℂ := if χ = 1 then 1 else 0
  have hI₁ : ‖I₁‖ ≤ 1 := by simp only [I₁]; split_ifs <;> simp
  have hk : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr (NeZero.pos k)
  have hy₀ : 0 < y := by linarith
  -- powers of `r = y^{1/64}`
  set r := y ^ (1 / 64 : ℝ) with hr
  have hr₀ : 0 < r := Real.rpow_pos_of_pos hy₀ _
  have hr₁ : 1 ≤ r := Real.one_le_rpow (by linarith) (by norm_num)
  have hpow : ∀ n : ℕ, y ^ ((n : ℝ) / 64) = r ^ n := fun n ↦ by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hy₀.le]
    congr 1
    ring
  have hy64 : y = r ^ 64 := by rw [← hpow 64]; norm_num
  have hy60 : y ^ (15 / 16 : ℝ) = r ^ 60 := by rw [← hpow 60]; norm_num
  have hy62 : y ^ (31 / 32 : ℝ) = r ^ 62 := by rw [← hpow 62]; norm_num
  have hy63 : y ^ (1 - 1 / 64 : ℝ) = r ^ 63 := by rw [← hpow 63]; norm_num
  have hr62 : r ^ 62 ≤ r ^ 63 := pow_le_pow_right₀ hr₁ (by norm_num)
  have hr63 : r ^ 63 ≤ r ^ 64 := pow_le_pow_right₀ hr₁ (by norm_num)
  have hr1 : 1 ≤ r ^ 62 := one_le_pow₀ hr₁
  -- the evaluation points `x = ⌊y⌋ + 1/2` and `x + h`, with `h = ⌈y^{31/32}⌉`
  set m := ⌊y⌋₊
  set x : ℝ := m + 1 / 2
  have hmy : (m : ℝ) ≤ y := Nat.floor_le hy₀.le
  have hym : y < m + 1 := Nat.lt_floor_add_one y
  have hx : 2 ≤ x := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast Nat.le_floor (by exact_mod_cast hy)
    simp only [x]
    linarith
  have hxfloor : ⌊x⌋₊ = m := by
    rw [Nat.floor_eq_iff (by linarith)]
    constructor <;> simp only [x] <;> linarith
  set h := ⌈y ^ (31 / 32 : ℝ)⌉₊
  have hh₁ : r ^ 62 ≤ h := hy62 ▸ Nat.le_ceil _
  have hh₂ : (h : ℝ) ≤ 2 * r ^ 62 := by
    have h₁ : (h : ℝ) < y ^ (31 / 32 : ℝ) + 1 :=
      Nat.ceil_lt_add_one (show 0 ≤ y ^ (31 / 32 : ℝ) by positivity)
    rw [hy62] at h₁
    linarith
  have hh₀ : (0 : ℝ) < h := by linarith
  have hhalf : ∀ n : ℕ, ∀ j : ℕ, (n : ℝ) ≠ j + 1 / 2 := by
    intro n j hn
    have : ((2 * n : ℕ) : ℝ) = ((2 * j + 1 : ℕ) : ℝ) := by push_cast; linarith
    have := Nat.cast_injective this
    omega
  have hxN : ∀ n : ℕ, (n : ℝ) ≠ x := fun n ↦ hhalf n m
  have hxhN : ∀ n : ℕ, (n : ℝ) ≠ x + h := fun n hn ↦ hhalf n (m + h) (by rw [hn]; push_cast; ring)
  have hxh : x + h ≤ 4 * r ^ 64 := by
    simp only [x]
    nlinarith
  -- the weighted sums `W(z) = ∑_{n ≤ z} a(n) (z - n)` are `I₁ z²/2 + O(k z^{31/16})`
  have hW : ∀ z : ℝ, 2 ≤ z → (∀ n : ℕ, (n : ℝ) ≠ z) → z ≤ 4 * r ^ 64 →
      ‖∑ n ∈ Finset.Icc 1 ⌊z⌋₊, a n * ((z : ℂ) - n) - I₁ * ((z : ℂ) ^ 2 / 2)‖ ≤
        16 * |B| * k * r ^ 124 := by
    intro z hz hzN hz₄
    have hz₀ : (z : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
    have h₁ := hB k χ z hz hzN
    have heq : ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, a n * ((z : ℂ) - n) - I₁ * ((z : ℂ) ^ 2 / 2) =
        (z : ℂ) * (∑ m ∈ Finset.Icc 1 ⌊z⌋₊,
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ m * (1 - m / z) -
            (if χ = 1 then (z : ℂ) / 2 else 0)) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun n _ ↦ ?_
        simp only [a]
        field_simp
      · simp only [I₁]
        split_ifs <;> ring
    rw [heq, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have hz15 : z ^ (15 / 16 : ℝ) ≤ 4 * r ^ 60 := by
      calc z ^ (15 / 16 : ℝ) ≤ (4 * y) ^ (15 / 16 : ℝ) :=
            Real.rpow_le_rpow (by linarith) (by rw [hy64]; exact hz₄) (by norm_num)
        _ = 4 ^ (15 / 16 : ℝ) * r ^ 60 := by
            rw [Real.mul_rpow (by norm_num) hy₀.le, hy60]
        _ ≤ 4 * r ^ 60 := by
            gcongr
            calc (4 : ℝ) ^ (15 / 16 : ℝ) ≤ 4 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 4 := Real.rpow_one 4
    have h₂ : ‖_‖ ≤ |B| * k * (4 * r ^ 60) :=
      h₁.trans (by gcongr; exact le_abs_self B)
    calc z * ‖_‖ ≤ (4 * r ^ 64) * (|B| * k * (4 * r ^ 60)) :=
          mul_le_mul hz₄ h₂ (norm_nonneg _) (by positivity)
      _ = 16 * |B| * k * r ^ 124 := by ring
  have hWx := hW x hx hxN (by linarith)
  have hWxh := hW (x + h) (by linarith) hxhN hxh
  -- the differencing error
  have hR := SmoothedPerron.ramp_error a (show 0 ≤ x by linarith) h ⌊x⌋₊ le_rfl
    (Nat.le_add_right ..) (B := Real.log (x + h)) (fun n hn => (ha n).trans (Real.log_le_log
      (Nat.cast_pos.mpr (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1)) (by
        have hn' : (n : ℝ) ≤ ⌊x⌋₊ + h := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
        linarith [Nat.floor_le (show 0 ≤ x by linarith)])))
  unfold SmoothedPerron.ramp at hR
  have hlog : Real.log (x + h) ≤ 256 * r := by
    have h₁ := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ x + h) (by norm_num : (0 : ℝ) < 1 / 64)
    have h₂ : (x + h) ^ (1 / 64 : ℝ) ≤ 4 * r := by
      calc (x + h) ^ (1 / 64 : ℝ) ≤ (4 * y) ^ (1 / 64 : ℝ) :=
            Real.rpow_le_rpow (by linarith) (by rw [hy64]; exact hxh) (by norm_num)
        _ = 4 ^ (1 / 64 : ℝ) * r := by rw [Real.mul_rpow (by norm_num) hy₀.le]
        _ ≤ 4 * r := by
            gcongr
            calc (4 : ℝ) ^ (1 / 64 : ℝ) ≤ 4 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 4 := Real.rpow_one 4
    calc Real.log (x + h) ≤ (x + h) ^ (1 / 64 : ℝ) / (1 / 64) := h₁
      _ ≤ 4 * r / (1 / 64) := by gcongr
      _ = 256 * r := by ring
  -- the identity behind the differencing
  set S := ∑ n ∈ Finset.Icc 1 m, a n
  set Wx := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * ((x : ℂ) - n)
  set Wxh := ∑ n ∈ Finset.Icc 1 ⌊x + h⌋₊, a n * (((x + h : ℝ) : ℂ) - n)
  have hid : (h : ℂ) * (S - I₁ * y) = (Wxh - I₁ * (((x + h : ℝ) : ℂ) ^ 2 / 2)) -
      (Wx - I₁ * ((x : ℂ) ^ 2 / 2)) - (Wxh - Wx - h * S) +
        I₁ * (h * ((x : ℂ) - y + h / 2)) := by
    push_cast
    ring
  have hxy : ‖(x : ℂ) - y + h / 2‖ ≤ 1 / 2 + h / 2 := by
    rw [show (x : ℂ) - y + h / 2 = ((x - y + h / 2 : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_eq_abs, abs_le]
    simp only [x]
    constructor <;> linarith
  have hmain : (h : ℝ) * ‖S - I₁ * y‖ ≤ 32 * |B| * k * r ^ 124 +
      h ^ 2 * (256 * r) + h * (1 / 2 + h / 2) := by
    have h₁ : ‖(h : ℂ) * (S - I₁ * y)‖ = h * ‖S - I₁ * y‖ := by
      rw [norm_mul, Complex.norm_natCast]
    rw [← h₁, hid]
    have h₂ : ‖I₁ * (h * ((x : ℂ) - y + h / 2))‖ ≤ h * (1 / 2 + h / 2) := by
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      calc ‖I₁‖ * (h * ‖(x : ℂ) - y + h / 2‖) ≤ 1 * (h * (1 / 2 + h / 2)) := by
            gcongr
        _ = h * (1 / 2 + h / 2) := one_mul _
    have h₃ : ‖Wxh - Wx - h * S‖ ≤ h ^ 2 * (256 * r) := by
      rw [hxfloor] at hR
      refine hR.trans ?_
      gcongr
    have h₄ := norm_add_le ((Wxh - I₁ * (((x + h : ℝ) : ℂ) ^ 2 / 2)) -
      (Wx - I₁ * ((x : ℂ) ^ 2 / 2)) - (Wxh - Wx - h * S)) (I₁ * (h * ((x : ℂ) - y + h / 2)))
    have h₅ := norm_sub_le ((Wxh - I₁ * (((x + h : ℝ) : ℂ) ^ 2 / 2)) -
      (Wx - I₁ * ((x : ℂ) ^ 2 / 2))) (Wxh - Wx - h * S)
    have h₆ := norm_sub_le (Wxh - I₁ * (((x + h : ℝ) : ℂ) ^ 2 / 2)) (Wx - I₁ * ((x : ℂ) ^ 2 / 2))
    linarith
  -- dividing by `h ≥ r^62`
  have hfinal : ‖S - I₁ * y‖ ≤ C₀ * k * r ^ 63 := by
    refine le_of_mul_le_mul_left (hmain.trans ?_) hh₀
    have hB₀ : 0 ≤ |B| * k := by positivity
    have e₁ : 32 * |B| * k * r ^ 124 ≤ h * (32 * |B| * k * r ^ 63) := by
      have : r ^ 124 ≤ r ^ 62 * r ^ 63 := by
        rw [← pow_add]; exact pow_le_pow_right₀ hr₁ (by norm_num)
      calc 32 * |B| * k * r ^ 124 ≤ 32 * |B| * k * (r ^ 62 * r ^ 63) := by gcongr
        _ ≤ 32 * |B| * k * (h * r ^ 63) := by gcongr
        _ = h * (32 * |B| * k * r ^ 63) := by ring
    have e₂ : (h : ℝ) ^ 2 * (256 * r) ≤ h * (512 * r ^ 63) := by
      have : (h : ℝ) * r ≤ 2 * r ^ 63 := by
        calc (h : ℝ) * r ≤ 2 * r ^ 62 * r := by gcongr
          _ = 2 * r ^ 63 := by ring
      nlinarith
    have e₃ : (h : ℝ) * (1 / 2 + h / 2) ≤ h * (2 * r ^ 63) := by
      gcongr
      linarith
    have e₄ : 32 * |B| * k * r ^ 63 + 512 * r ^ 63 + 2 * r ^ 63 ≤ C₀ * k * r ^ 63 := by
      have h₁ : (514 : ℝ) * r ^ 63 ≤ 520 * k * r ^ 63 := by
        have : 0 ≤ r ^ 63 := by positivity
        nlinarith
      have h₂ : C₀ * k * r ^ 63 = 32 * |B| * k * r ^ 63 + 520 * k * r ^ 63 := by
        simp only [C₀]; ring
      linarith
    calc 32 * |B| * k * r ^ 124 + (h : ℝ) ^ 2 * (256 * r) + h * (1 / 2 + h / 2)
        ≤ h * (32 * |B| * k * r ^ 63) + h * (512 * r ^ 63) + h * (2 * r ^ 63) := by
          linarith
      _ = h * (32 * |B| * k * r ^ 63 + 512 * r ^ 63 + 2 * r ^ 63) := by ring
      _ ≤ h * (C₀ * k * r ^ 63) := mul_le_mul_of_nonneg_left e₄ hh₀.le
  -- conclude
  have hS : ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n -
      (if χ = 1 then (y : ℂ) else 0) = S - I₁ * y := by
    simp only [S, I₁, a, m]
    split_ifs <;> ring
  have hC₀ : 1 ≤ C₀ := by simp only [C₀]; linarith [abs_nonneg B]
  have hkC : (k : ℝ) ≤ (k : ℝ) ^ C₀ := by
    calc (k : ℝ) = (k : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (k : ℝ) ^ C₀ := Real.rpow_le_rpow_of_exponent_le hk hC₀
  rw [hS, hy63]
  calc ‖S - I₁ * y‖ ≤ C₀ * k * r ^ 63 := hfinal
    _ ≤ C₀ * (k : ℝ) ^ C₀ * r ^ 63 := by gcongr

end Erdos408
