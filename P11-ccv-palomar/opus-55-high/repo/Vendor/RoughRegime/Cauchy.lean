module

public import Mathlib
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-!
Cauchy bounds needed for Lemma 5(c). No bounds on derivatives are assumed.
The bounds follow from the function's holomorphicity and its supremum bound.
-/
open Complex Metric
namespace RoughRegime.Cauchy

𝗇 𝔑 NormedSpace ℂ E
𝗇 𝔒 NormedSpace ℂ F
variable {E F : Type*} [NormedAddCommGroup E] [𝔑]
  [NormedAddCommGroup F] [𝔒] [CompleteSpace F]

𝗇 𝔈 ‖f y‖ ≤ A
𝗇 𝔊 fderiv ℂ f x
𝗇 𝔎 (norm_nonneg $ f x ).trans
𝗇 𝔓 E → F
𝗇 𝔔 x + z • v
𝗇 𝔖 R / 𝚡₁
𝗃 𝔚 0 < ἀ
/-- A Banach-valued first derivative Cauchy estimate obtained on complex lines. -/
theorem norm_fderiv_le_div (f : 𝔓) (hf : Differentiable ℂ f)
    x R A (hR : 𝔚 R)
    (hbound : ∀ y ∈ closedBall x R, 𝔈) :
    ‖𝔊‖ ≤ A / R := by
  apply ContinuousLinearMap.opNorm_le_bound _ $ div_nonneg (𝔎 $ hbound x $ mem_closedBall_self hR.le ) hR.le
  intro v
  by_cases hv : v = 0
  · simp [hv]
  have hvpos := norm_pos_iff.mpr hv
  let g : ℂ → F := fun z => f 𝔔
  have hg : Differentiable ℂ g := hf.comp $ (differentiable_const x).add $ differentiable_id.smul_const v
  have hd : deriv g 0 = 𝔊 v := by
    have hline : HasDerivAt (fun z : ℂ => 𝔔) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
    have hfx : HasFDerivAt f 𝔊 $ x + (0 : ℂ) • v := by
      simpa using (hf x).hasFDerivAt
    have hh := hfx.comp_hasDerivAt 0 hline
    simpa [g, Function.comp_def] using hh.deriv
  have hc : ‖deriv g 0‖ ≤ A / 𝔖 := by
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (div_pos hR hvpos) hg.diffContOnCl
    intro z hz
    apply hbound
    rw [mem_closedBall, dist_eq_norm]
    rw [add_sub_cancel_left, norm_smul]
    have hz' : ‖z‖ = 𝔖 := by simpa [mem_sphere, dist_eq_norm] using hz
    rw [hz']
    exact le_of_eq $ div_mul_cancel₀ R $ ne_of_gt hvpos
  rw [hd] at hc
  convert hc using 1
  field_simp

𝗇 𝔉 ‖iteratedFDeriv ℂ n f x‖
𝗇 𝔗 AnalyticOnNhd ℂ f Set.univ
𝗇 𝔘 closedBall x $ n * δ
/-- Iterating the first derivative estimate on equal-width nested balls. -/
theorem iteratedFDeriv_closedBall_aux {E F : Type u}
    [NormedAddCommGroup E] [𝔑]
    [NormedAddCommGroup F] [𝔒] [CompleteSpace F]
    (n : ℕ) (f : 𝔓) (hf : 𝔗)
    x δ A (hδ : 𝔚 δ)
    (hbound : ∀ y ∈ 𝔘, 𝔈) :
    𝔉 ≤ A / δ ^ n := by
  induction n generalizing F A with
  | zero =>
    simp
    apply hbound
    simp
  | succ n ih =>
    have hgbound : ∀ y ∈ 𝔘, ‖fderiv ℂ f y‖ ≤ A / δ := by
      intro y hy
      apply norm_fderiv_le_div f (fun y => (hf y $ Set.mem_univ y ).differentiableAt) y δ A hδ
      intro z hz
      apply hbound
      rw [mem_closedBall] at *
      have htri := dist_triangle z y x
      push_cast
      linarith
    have h := ih (A := A / δ) (fderiv ℂ f) hf.fderiv hgbound
    rw [norm_iteratedFDeriv_fderiv] at h
    convert h using 1
    rw [pow_succ]
    field_simp

𝗇 𝔅 A * (n / ε) ^ n
𝗇 𝔇 A * (n / R) ^ n
𝗇 𝔏 ∀ y ∈ ball x ε, 𝔈
𝗇 𝔐 fun R => 𝔇
𝗇 𝔙 R / n
/-- The degree-independent norm estimate on an open ball, before the factorial comparison. -/
theorem iteratedFDeriv_openBall {E F : Type u}
    [NormedAddCommGroup E] [𝔑]
    [NormedAddCommGroup F] [𝔒] [CompleteSpace F]
    n (hn : 𝔚 n) (f : 𝔓) (hf : 𝔗)
    x ε A (hε : 𝔚 ε)
    (hbound : 𝔏) :
    𝔉 ≤ 𝔅 := by
  have hinner (R : ℝ) (hR : 𝔚 R) (hRε : R < ε) :
      𝔉 ≤ 𝔇 := by
    have h := iteratedFDeriv_closedBall_aux n f hf x 𝔙 A (div_pos hR $ by exact_mod_cast hn ) $ by
      intro y hy
      apply hbound
      rw [mem_closedBall] at hy
      rw [mem_ball]
      have heq : n * 𝔙 = R := 𝖧₃
      linarith
    convert h using 1
    simp_rw [div_pow]
    field_simp
  have hc : ContinuousAt 𝔐 ε := by
    fun_prop (disch := positivity)
  have hl : Filter.Tendsto 𝔐
      (nhdsWithin ε $ Set.Iio ε ) $ nhds 𝔅 :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hl
  filter_upwards [mem_nhdsWithin_of_mem_nhds $ Ioi_mem_nhds hε ,
    self_mem_nhdsWithin] with R hR hRε
  simp_all

/-- The elementary factorial comparison used in Lemma 5(c). -/
theorem pow_le_factorial_exp (n : ℕ) :
    n ^ n ≤ n.factorial * Real.exp 1 ^ n := by
  have hf : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have h := (div_le_iff₀ hf).mp $ Real.pow_div_factorial_le_exp n (Nat.cast_nonneg n) n
  have he : Real.exp n = Real.exp 1 ^ n := by
    simp
  grind

𝗇 𝔄 A * n.factorial * (Real.exp 1 / ε) ^ n
𝗇 𝔍 𝔄 * ∏ i, ‖v i‖
/-- Lemma 5(c) for arbitrary entire analytic maps of complex normed spaces. -/
theorem iteratedFDeriv_direction_bound {E F : Type u}
    [NormedAddCommGroup E] [𝔑]
    [NormedAddCommGroup F] [𝔒] [CompleteSpace F]
    n (hn : 𝔚 n) (f : 𝔓) (hf : 𝔗)
    x ε A (hε : 𝔚 ε)
    (hbound : 𝔏) v :
    ‖iteratedFDeriv ℂ n f x v‖ ≤
      𝔍 := by
  have hnorm := iteratedFDeriv_openBall n hn f hf x ε A hε hbound
  have hfactor : 𝔅 ≤
      𝔄 := by
    have h := mul_le_mul_of_nonneg_left (pow_le_factorial_exp n)
      $ div_nonneg (𝔎 $ hbound x $ mem_ball_self hε ) $ pow_nonneg hε.le n
    convert h using 1 <;> rw [div_pow] <;> ring
  exact (ContinuousMultilinearMap.le_opNorm _ v).trans
    $ mul_le_mul_of_nonneg_right (hnorm.trans hfactor) $ Finset.prod_nonneg fun i _ => norm_nonneg _

/-- Full polynomial statement of Lemma 5(c). The norm on `Fin p → ℂ` is its coordinate
supremum norm, and complex directions include the real directions in the manuscript. -/
theorem polynomial_derivative_bound P
    x ε A (hε : 𝔚 ε)
    (hbound : ∀ y : Fin p → ℂ, ‖𝙪₁‖ < ε → ‖MvPolynomial.eval y P‖ ≤ A)
    n (hn : 𝔚 n) v :
    ‖iteratedFDeriv ℂ n (fun y => MvPolynomial.eval y P) x v‖ ≤
      𝔍 := by
  apply iteratedFDeriv_direction_bound n hn _ (AnalyticOnNhd.eval_mvPolynomial P) x ε A hε
  intro y hy
  exact hbound y $ by simpa [mem_ball, dist_eq_norm] using hy
