module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# The confluent hypergeometric power series

Literal real and complex series for Kummer M, with positive denominator parameter.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

/-- Positive real parameters. -/
abbrev Pos := {x : ℝ // 0 < x}

/-- The negative parameter interval used by the scalar counterexample. -/
abbrev NegThird := {x : ℝ // -(1 / 3 : ℝ) < x ∧ x < 0}

/-- The rising factorial. -/
def poch (a : ℝ) (n : ℕ) : ℝ := (ascPochhammer ℝ n).eval a

/-- The coefficient of the confluent hypergeometric series. -/
def coeff (a : ℝ) (b : Pos) (n : ℕ) : ℝ :=
  poch a n / (poch b.1 n * (n.factorial : ℝ))

/-- Kummer M on the real line. -/
def M (a : ℝ) (b : Pos) (z : ℝ) : ℝ :=
  ∑' n : ℕ, coeff a b n * z ^ n

/-- The same series on the complex plane. -/
def Mc (a : ℝ) (b : Pos) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (coeff a b n : ℂ) * z ^ n

/-- The first denominator parameter in the scalar profile. -/
def b23 : Pos := ⟨2 / 3, by positivity⟩

/-- The second denominator parameter in the scalar profile. -/
def b43 : Pos := ⟨4 / 3, by positivity⟩

variable (a : ℝ) (b : Pos) (z : ℂ) (n : ℕ)

/-- The rising factorial at order zero. -/
@[simp] theorem poch_zero  : poch a 0 = 1 := by
  simp only [poch, ascPochhammer_zero, Polynomial.eval_one]

/-- The rising factorial at order one. -/
@[simp] theorem poch_one  : poch a 1 = a := by
  simp only [poch, ascPochhammer_one, Polynomial.eval_X]

/-- Right recurrence for the rising factorial. -/
theorem poch_succ  : poch a (n + 1) = poch a n * (a + n) := by
  simp [poch, ascPochhammer_succ_right]

/-- Positive parameters have nonzero rising factorials. -/
theorem poch_pos  : 0 < poch b.1 n :=
  ascPochhammer_pos n b.1 b.2

/-- The constant coefficient is normalized to one. -/
@[simp] theorem coeff_zero  : coeff a b 0 = 1 := by
  simp [coeff]

/-- The linear coefficient. -/
@[simp] theorem coeff_one  : coeff a b 1 = a / b.1 := by
  simp [coeff]

private theorem poch_ofReal  :
    (poch a n : ℂ) = (ascPochhammer ℂ n).eval (a : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih => simp [poch_succ, ascPochhammer_succ_right, ih]

private theorem parameter_ne_neg_nat  (k : ℕ) : (b.1 : ℂ) ≠ -k := by
  intro h
  have hr := congrArg Complex.re h
  simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hr
  grind

/-- Coefficient bridge to Mathlib's regularized confluent series. -/
theorem coeff_eq_regularized  :
    (coeff a b n : ℂ) = Complex.Gamma (b.1 : ℂ) *
      Complex.regularizedHGFunCoeff {(a : ℂ)} {(b.1 : ℂ)} n := by
  rw [coeff, Complex.ofReal_div, Complex.ofReal_mul, poch_ofReal, poch_ofReal, ← Complex.Gamma_add_nat_div_Gamma_eq _ (parameter_ne_neg_nat b)]
  simp only [Complex.regularizedHGFunCoeff, Multiset.map_singleton,
    Multiset.prod_singleton, Complex.ofReal_natCast]
  field_simp

/-- The literal complex series equals the Gamma-normalized regularized function. -/
theorem Mc_eq_regularized  :
    Mc a b z = Complex.Gamma (b.1 : ℂ) *
      Complex.regularizedHGFun {(a : ℂ)} {(b.1 : ℂ)} z := by
  rw [Mc, Complex.regularizedHGFun, Complex.regularizedHGFunSeries,
    ← FormalMultilinearSeries.ofScalarsSum, FormalMultilinearSeries.ofScalars_sum_eq]
  simp only [coeff_eq_regularized, mul_assoc, tsum_mul_left, smul_eq_mul]

/-- Convergence of the regularized series at every complex argument. -/
theorem hasSum_regularized  :
    HasSum (fun n : ℕ =>
      Complex.regularizedHGFunCoeff {(a : ℂ)} {(b.1 : ℂ)} n * z ^ n)
      (Complex.regularizedHGFun {(a : ℂ)} {(b.1 : ℂ)} z) := by
  have hr : (Complex.regularizedHGFunSeries {(a : ℂ)} {(b.1 : ℂ)}).radius = ⊤ :=
    Complex.radius_regularizedHGFunSeries_eq_top (by simp)
  have hz : z ∈ Metric.eball (0)
      (Complex.regularizedHGFunSeries {(a : ℂ)} {(b.1 : ℂ)}).radius := by
    simp_all
  simpa only [Complex.regularizedHGFun, Complex.regularizedHGFunSeries,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using
    (Complex.regularizedHGFunSeries _ _).hasSum hz

/-- The complex series converges to its defined sum. -/
theorem hasSum_Mc  :
    HasSum (fun n : ℕ => (coeff a b n : ℂ) * z ^ n) (Mc a b z) := by
  simpa only [coeff_eq_regularized, mul_assoc, Mc_eq_regularized] using
    (hasSum_regularized a b z).mul_left _

/-- The real series converges to its defined sum. -/
theorem hasSum_M  (z : ℝ) :
    HasSum (fun n : ℕ => coeff a b n * z ^ n) (M a b z) := by
  apply Summable.hasSum
  apply Complex.summable_ofReal.mp
  simpa using
    (hasSum_Mc a b _).summable

/-- Compatibility of the real and complex power series. -/
theorem Mc_ofReal  (z : ℝ) : Mc a b (z : ℂ) = (M a b z : ℂ) := (hasSum_Mc a b _).unique
    (by simpa using
      Complex.hasSum_ofReal.mpr (hasSum_M a b z))

/-- The complex Kummer series is entire. -/
theorem analyticOnNhd_Mc  : AnalyticOnNhd ℂ (Mc a b) Set.univ := by
  have heq  :=
    funext (Mc_eq_regularized a b)
  rw [heq]
  intro z _
  exact analyticAt_const.mul
    (Complex.analyticAt_regularizedHGFun_of_card_le (by simp) z)

/-- The real Kummer function is real analytic everywhere. -/
theorem analyticOnNhd_M  : AnalyticOnNhd ℝ (M a b) Set.univ := by
  intro z _
  have hc := (analyticOnNhd_Mc a b z (Set.mem_univ _)).restrictScalars (𝕜 := ℝ)
  have hi : AnalyticAt ℝ (fun x : ℝ => Mc a b _) z :=
    hc.comp (Complex.ofRealCLM.analyticAt z)
  have h := (Complex.reCLM.analyticAt _).comp
    (f := fun x : ℝ => Mc a b _) hi
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.reCLM_apply,
    Mc_ofReal, Complex.ofReal_re] using h

/-- Value of the series at the regular singular point. -/
@[simp] theorem M_zero  : M a b 0 = 1 := by
  rw [M, tsum_eq_single 0]
  · simp
  simp_all

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
