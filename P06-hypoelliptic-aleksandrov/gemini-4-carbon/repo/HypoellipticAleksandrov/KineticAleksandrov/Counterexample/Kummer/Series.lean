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

/-- The rising factorial at order zero. -/
@[simp] theorem poch_zero (a : ℝ) : poch a 0 = 1 := by
  simp only [poch, ascPochhammer_zero, Polynomial.eval_one]


/-- Right recurrence for the rising factorial. -/
theorem poch_succ (a : ℝ) (n : ℕ) : poch a (n + 1) = poch a n * (a + n) := by
  simp [poch, ascPochhammer_succ_right]

/-- Positive parameters have nonzero rising factorials. -/
theorem poch_pos (b : Pos) (n : ℕ) : 0 < poch b.1 n :=
  ascPochhammer_pos n b.1 b.2

/-- The constant coefficient is normalized to one. -/
@[simp] theorem coeff_zero (a : ℝ) (b : Pos) : coeff a b 0 = 1 := by
  simp [coeff]




/-- Coefficient bridge to Mathlib's regularized confluent series. -/
theorem coeff_eq_regularized (a : ℝ) (b : Pos) (n : ℕ) :
    (coeff a b n : ℂ) = Complex.Gamma (b.1 : ℂ) *
      Complex.regularizedHGFunCoeff {(a : ℂ)} {(b.1 : ℂ)} n   := by
  have parameter_ne_neg_nat (k : ℕ) :
      (b.1 : ℂ) ≠ -k := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    have hk : 0 ≤ k := Nat.cast_nonneg k
    linarith [b.2]
  have poch_ofReal (a : ℝ) (n : ℕ) :
      (poch a n : ℂ) = (ascPochhammer ℂ n).eval (a : ℂ) := by
    induction n with
    | zero => simp [poch]
    | succ n ih => simp [poch_succ, ascPochhammer_succ_right, ih]
  rw [coeff, Complex.ofReal_div, Complex.ofReal_mul, poch_ofReal, poch_ofReal]
  rw [← Complex.Gamma_add_nat_div_Gamma_eq (b.1 : ℂ) (parameter_ne_neg_nat)]
  simp only [Complex.regularizedHGFunCoeff, Multiset.map_singleton,
    Multiset.prod_singleton, Complex.ofReal_natCast]
  field_simp

/-- The literal complex series equals the Gamma-normalized regularized function. -/
theorem Mc_eq_regularized (a : ℝ) (b : Pos) (z : ℂ) :
    Mc a b z = Complex.Gamma (b.1 : ℂ) *
      Complex.regularizedHGFun {(a : ℂ)} {(b.1 : ℂ)} z := by
  rw [Mc, Complex.regularizedHGFun, Complex.regularizedHGFunSeries,
    ← FormalMultilinearSeries.ofScalarsSum, FormalMultilinearSeries.ofScalars_sum_eq]
  simp [coeff_eq_regularized, mul_assoc, tsum_mul_left]


/-- The complex series converges to its defined sum. -/
theorem hasSum_Mc (a : ℝ) (b : Pos) (z : ℂ) :
    HasSum (fun n : ℕ => (coeff a b n : ℂ) * z ^ n) (Mc a b z)  := by
  have hasSum_regularized :
      HasSum (fun n =>
      Complex.regularizedHGFunCoeff {(a : ℂ)} {(b.1 : ℂ)} n * z ^ n)
      (Complex.regularizedHGFun {(a : ℂ)} {(b.1 : ℂ)} z) := by
    have hr : (Complex.regularizedHGFunSeries {(a : ℂ)} {(b.1 : ℂ)}).radius = ⊤ :=
      Complex.radius_regularizedHGFunSeries_eq_top (by simp)
    have hz : z ∈ Metric.eball 0
        (Complex.regularizedHGFunSeries {(a : ℂ)} {(b.1 : ℂ)}).radius := by
      rw [hr]
      simp
    simpa only [Complex.regularizedHGFun, Complex.regularizedHGFunSeries,
      FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using
      (Complex.regularizedHGFunSeries {(a : ℂ)} {(b.1 : ℂ)}).hasSum hz
  simpa only [coeff_eq_regularized, mul_assoc, Mc_eq_regularized] using
    (hasSum_regularized).mul_left (Complex.Gamma (b.1 : ℂ))

/-- The real series converges to its defined sum. -/
theorem hasSum_M (a : ℝ) (b : Pos) (z : ℝ) :
    HasSum (fun n : ℕ => coeff a b n * z ^ n) (M a b z) := by
  apply Summable.hasSum
  apply Complex.summable_ofReal.mp
  simpa using
    (hasSum_Mc a b (z : ℂ)).summable

/-- Compatibility of the real and complex power series. -/
theorem Mc_ofReal (a : ℝ) (b : Pos) (z : ℝ) : Mc a b (z : ℂ) = (M a b z : ℂ) := by
  exact (hasSum_Mc a b (z : ℂ)).unique
    (by simpa using
      Complex.hasSum_ofReal.mpr (hasSum_M a b z))


/-- The real Kummer function is real analytic everywhere. -/
theorem analyticOnNhd_M (a : ℝ) (b : Pos) : AnalyticOnNhd ℝ (M a b) Set.univ  := by
  intro z _
  have analyticOnNhd_Mc :
      AnalyticOnNhd ℂ (Mc a b) Set.univ := by
    rw [(funext (Mc_eq_regularized a b))]
    intro z _
    exact analyticAt_const.mul
      (Complex.analyticAt_regularizedHGFun_of_card_le (by simp) z)
  have hi :=
    (analyticOnNhd_Mc (z : ℂ) (Set.mem_univ _)).restrictScalars (𝕜 := ℝ).comp (Complex.ofRealCLM.analyticAt z)
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.reCLM_apply,
    Mc_ofReal, Complex.ofReal_re] using ((Complex.reCLM.analyticAt (Mc a b (z : ℂ))).comp (f := fun x : ℝ => Mc a b (x : ℂ)) hi)

/-- Value of the series at the regular singular point. -/
@[simp] theorem M_zero (a : ℝ) (b : Pos) : M a b 0 = 1 := by
  rw [M, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
