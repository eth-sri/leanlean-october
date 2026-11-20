module

public import NearlyMinimax.ScoreSupport
public import NearlyMinimax.ParametricConstants
public import NearlyMinimax.TernaryMeasure
public import NearlyMinimax.ModelRegularity
public import NearlyMinimax.PathRisk

@[expose] public section

/-! # The actual low-smoothness ternary prior

This file connects the finite likelihood construction to the original model.
In the order-zero regime a globally bounded Hölder regression gives an
admissible extension on every extension domain in `ModelConstants`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace NearlyMinimax

theorem ternaryMass_measurable_comp {α : Type*} [MeasurableSpace α]
    (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (y : Fin 3) :
    Measurable (fun x => ternaryMass a (F x) V y) := ternaryMass_measurable a hF measurable_const measurable_const

/-- The errors have actual values `-a-f(x)`, `-f(x)`, and `a-f(x)`. -/
def ternaryErrorKernel {α : Type*} [MeasurableSpace α]
    (a V : ℝ) (F : α → ℝ) (hF : Measurable F) : Kernel α ℝ :=
  weightedAtomKernel (fun x => ternaryMass a (F x) V) (fun x y => ternaryValue a y - F x)
    (ternaryMass_measurable_comp a V F hF) (fun _ => measurable_const.sub hF)

section
variable {α : Type*} [MeasurableSpace α]
    (a V : ℝ) (F : α → ℝ) (hF : Measurable F)

theorem ternaryErrorKernel_apply (x : α) :
    ternaryErrorKernel a V F hF x = ∑ y : Fin 3,
      ENNReal.ofReal (ternaryMass a (F x) V y) •
        Measure.dirac (ternaryValue a y - F x) := rfl

theorem ternaryErrorKernel_markov (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    IsMarkovKernel (ternaryErrorKernel a V F hF) :=
  weightedAtomKernel_markov _ _ _ _ hp (fun x => ternary_normalized a (F x) V)

section
variable (x : α)

theorem ternary_error_integrable (G : ℝ → ℝ) :
    Integrable G (ternaryErrorKernel a V F hF x) := weightedAtomMeasure_integrable _ _ _

theorem ternary_error_integral
    (hp : ∀ y, 0 ≤ ternaryMass a (F x) V y) (G : ℝ → ℝ) :
    (∫ u, G u ∂ternaryErrorKernel a V F hF x) =
      ∑ y, ternaryMass a (F x) V y * G (ternaryValue a y - F x) :=
  weightedAtomMeasure_integral _ (fun y => ternaryValue a y - F x) hp G

theorem ternary_error_mean
    (ha : a ≠ 0) (hp : ∀ y, 0 ≤ ternaryMass a (F x) V y) :
    (∫ u, u ∂ternaryErrorKernel a V F hF x) = 0 := by
  rw [ternary_error_integral a V F hF x hp]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hm := ternary_mean a (F x) V ha
  change (∑ y, ternaryMass a (F x) V y * ternaryValue a y) = F x at hm
  simp [hm, ternary_normalized a (F x) V]

end

theorem ternary_error_moments (ha : a ≠ 0) (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    {B : ℝ} (hb : ∀ x, ternaryExpectation a (F x) V (fun y => (y-F x)^4) ≤ B) (x : α) :
    Integrable (fun u : ℝ => u) (ternaryErrorKernel a V F hF x) ∧
    Integrable (fun u : ℝ => u^2) (ternaryErrorKernel a V F hF x) ∧
    Integrable (fun u : ℝ => u^4) (ternaryErrorKernel a V F hF x) ∧
    (∫ u, u ∂ternaryErrorKernel a V F hF x) = 0 ∧
    (∫ u, u^2 ∂ternaryErrorKernel a V F hF x) = V ∧
    (∫ u, u^4 ∂ternaryErrorKernel a V F hF x) ≤ B := by
  let hi := ternary_error_integrable a V F hF x
  refine ⟨hi _, hi _, hi _, ternary_error_mean a V F hF x ha (hp x), ?_, ?_⟩ <;>
    rw [ternary_error_integral a V F hF x (hp x)]
  · exact ternary_variance a (F x) V ha
  · exact hb x

end

/-- Global bounds imply the paper's exact order-zero norm bound on any domain. -/
theorem holderNorm_order_zero_of_global_bounds {d : ℕ} (U : Set (Covariate d))
    (F : Covariate d → ℝ) (α M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hsup : ∀ x, |F x| ≤ M)
    (hmod : ∀ x y, |F x - F y| ≤ H * euclideanNorm (x - y) ^ α) :
    holderNorm U F 0 α ≤ ENNReal.ofReal (M + H) := by
  have hs : derivativeSup U F ≤ ENNReal.ofReal M := by
    solve_by_elim [iSup_le, ENNReal.ofReal_le_ofReal]
  have hh : holderSeminorm U F α ≤ ENNReal.ofReal H := by
    apply iSup_le
    intro x
    apply iSup_le
    intro y
    by_cases hxy : (x : Covariate d) = y
    · simp [hxy]
    · simp only [ite_eq_right_iff.mpr (fun h => False.elim (hxy h))]
      apply ENNReal.ofReal_le_ofReal
      exact (div_le_iff₀ (Real.rpow_pos_of_pos
        (euclideanNorm_pos_of_ne_zero (x.val - y.val) (sub_ne_zero.mpr hxy)) α)).mpr
          (hmod x y)
  rw [holderNorm_order_zero, ENNReal.ofReal_add hM hH] <;> gcongr

/-- The genuine original-model parameter with uniform design and ternary errors. -/
def uniformTernaryParameter {d : ℕ} (a V : ℝ) (F : Covariate d → ℝ)
    (hF : Measurable F) (ha : a ≠ 0) (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    RegressionParameter d := {
  density := fun _ => 1
  regression := F
  variance := V
  errors := ternaryErrorKernel a V F hF
  errors_markov := ternaryErrorKernel_markov a V F hF ha hp }

/-- Order-zero legality uses global bounds, so it is independent of the
size or shape of the model's prescribed extension domain. -/
theorem uniformTernaryParameter_admissible_order_zero {d : ℕ} (C : ModelConstants d)
    (a V : ℝ) (F : Covariate d → ℝ) (hF : Continuous F) (horder : C.order = 0)
    (ha : a ≠ 0) (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    (hVlo : C.varianceLower ≤ V) (hVhi : V ≤ C.varianceUpper)
    (M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H) (hbudget : M + H ≤ C.holderBound)
    (hsup : ∀ x, |F x| ≤ M)
    (hmod : ∀ x y, |F x - F y| ≤ H * euclideanNorm (x - y) ^ C.smoothness)
    (hfourth : ∀ x, ternaryExpectation a (F x) V (fun y => (y-F x)^4) ≤ C.fourthBound) :
    Admissible C (uniformTernaryParameter a V F hF.measurable ha hp) := by
  refine ⟨measurable_const, hF.measurable, ?_, ?_, ?_, hVlo, hVhi, ?_⟩
  · exact Filter.Eventually.of_forall (fun _ =>
      ⟨C.densityLower_lt_one.le, C.one_lt_densityUpper.le⟩)
  · simp only [uniformTernaryParameter, ENNReal.ofReal_one, lintegral_const, one_mul]
    exact cubeVolume_univ d
  · refine ⟨F, fun _ _ => rfl, ?_, ?_⟩
    · simpa [horder] using
        (contDiffOn_zero.mpr hF.continuousOn : ContDiffOn ℝ 0 F C.domain)
    · have hα : C.alpha = C.smoothness := by simp [ModelConstants.alpha, horder]
      rw [horder, hα]
      exact (holderNorm_order_zero_of_global_bounds C.domain F C.smoothness M H hM hH
        hsup hmod).trans (ENNReal.ofReal_le_ofReal hbudget)
  · exact .of_forall (ternary_error_moments a V F hF.measurable ha hp hfourth)

/-- Uniform interior margins for nonzero regression fields and the variance path. -/
structure LowSmoothnessTernaryConstants {d : ℕ} (C : ModelConstants d) where
  a : ℝ
  v : ℝ
  ρ : ℝ
  c : ℝ
  a_pos : 0 < a
  ρ_pos : 0 < ρ
  c_pos : 0 < c
  legal : ∀ f V, |f| ≤ ρ → |V - v| ≤ ρ →
    C.varianceLower < V ∧ V < C.varianceUpper ∧
      (∀ y, c ≤ ternaryMass a f V y) ∧
      ternaryExpectation a f V (fun y => (y - f) ^ 4) ≤ C.fourthBound

theorem lowSmoothnessTernaryConstants_exists {d : ℕ} (C : ModelConstants d) :
    Nonempty (LowSmoothnessTernaryConstants C) := by
  obtain ⟨P⟩ := parametricTernaryConstants_exists C
  let v := (P.l + P.r) / 2
  have hv : 0 < v := by dsimp [v]; linarith [P.l_pos, P.interval]
  have hVl : C.varianceLower < v := by dsimp [v]; linarith [P.lower_le, P.interval]
  have hVr : v < C.varianceUpper := by dsimp [v]; linarith [P.upper_le, P.interval]
  have hva : v < P.a ^ 2 := by dsimp [v]; linarith [P.variance_lt_square, P.interval]
  have hfourth : P.a ^ 2 * v < C.fourthBound := by
    have hmid : v < P.r := by dsimp [v]; linarith [P.interval]
    exact (mul_lt_mul_of_pos_left hmid (sq_pos_of_pos P.a_pos)).trans_le P.fourth_le
  obtain ⟨ρ, c, hρ, hc, hlegal⟩ := ternary_admissible_neighborhood P.a v
    C.varianceLower C.varianceUpper C.fourthBound P.a_pos hv hva hVl hVr hfourth
  exact ⟨⟨P.a, v, ρ, c, P.a_pos, hρ, hc, hlegal⟩⟩

namespace LowSmoothnessTernaryConstants

variable {d : ℕ} {C : ModelConstants d} (P : LowSmoothnessTernaryConstants C)

def variancePath (η t : ℝ) : ℝ := P.v - η ^ 2 * t

theorem variance_path_distance (η t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    |P.variancePath η t - P.v| ≤ η ^ 2 := by
  simp only [variancePath, sub_sub_cancel_left, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg η),
    abs_of_nonneg ht.1]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left ht.2 (sq_nonneg η)

theorem path_legality (η t f : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hη : η ^ 2 ≤ P.ρ) (hf : |f| ≤ P.ρ) :
    C.varianceLower < P.variancePath η t ∧ P.variancePath η t < C.varianceUpper ∧
      (∀ y, P.c ≤ ternaryMass P.a f (P.variancePath η t) y) ∧
      ternaryExpectation P.a f (P.variancePath η t) (fun y => (y - f) ^ 4) ≤ C.fourthBound :=
  P.legal f (P.variancePath η t) hf ((P.variance_path_distance η t ht).trans hη)

/-- A canonical actual-model parameter along the variance path. -/
def pathParameter (F : Covariate d → ℝ) (hF : Continuous F) (η t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (hη : η ^ 2 ≤ P.ρ) (hf : ∀ x, |F x| ≤ P.ρ) :
    RegressionParameter d :=
  uniformTernaryParameter P.a (P.variancePath η t) F hF.measurable P.a_pos.ne'
    (fun x y => P.c_pos.le.trans ((P.path_legality η t (F x) ht hη (hf x)).2.2.1 y))

theorem pathParameter_admissible_order_zero (F : Covariate d → ℝ) (hF : Continuous F)
    (η t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (hη : η ^ 2 ≤ P.ρ) (hf : ∀ x, |F x| ≤ P.ρ)
    (horder : C.order = 0) (M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hbudget : M + H ≤ C.holderBound) (hsup : ∀ x, |F x| ≤ M)
    (hmod : ∀ x y, |F x - F y| ≤ H * euclideanNorm (x - y) ^ C.smoothness) :
    Admissible C (P.pathParameter F hF η t ht hη hf) := by
  have hlegal (x : Covariate d) := P.path_legality η t (F x) ht hη (hf x)
  apply uniformTernaryParameter_admissible_order_zero C P.a (P.variancePath η t) F hF horder P.a_pos.ne'
    _ (hlegal 0).1.le (hlegal 0).2.1.le M H hM hH hbudget hsup hmod fun x => (hlegal x).2.2.2

end LowSmoothnessTernaryConstants

end NearlyMinimax
