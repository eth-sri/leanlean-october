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

section
variable {α : Type*} [MeasurableSpace α] (a V : ℝ) {F : α → ℝ} (hF : Measurable F)

theorem ternaryMass_measurable_comp (F : α → ℝ) (hF : Measurable F) (y : Fin 3) :
    Measurable (fun x => ternaryMass a (F x) V y) := by
  fun_prop

/-- The errors have actual values `-a-f(x)`, `-f(x)`, and `a-f(x)`. -/
def ternaryErrorKernel : Kernel α ℝ where
  toFun x := ∑ y, ENNReal.ofReal (ternaryMass a (F x) V y) •
    Measure.dirac (ternaryValue a y - F x)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hs]
    apply Finset.measurable_sum
    intro y _
    exact (ENNReal.measurable_ofReal.comp (ternaryMass_measurable_comp a V F hF y)).mul
      (measurable_const.indicator ((measurable_const.sub hF) hs))

theorem ternaryErrorKernel_apply (F : α → ℝ) (hF : Measurable F) (x : α) :
    ternaryErrorKernel a V hF x = ∑ y,
      ENNReal.ofReal (ternaryMass a (F x) V y) •
        Measure.dirac (ternaryValue a y - F x) := rfl

theorem ternaryErrorKernel_markov
    {a V : ℝ} {F : α → ℝ} (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    IsMarkovKernel (ternaryErrorKernel a V hF) := by
  constructor
  intro x
  constructor
  simp [ternaryErrorKernel_apply, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => hp x y), ternary_normalized (F x) V ha]
  simp

theorem ternary_error_integrable (x : α) (G : ℝ → ℝ) :
    Integrable G (ternaryErrorKernel a V hF x) := by
  rw [ternaryErrorKernel_apply]
  apply integrable_finsetSum_measure.mpr
  intro y _
  exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

end

section
variable {α : Type*} [MeasurableSpace α] {a V : ℝ} {F : α → ℝ} (hF : Measurable F) {x : α} (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a (F x) V y)
include hp

theorem ternary_error_integral (G : ℝ → ℝ) :
    (∫ u, G u ∂ternaryErrorKernel a V hF x) =
      ∑ y, ternaryMass a (F x) V y * G (ternaryValue a y - F x) := by
  rw [ternaryErrorKernel_apply, integral_finsetSum_measure]
  · simp [integral_smul_measure, integral_dirac, smul_eq_mul,
      ENNReal.toReal_ofReal (hp _)]
  · intro y _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

include ha in
theorem ternary_error_mean :
    (∫ u, u ∂ternaryErrorKernel a V hF x) = 0 := by
  rw [ternary_error_integral hF hp]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hm := ternary_mean a (F x) V ha
  change (∑ y, ternaryMass a (F x) V y * ternaryValue a y) = _ at hm
  rw [hm, ternary_normalized (F x) V ha]
  ring

include ha in
theorem ternary_error_variance :
    (∫ u, u ^ 2 ∂ternaryErrorKernel a V hF x) = V := by
  rw [ternary_error_integral hF hp]
  solve_by_elim [ternary_variance]

include ha in
theorem ternary_error_fourth :
    (∫ u, u ^ 4 ∂ternaryErrorKernel a V hF x) =
      a ^ 2 * V + (6 * V - 3 * a ^ 2) * (F x) ^ 2 + 3 * (F x) ^ 4 := by
  rw [ternary_error_integral hF hp]
  solve_by_elim [ternary_fourth_central_moment]

end

section
variable {d : ℕ} (U : Set (Covariate d)) (density : Covariate d → ℝ) {C : ModelConstants d} {a V : ℝ}
    {F : Covariate d → ℝ} (hF : Measurable F) (ha : a ≠ 0) (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y)

/-- Pointwise mixed-derivative and Euclidean modulus bounds imply the
original sum-over-distinct-multi-indices norm on any extension domain. -/
theorem holderNorm_of_global_mixed_bounds {ℓ : ℕ} {α B L : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L)
    {K : ℕ} (hK : (Finset.univ.filter (fun γ : Fin d → Fin (ℓ + 1) => (∑ i, (γ i).val) ≤ ℓ)).card ≤ K)
    (hsup : ∀ γ : Fin d → Fin (ℓ + 1), (∑ i, (γ i).val) ≤ ℓ →
      ∀ x, |multiPartial F (fun i => (γ i).val) x| ≤ B)
    (hmod : ∀ γ : Fin d → Fin (ℓ + 1), (∑ i, (γ i).val) = ℓ → ∀ x y,
      |multiPartial F (fun i => (γ i).val) x - multiPartial F (fun i => (γ i).val) y| ≤
        L * euclideanNorm (x - y) ^ α) :
    holderNorm U F ℓ α ≤ ENNReal.ofReal ((K : ℝ) * B + L) := by
  have hs (γ : Fin d → Fin (ℓ + 1)) (hγ : (∑ i, (γ i).val) ≤ ℓ) :
      derivativeSup U (multiPartial F (fun i => (γ i).val)) ≤ ENNReal.ofReal B := by
    apply iSup_le
    solve_by_elim [ENNReal.ofReal_le_ofReal]
  have hh (γ : Fin d → Fin (ℓ + 1)) (hγ : (∑ i, (γ i).val) = ℓ) :
      holderSeminorm U (multiPartial F (fun i => (γ i).val)) α ≤ ENNReal.ofReal L := by
    apply iSup_le
    intro x
    apply iSup_le
    intro y
    by_cases hxy : (x : Covariate d) = y
    · simp [hxy]
    · simp [ite_eq_right_iff.mpr (False.elim ∘ hxy)]
      apply ENNReal.ofReal_le_ofReal
      apply (div_le_iff₀ (Real.rpow_pos_of_pos
        (euclideanNorm_pos_of_ne_zero (sub_ne_zero.mpr hxy)) α)).mpr
      bound
  let A := Finset.univ.filter (fun γ : Fin d → Fin (ℓ + 1) => (∑ i, (γ i).val) ≤ ℓ)
  have hsum : (∑ γ : Fin d → Fin (ℓ + 1),
      if (∑ i, (γ i).val) ≤ ℓ then
        derivativeSup U (multiPartial F (fun i => (γ i).val)) else 0) ≤
      ENNReal.ofReal ((K : ℝ) * B) := by
    calc
      _ = ∑ γ ∈ A, derivativeSup U (multiPartial F (fun i => (γ i).val)) := by
        rw [Finset.sum_filter]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro γ hγ
        exact hs γ (Finset.mem_filter.mp hγ).2
      _ = ENNReal.ofReal (A.card * B) := by
        simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (by exact_mod_cast hK) hB)
  have hsem : (⨆ γ : Fin d → Fin (ℓ + 1), if (∑ i, (γ i).val) = ℓ then
      holderSeminorm U (multiPartial F (fun i => (γ i).val)) α else 0) ≤ ENNReal.ofReal L := by
    apply iSup_le
    intro γ
    bound
  rw [ENNReal.ofReal_add (by positivity) hL]
  exact add_le_add hsum hsem

theorem holderNorm_order_zero_of_global_bounds {α M H : ℝ} (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hsup : ∀ x, |F x| ≤ M)
    (hmod : ∀ x y, |F x - F y| ≤ H * euclideanNorm (x - y) ^ α) :
    holderNorm U F 0 α ≤ ENNReal.ofReal (M + H) := by
  have hzero (γ : Fin d → Fin (0+1)) : (fun i => (γ i).val) = fun _ => 0 :=
    funext fun i => Fin.val_eq_zero _
  simpa using holderNorm_of_global_mixed_bounds U (ℓ := 0) hM hH (K := 1) (by
    simpa using Finset.card_filter_le (Finset.univ : Finset (Fin d → Fin 1)) _)
    (fun γ _ x => by simpa only [hzero, multiPartial_zero_index] using hsup x)
    (fun γ _ x y => by simpa only [hzero, multiPartial_zero_index] using hmod x y)

/-- A ternary regression experiment with the specified design density. -/
def ternaryParameter :
    RegressionParameter d := {
  density := density
  regression := F
  variance := V
  errors := ternaryErrorKernel a V hF
  errors_markov := ternaryErrorKernel_markov hF ha hp }

abbrev uniformTernaryParameter :
    RegressionParameter d := ternaryParameter (fun _ => 1) hF ha hp

/-- Order-zero legality uses global bounds, so it is independent of the
size or shape of the model's prescribed extension domain. -/
theorem uniformTernaryParameter_admissible_order_zero (hF : Continuous F) (horder : C.order = 0)
    (ha : a ≠ 0) (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    (hVlo : C.varianceLower ≤ V) (hVhi : V ≤ C.varianceUpper)
    {M H : ℝ} (hM : 0 ≤ M) (hH : 0 ≤ H) (hbudget : M + H ≤ C.holderBound)
    (hsup : ∀ x, |F x| ≤ M)
    (hmod : ∀ x y, |F x - F y| ≤ H * euclideanNorm (x - y) ^ C.smoothness)
    (hfourth : ∀ x, a ^ 2 * V + (6 * V - 3 * a ^ 2) * (F x) ^ 2 +
      3 * (F x) ^ 4 ≤ C.fourthBound) :
    Admissible C (uniformTernaryParameter hF.measurable ha hp) := by
  refine ⟨measurable_const, hF.measurable, ?_, ?_, ?_, hVlo, hVhi, ?_⟩
  · exact Filter.Eventually.of_forall (fun _ =>
      ⟨C.densityLower_lt_one.le, C.one_lt_densityUpper.le⟩)
  · simp [uniformTernaryParameter, ternaryParameter]
    exact cubeVolume_univ d
  · refine ⟨F, fun _ _ => rfl, ?_, ?_⟩
    · simpa [horder] using
        (contDiffOn_zero.mpr hF.continuousOn : ContDiffOn ℝ 0 F C.domain)
    · have hα : C.alpha = C.smoothness := by simp [ModelConstants.alpha, horder]
      rw [horder, hα]
      exact (holderNorm_order_zero_of_global_bounds C.domain hM hH
        hsup hmod).trans (ENNReal.ofReal_le_ofReal hbudget)
  · apply Filter.Eventually.of_forall
    intro x
    refine ⟨ternary_error_integrable a V hF.measurable x _,
      ternary_error_integrable a V hF.measurable x _,
      ternary_error_integrable a V hF.measurable x _,
      ternary_error_mean hF.measurable ha (hp x),
      ternary_error_variance hF.measurable ha (hp x), ?_⟩
    exact (ternary_error_fourth hF.measurable ha (hp x)).trans_le (hfourth x)

end

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
  obtain ⟨ρ, c, hρ, hc, hlegal⟩ := ternary_admissible_neighborhood P.a_pos hv hva hVl hVr hfourth
  exact ⟨⟨P.a, v, ρ, c, P.a_pos, hρ, hc, hlegal⟩⟩

namespace LowSmoothnessTernaryConstants

variable {d : ℕ} {C : ModelConstants d} (P : LowSmoothnessTernaryConstants C)

variable (F : Covariate d → ℝ) (hF : Continuous F) (η t f : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hη : η ^ 2 ≤ P.ρ) (hf : ∀ x, |F x| ≤ P.ρ)

def variancePath : ℝ := P.v - η ^ 2 * t

include ht hη in
theorem path_legality (hf : |f| ≤ P.ρ) :
    C.varianceLower < P.variancePath η t ∧ P.variancePath η t < C.varianceUpper ∧
      (∀ y, P.c ≤ ternaryMass P.a f (P.variancePath η t) y) ∧
      ternaryExpectation P.a f (P.variancePath η t) (fun y => (y - f) ^ 4) ≤ C.fourthBound :=
  P.legal f (P.variancePath η t) hf (((by simp only [variancePath, sub_sub_cancel_left, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg η), abs_of_nonneg ht.1]; simpa using mul_le_mul_of_nonneg_left ht.2 (sq_nonneg η) : |P.variancePath η t - P.v| ≤ η ^ 2)).trans hη)

/-- A canonical actual-model parameter along the variance path. -/
def pathParameter :
    RegressionParameter d :=
  uniformTernaryParameter hF.measurable P.a_pos.ne'
    (fun x y => P.c_pos.le.trans ((P.path_legality η t (F x) ht hη (hf x)).2.2.1 y))

theorem pathParameter_admissible_order_zero
    (horder : C.order = 0) (M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hbudget : M + H ≤ C.holderBound) (hsup : ∀ x, |F x| ≤ M)
    (hmod : ∀ x y, |F x - F y| ≤ H * euclideanNorm (x - y) ^ C.smoothness) :
    Admissible C (P.pathParameter F hF η t ht hη hf) := by
  have hlegal (x : Covariate d) := P.path_legality η t (F x) ht hη (hf x)
  apply uniformTernaryParameter_admissible_order_zero hF horder P.a_pos.ne'
    (fun x y => P.c_pos.le.trans ((hlegal x).2.2.1 y)) (hlegal 0).1.le (hlegal 0).2.1.le hM hH hbudget hsup hmod
  intro x
  have hf4 := (hlegal x).2.2.2
  rw [ternary_fourth_central_moment P.a (F x) (P.variancePath η t) P.a_pos.ne'] at hf4
  exact hf4

end LowSmoothnessTernaryConstants

end NearlyMinimax
