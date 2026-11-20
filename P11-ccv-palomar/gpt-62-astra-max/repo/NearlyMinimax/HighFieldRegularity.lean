module

public import NearlyMinimax.HighSmoothnessWindows
public import NearlyMinimax.CoordinatePartialBridge
public import NearlyMinimax.HighPriorModel
public import NearlyMinimax.AnchoredGeometry

@[expose] public section

/-! Resolution-independent derivative and Hölder estimates for actual
periodic window fields. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

section
variable {d : ℕ} {F : Covariate d → ℝ} (hF : ContDiff ℝ ∞ F) (γ : Fin d → ℕ) (x : Covariate d)
    {J E : Type*}

theorem finite_sum_norm_le_active_count [Fintype J]
    [NormedAddCommGroup E] {g : J → E} {N : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ j, ‖g j‖ ≤ B)
    (hcount : (Finset.univ.filter (fun j => g j ≠ 0)).card ≤ N) :
    ‖∑ j, g j‖ ≤ (N : ℝ) * B := by
  let A := Finset.univ.filter (fun j => g j ≠ 0)
  have hsum : (∑ j, ‖g j‖) = ∑ j ∈ A, ‖g j‖ := by
    symm
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    aesop
  calc
    _ ≤ _ := norm_sum_le _ _
    _ = _ := hsum
    _ ≤ ∑ _j ∈ A, B := by bound
    _ = A.card * B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) hB

/-- Combining the uniform derivative bound and the next-derivative
Lipschitz bound preserves the fractional exponent, uniformly in resolution. -/
theorem holder_of_scaled_sup_and_lipschitz {k r A α q : ℝ}
    (hk : 0 < k) (hr : 0 ≤ r) (hA : 0 ≤ A) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hsup : q ≤ 2 * A * k ^ (-α))
    (hlip : q ≤ A * k ^ (1 - α) * r) :
    q ≤ 2 * A * r ^ α := by
  by_cases hr0 : r = 0
  · subst r
    simpa only [mul_zero, Real.zero_rpow hα0.ne'] using hlip
  have hrpos  := lt_of_le_of_ne hr (Ne.symm hr0)
  by_cases hkr : k * r ≤ 1
  · have hp  :=
      Real.rpow_le_one (mul_nonneg hk.le hr) hkr (sub_nonneg.mpr hα1)
    have hid : k ^ (1 - α) * r = (k * r) ^ (1 - α) * r ^ α := by
      rw [Real.mul_rpow hk.le hr]
      rw [mul_assoc, ← Real.rpow_add hrpos]
      simp
    have hsmall : A * k ^ (1 - α) * r ≤ A * r ^ α := by
      calc
        _ = A * ((k * r) ^ (1 - α) * r ^ α) := by rw [← hid]; ring
        _ ≤ A * (1 * r ^ α) := by gcongr
        _ = _ := by ring
    have hpositive : 0 ≤ A * r ^ α := by positivity
    bound
  · have hp  := Real.one_le_rpow (le_of_not_ge hkr) hα0.le
    have hkinv : k ^ (-α) ≤ r ^ α := by
      rw [Real.rpow_neg hk.le, ← one_div]
      apply (div_le_iff₀ (Real.rpow_pos_of_pos hk α)).mpr
      simpa only [Real.mul_rpow hk.le hr, one_mul, mul_comm] using hp
    exact hsup.trans (mul_le_mul_of_nonneg_left hkinv (by positivity))

theorem multiIndexBasis_norm (j : Fin (∑ r, γ r)) :
    ‖multiIndexBasis γ j‖ = 1 := by
  simp [multiIndexBasis, wordBasis, Pi.norm_single]

include hF in
theorem multiPartial_norm_le_iterated :
    |multiPartial F γ x| ≤ ‖iteratedFDeriv ℝ (∑ r, γ r) F x‖ := by
  rw [multiPartial_eq_iteratedFDeriv isOpen_univ
    (hF.of_le (by simp)).contDiffOn le_rfl (mem_univ x)]
  have hh := (iteratedFDeriv ℝ (∑ r, γ r) F x).le_opNorm (multiIndexBasis γ)
  simpa only [Real.norm_eq_abs, multiIndexBasis_norm, Finset.prod_const_one, mul_one] using hh

include hF in
theorem multiPartial_diff_norm_le_iterated (y : Covariate d) :
    let eriv := iteratedFDeriv ℝ (∑ r, γ r) F
    |multiPartial F γ x - multiPartial F γ y| ≤
      ‖eriv x - eriv y‖ := by
  intro eriv
  rw [multiPartial_eq_iteratedFDeriv isOpen_univ
    (hF.of_le (by simp)).contDiffOn le_rfl (mem_univ x),
    multiPartial_eq_iteratedFDeriv isOpen_univ
    (hF.of_le (by simp)).contDiffOn le_rfl (mem_univ y)]
  have hh := (eriv x -
    eriv y).le_opNorm (multiIndexBasis γ)
  simpa only [ContinuousMultilinearMap.sub_apply, Real.norm_eq_abs, multiIndexBasis_norm,
    Finset.prod_const_one, mul_one] using hh

end

variable {d : ℕ} {C : ModelConstants d} (U : Set (Covariate d)) {F : Covariate d → ℝ}
    (hF : ContDiff ℝ ∞ F) {k A : ℝ} (hk : 1 ≤ k) (hA : 0 ≤ A)
    (hbound : ∀ q ≤ C.order + 1, ∀ x, ‖iteratedFDeriv ℝ q F x‖ ≤ A * k ^ ((q : ℝ) - C.smoothness))
include hF hk hA hbound

/-- The actual scaled Fréchet bounds imply the manuscript's sorted mixed
partial bounds and top-order Euclidean Hölder modulus. -/
theorem mixed_bounds_of_scaled_derivatives :
    (∀ γ : Fin d → Fin (C.order + 1), (∑ r, (γ r).val) ≤ C.order → ∀ x,
      |multiPartial F (fun r => (γ r).val) x| ≤ A) ∧
    (∀ γ : Fin d → Fin (C.order + 1), (∑ r, (γ r).val) = C.order → ∀ x y,
      |multiPartial F (fun r => (γ r).val) x - multiPartial F (fun r => (γ r).val) y| ≤
        (2 * A) * euclideanNorm (x - y) ^ C.alpha) := by
  have hkpos : 0 < k := by positivity
  constructor
  · intro γ hγ x
    apply (multiPartial_norm_le_iterated hF _ x).trans
    apply (hbound _ (by omega) x).trans
    have hcast : ((∑ r, (γ r).val : ℕ) : ℝ) ≤ C.order := by exact_mod_cast hγ
    have hp : k ^ (((∑ r, (γ r).val : ℕ) : ℝ) - C.smoothness) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hk (by linarith [C.order_lt])
    bound
  · intro γ hγ x y
    have hsup (z : Covariate d) : ‖iteratedFDeriv ℝ C.order F z‖ ≤ A * k ^ (-C.alpha) := by
      have he : C.order - C.smoothness = -C.alpha := by unfold ModelConstants.alpha; ring
      grind
    have hnext (z : Covariate d) : ‖fderiv ℝ (iteratedFDeriv ℝ C.order F) z‖ ≤
        A * k ^ (1 - C.alpha) := by
      rw [norm_fderiv_iteratedFDeriv]
      have he : ((C.order + 1 : ℕ) : ℝ) - C.smoothness = 1 - C.alpha := by
        unfold ModelConstants.alpha
        push_cast
        ring
      grind
    have hlarge : ‖iteratedFDeriv ℝ C.order F x - iteratedFDeriv ℝ C.order F y‖ ≤
        2 * A * k ^ (-C.alpha) := (norm_sub_le _ _).trans (by nlinarith [hsup x, hsup y])
    have hsmall : ‖iteratedFDeriv ℝ C.order F x - iteratedFDeriv ℝ C.order F y‖ ≤
        A * k ^ (1 - C.alpha) * ‖x - y‖ := by
      have hfFinite : ContDiff ℝ (C.order + 1) F := hF.of_le (by simp)
      exact Convex.norm_image_sub_le_of_norm_fderiv_le
        (fun z _hz =>
          hfFinite.contDiffAt.differentiableAt_iteratedFDeriv
            (by exact_mod_cast Nat.lt_succ_self C.order))
        (fun z _ => hnext z) convex_univ (mem_univ y) (mem_univ x)
    have hh := holder_of_scaled_sup_and_lipschitz
      hkpos (norm_nonneg _) hA C.alpha_pos C.alpha_le_one hlarge hsmall
    have heval := multiPartial_diff_norm_le_iterated hF (fun r => (γ r).val) x y
    rw [hγ] at heval
    exact (heval.trans hh).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (by apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr; intro r; exact abs_coordinate_le_euclideanNorm (x - y) r) C.alpha_pos.le)
      (by positivity))

theorem holderNorm_of_scaled_derivatives :
    holderNorm U F C.order C.alpha ≤
      ENNReal.ofReal ((((C.order + 1 : ℕ) : ℝ) ^ d + 2) * A) := by
  obtain ⟨hs, hm⟩ := mixed_bounds_of_scaled_derivatives hF hk hA hbound
  have hh := holderNorm_of_global_mixed_bounds U
    hA (by positivity) (K := (C.order+1)^d) (by
      simpa using Finset.card_filter_le (Finset.univ : Finset (Fin d → Fin (C.order+1))) _) hs hm
  simpa only [Nat.cast_pow, add_mul, mul_add] using hh

end NearlyMinimax
