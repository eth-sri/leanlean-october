module

public import NearlyMinimax.HighSmoothnessWindows
public import NearlyMinimax.HighFieldRegularity
public import RoughRegime.ComplexDerivativeBridge

@[expose] public section

/-! Degree-independent bounds for the manuscript's polynomial chart frame.
The factor 1/8 provides a fixed complex neighborhood at every real chart point. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace NearlyMinimax
open RoughRegime.ComplexDerivativeBridge
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def frameCoefficientL1 {d : ℕ} (P : MvPolynomial (Fin d) ℝ) : ℝ :=
  ∑ β ∈ P.support, |P.coeff β|

theorem frameCoefficientL1_nonneg {d : ℕ} (P : MvPolynomial (Fin d) ℝ) :
    0 ≤ frameCoefficientL1 P := by apply Finset.sum_nonneg <;> simp_all

def frameScaledPolynomial {d : ℕ} (P : MvPolynomial (Fin d) ℝ) : MvPolynomial (Fin d) ℝ :=
  MvPolynomial.bind₁ (fun r => MvPolynomial.C (1 / 8 : ℝ) * MvPolynomial.X r) P

section
variable {d : ℕ} (P : MvPolynomial (Fin d) ℝ)

theorem frameScaledPolynomial_eval (x : Covariate d) :
    MvPolynomial.eval x (frameScaledPolynomial P) = MvPolynomial.eval (fun r => x r / 8) P := by
  change MvPolynomial.eval₂Hom (RingHom.id ℝ) x _ = MvPolynomial.eval₂Hom (RingHom.id ℝ) _ P
  rw [frameScaledPolynomial, MvPolynomial.eval₂Hom_bind₁]
  simp only [map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', RingHom.id_apply]
  ring

section
variable (z : Fin d → ℂ)

theorem frameScaledPolynomial_complex_eval : MvPolynomial.eval z (complexify (frameScaledPolynomial P)) =
      MvPolynomial.eval₂ Complex.ofRealHom (fun r => z r / 8) P := by
  rw [complexify, MvPolynomial.eval_map]
  change MvPolynomial.eval₂Hom Complex.ofRealHom z _ =
    MvPolynomial.eval₂Hom Complex.ofRealHom _ P
  rw [frameScaledPolynomial, MvPolynomial.eval₂Hom_bind₁]
  simp only [map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
  simp_all <;> field_simp <;> ring

theorem frame_complex_eval_norm_le_l1 (hz : ∀ r, ‖z r‖ ≤ 1) :
    ‖MvPolynomial.eval₂ Complex.ofRealHom z P‖ ≤ frameCoefficientL1 P := by
  rw [MvPolynomial.eval₂_eq']
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro β hβ
  rw [norm_mul]
  change ‖(P.coeff β : ℂ)‖ * ‖∏ r, z r ^ β r‖ ≤ |P.coeff β|
  rw [Complex.norm_real]
  have hp : ‖∏ r, z r ^ β r‖ ≤ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_one₀
    · solve_by_elim [norm_nonneg]
    · intro r hr
      simpa using pow_le_one₀ (norm_nonneg _) (hz r)
  exact (mul_le_mul_of_nonneg_left hp (abs_nonneg _)).trans_eq (mul_one _)

end

section
variable (u : Covariate d) (hu : ‖u‖ ≤ 1)
include hu

theorem frameScaledPolynomial_complex_bound (z : Fin d → ℂ)
    (hz : ‖z - (fun r => (u r : ℂ))‖ < 1) :
    ‖MvPolynomial.eval z (complexify (frameScaledPolynomial P))‖ ≤ frameCoefficientL1 P := by
  rw [frameScaledPolynomial_complex_eval]
  apply frame_complex_eval_norm_le_l1
  intro r
  have hcoord : ‖z r - (u r : ℂ)‖ < 1 := (norm_le_pi_norm
    (z - fun r => (u r : ℂ)) r).trans_lt hz
  have hucoord : ‖(u r : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real] using (norm_le_pi_norm u r).trans hu
  have hzcoord : ‖z r‖ ≤ 2 := by
    have htri := norm_sub_norm_le (z r) (u r : ℂ)
    linarith
  simpa using (div_le_one (by norm_num : (0 : ℝ) < 8)).mpr (by linarith)

theorem frameScaledPolynomial_derivative_bound (q : ℕ) :
    ‖iteratedFDeriv ℝ q (fun x => MvPolynomial.eval x (frameScaledPolynomial P)) u‖ ≤
      frameCoefficientL1 P * (q.factorial : ℝ) * (Real.exp 1) ^ q := by
  simpa only [div_one] using real_polynomial_derivative_norm_bound
    (frameScaledPolynomial P) u 1 (frameCoefficientL1 P) (by norm_num)
    (frameCoefficientL1_nonneg P) (frameScaledPolynomial_complex_bound P u hu)

end

theorem frameScaledPolynomial_contDiff :
    ContDiff ℝ ∞ (fun x => MvPolynomial.eval x (frameScaledPolynomial P)) :=
  (RoughRegime.PolynomialDerivatives.polynomial_contDiff _).of_le le_top

/-- A bound for every derivative through a fixed order, independent of the
polynomial degree and the number of frame coefficients. -/
theorem frameScaledPolynomial_derivatives_bound
    (m q : ℕ) (hq : q ≤ m) (u : Covariate d) (hu : ‖u‖ ≤ 1) :
    ‖iteratedFDeriv ℝ q (fun x => MvPolynomial.eval x (frameScaledPolynomial P)) u‖ ≤
      frameCoefficientL1 P * (m.factorial : ℝ) * (Real.exp 1) ^ m := by
  have hL1 := frameCoefficientL1_nonneg P
  have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  have hp := pow_le_pow_right₀ he hq
  apply (frameScaledPolynomial_derivative_bound P u hu q).trans
  gcongr

end

def highFrameProfile {d : ℕ} (P : MvPolynomial (Fin d) ℝ) (u : Covariate d) : ℝ :=
  highWindowTensor d u * MvPolynomial.eval u (frameScaledPolynomial P)

section
variable {d : ℕ} (P : MvPolynomial (Fin d) ℝ)

theorem highFrameProfile_contDiff :
    ContDiff ℝ ∞ (highFrameProfile P) :=
  (highWindowTensor_contDiff d).mul (frameScaledPolynomial_contDiff P)

theorem highFrameProfile_tsupport_subset :
    tsupport (highFrameProfile P) ⊆ tsupport (highWindowTensor d) :=
  tsupport_mul_subset_left

end

/-- Fixed-order compact frame derivative bounds are uniform over all
polynomial degrees; only the coefficient ℓ¹ norm occurs. -/
theorem highFrameProfile_derivative_bound (d m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ P : MvPolynomial (Fin d) ℝ, ∀ q ≤ m, ∀ u : Covariate d,
      ‖iteratedFDeriv ℝ q (highFrameProfile P) u‖ ≤ K * frameCoefficientL1 P := by
  obtain ⟨B, hB0, hB⟩ := highWindowTensor_derivative_bound d m
  let B' := max B 1
  let Cp := (m.factorial : ℝ) * (Real.exp 1) ^ m
  let K := (2 : ℝ) ^ m * B' * Cp
  have hK : 0 < K := by positivity
  refine ⟨K, hK, ?_⟩
  intro P q hq u
  have hL1 := frameCoefficientL1_nonneg P
  by_cases hu : u ∈ tsupport (highWindowTensor d)
  · have hunorm : ‖u‖ ≤ 1 := by
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
      intro r
      exact (highWindowTensor_tsupport_bound hu r).trans (by norm_num)
    have hder := norm_iteratedFDeriv_mul_le (highWindowTensor_contDiff d)
      (frameScaledPolynomial_contDiff P) u (n := q) (by simp)
    change ‖iteratedFDeriv ℝ q (highFrameProfile P) u‖ ≤ _ at hder
    calc
      _ ≤ _ := hder
      _ ≤ ∑ j ∈ Finset.range (q + 1), (q.choose j : ℝ) * B' *
          (frameCoefficientL1 P * Cp) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjq : j ≤ q := by simpa using (Finset.mem_range.mp hj)
        have hjm := hjq.trans hq
        have hpm : q - j ≤ m := (Nat.sub_le _ _).trans hq
        gcongr
        · exact (hB j hjm u).trans (le_max_left _ _)
        · simpa only [Cp, mul_assoc] using
            frameScaledPolynomial_derivatives_bound P m (q - j) hpm u hunorm
      _ = (2 : ℝ) ^ q * B' * (frameCoefficientL1 P * Cp) := by
        simp [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
      _ ≤ (2 : ℝ) ^ m * B' * (frameCoefficientL1 P * Cp) := by
        gcongr
        norm_num
      _ = K * frameCoefficientL1 P := by ring
  · have hzero : iteratedFDeriv ℝ q (highFrameProfile P) u = 0 := by
      by_contra hn
      have hsub : Function.support (iteratedFDeriv ℝ q (highFrameProfile P)) ⊆
          tsupport (highFrameProfile P) := support_iteratedFDeriv_subset (𝕜 := ℝ) q
      exact hu (highFrameProfile_tsupport_subset P
        (hsub (show u ∈ Function.support (iteratedFDeriv ℝ q (highFrameProfile P)) from hn)))
    simp_all [norm_zero]

end NearlyMinimax
