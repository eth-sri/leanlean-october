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

section
variable {d : ℕ} (P : MvPolynomial (Fin d) ℝ) {m : ℕ} {u : Covariate d} (hu : ‖u‖ ≤ 1) (z : Fin d → ℂ)
    {q : ℕ}

def frameCoefficientL1 : ℝ :=
  ∑ β ∈ P.support, |P.coeff β|

theorem frameCoefficientL1_nonneg :
    0 ≤ frameCoefficientL1 P := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

def frameScaledPolynomial : MvPolynomial (Fin d) ℝ :=
  MvPolynomial.bind₁ (fun r => MvPolynomial.C (1 / 8) * MvPolynomial.X r) P

theorem frameScaledPolynomial_eval (x : Covariate d) :
    MvPolynomial.eval x (frameScaledPolynomial P) = MvPolynomial.eval (fun r => x r / 8) P := by
  change MvPolynomial.eval₂Hom (RingHom.id ℝ) x _ = _
  rw [frameScaledPolynomial, MvPolynomial.eval₂Hom_bind₁]
  simp
  ring

theorem frameScaledPolynomial_complex_eval : MvPolynomial.eval z (complexify (frameScaledPolynomial P)) =
      MvPolynomial.eval₂ Complex.ofRealHom (fun r => z r / 8) P := by
  rw [complexify, MvPolynomial.eval_map]
  change MvPolynomial.eval₂Hom Complex.ofRealHom z _ =
    MvPolynomial.eval₂Hom Complex.ofRealHom _ P
  rw [frameScaledPolynomial, MvPolynomial.eval₂Hom_bind₁]
  simp only [map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
  change MvPolynomial.eval₂Hom Complex.ofRealHom (fun r => (1 / 8 : ℝ) * z r) P = _
  have he : (fun r => (1 / 8 : ℝ) * z r) = (fun r => z r / 8) := by
    funext r
    push_cast
    ring
  rw [he]

theorem frame_complex_eval_norm_le_l1 (hz : ∀ r, ‖z r‖ ≤ 1) :
    ‖MvPolynomial.eval₂ Complex.ofRealHom z P‖ ≤ frameCoefficientL1 P := by
  rw [MvPolynomial.eval₂_eq']
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro β hβ
  rw [norm_mul]
  change ‖(P.coeff β : ℂ)‖ * _ ≤ _
  rw [Complex.norm_real]
  have hp : ‖∏ r, z r ^ β r‖ ≤ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_one₀
    · intro r hr
      positivity
    · intro r hr
      rw [norm_pow]
      bound
  bound

include hu in
theorem frameScaledPolynomial_complex_bound
    (hz : ‖z - (fun r => (u r : ℂ))‖ < 1) :
    ‖MvPolynomial.eval z (complexify (frameScaledPolynomial P))‖ ≤ frameCoefficientL1 P := by
  rw [frameScaledPolynomial_complex_eval]
  apply frame_complex_eval_norm_le_l1
  intro r
  have hcoord : ‖z r - (u r)‖ < 1 := (norm_le_pi_norm
    (z - fun r => (u r : ℂ)) r).trans_lt hz
  have hucoord : ‖(u r : ℂ)‖ ≤ 1 := by
    simpa using (norm_le_pi_norm u r).trans hu
  have hzcoord : ‖z r‖ ≤ 2 := by
    have htri := norm_sub_norm_le (z r) (u r)
    linarith
  norm_num
  bound

theorem frameScaledPolynomial_contDiff :
    ContDiff ℝ ∞ (fun x => MvPolynomial.eval x (frameScaledPolynomial P)) :=
  (RoughRegime.PolynomialDerivatives.polynomial_contDiff _).of_le le_top

include hu in
theorem frameScaledPolynomial_value_bound :
    |MvPolynomial.eval u (frameScaledPolynomial P)| ≤ frameCoefficientL1 P := by
  have hc := frameScaledPolynomial_complex_bound P hu (fun r => (u r)) (by simp)
  rw [complexify, MvPolynomial.eval_map] at hc
  change ‖MvPolynomial.eval₂ Complex.ofRealHom (Complex.ofRealHom ∘ u)
    (frameScaledPolynomial P)‖ ≤ _ at hc
  rw [← MvPolynomial.eval₂_comp] at hc
  simpa using hc

/-- A bound for every derivative through a fixed order, independent of the
polynomial degree and the number of frame coefficients. -/
theorem frameScaledPolynomial_derivatives_bound (hq : q ≤ m) {u : Covariate d} (hu : ‖u‖ ≤ 1) :
    ‖iteratedFDeriv ℝ q (fun x => MvPolynomial.eval x (frameScaledPolynomial P)) u‖ ≤
      frameCoefficientL1 P * m.factorial * (Real.exp 1) ^ m := by
  have hL1 := frameCoefficientL1_nonneg P
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  by_cases hq0 : q = 0
  · subst q
    rw [norm_iteratedFDeriv_zero]
    apply (frameScaledPolynomial_value_bound P hu).trans
    have hmfac : (1 : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_pos m
    have hmexp : 1 ≤ (Real.exp 1) ^ m := one_le_pow₀ he
    have hh : 1 ≤ m.factorial * (Real.exp 1) ^ m := by nlinarith
    nlinarith
  · apply ((by simpa using real_polynomial_derivative_norm_bound (by norm_num) (frameCoefficientL1_nonneg P) (frameScaledPolynomial_complex_bound P hu) (Nat.pos_of_ne_zero hq0) : ‖iteratedFDeriv ℝ q (fun x => (MvPolynomial.eval x) (frameScaledPolynomial P)) u‖ ≤ frameCoefficientL1 P * ↑q.factorial * Real.exp 1 ^ q)).trans
    gcongr

end

section
variable {d : ℕ} (P : MvPolynomial (Fin d) ℝ)

def highFrameProfile (u : Covariate d) : ℝ :=
  highWindowTensor d u * MvPolynomial.eval u (frameScaledPolynomial P)

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
    ∃ K : ℝ, 0 < K ∧ ∀ P, ∀ q ≤ m, ∀ u : Covariate d,
      ‖iteratedFDeriv ℝ q (highFrameProfile P) u‖ ≤ K * frameCoefficientL1 P := by
  obtain ⟨B, hB0, hB⟩ := (highWindowTensor_hasCompactSupport d).exists_bound_iteratedFDeriv (highWindowTensor_contDiff d) m
  let B' := max B 1
  let Cp := m.factorial * (Real.exp 1) ^ m
  refine ⟨(2 ^ m * B' * Cp), (by positivity), ?_⟩
  intro P q hq u
  have hL1 := frameCoefficientL1_nonneg P
  by_cases hu : u ∈ tsupport (highWindowTensor d)
  · have hunorm : ‖u‖ ≤ 1 := by
      apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
      intro r
      exact (highWindowTensor_tsupport_bound hu r).trans (by norm_num)
    have hder := norm_iteratedFDeriv_mul_le (highWindowTensor_contDiff d)
      (frameScaledPolynomial_contDiff P) u (n := q) (by simp)
    calc
      _ ≤ _ := hder
      _ ≤ ∑ j ∈ Finset.range (q + 1), (q.choose j) * B' *
          (frameCoefficientL1 P * Cp) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjq : j ≤ q := by simpa using (Finset.mem_range.mp hj)
        gcongr
        · exact (hB j (hjq.trans hq) u).trans (le_max_left _ _)
        · simpa only [ mul_assoc] using
            frameScaledPolynomial_derivatives_bound P ((Nat.sub_le _ _).trans hq) hunorm
      _ = _ := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
      _ ≤ 2 ^ m * B' * (frameCoefficientL1 P * Cp) := by
        gcongr
        norm_num
      _ = _ := by ring
  · have hzero : iteratedFDeriv ℝ q (highFrameProfile P) u = 0 := by
      by_contra hn
      exact hu (highFrameProfile_tsupport_subset P
        ((support_iteratedFDeriv_subset q) (show u ∈ Function.support (iteratedFDeriv ℝ q (highFrameProfile P)) from hn)))
    rw [hzero, norm_zero]
    positivity

end NearlyMinimax
