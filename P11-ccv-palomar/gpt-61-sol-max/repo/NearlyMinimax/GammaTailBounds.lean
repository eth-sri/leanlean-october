module

public import NearlyMinimax.GaussianSpatialDomination

@[expose] public section

/-! Genuine Gamma moments and polynomial-exponential tail integrals. These
are the analytic ingredients for the log-scale simplex tail in the spatial
interpolation construction. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

section
variable {b : ℝ} (hb : 0 < b)
include hb

/-- The actual Gamma moment, with respect to Lebesgue measure on the positive
half-line. -/
theorem gamma_monomial_integrable  r :
    IntegrableOn (fun v  => v ^ r * Real.exp (-(b * v))) (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (r : ℝ)) (p := 1)
    (b := b) (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg r)) (by norm_num) hb
  simp_all

theorem gamma_monomial_integral  r :
    (∫ v : ℝ in Ici 0, v ^ r * Real.exp (-(b * v))) =
      r.factorial / b ^ (r + 1) := by
  rw [integral_Ici_eq_integral_Ioi]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (r : ℝ) + 1)
    (r := b) (by positivity) hb
  simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  rw [h]
  have he : (r : ℝ) + 1 = ((r + 1 : ℕ) : ℝ) := by norm_num
  rw [he, Real.rpow_natCast]
  rw [div_pow, one_pow]
  field_simp
end


/-- Translation of a genuine set integral; no integrability premise is
needed to identify the two Bochner integrals. -/
theorem integral_Ici_translate A (f : ℝ → ℝ) :
    (∫ v : ℝ in Ici 0, f (A + v)) = ∫ u : ℝ in Ici A, f u := by
  have hp := (measurePreserving_add_left (volume : Measure ℝ) A).restrict_preimage
    (s := Ici A) measurableSet_Ici
  have hs : (fun v : ℝ => A + v) ⁻¹' Ici A = Ici 0 := by
    simp_all
  rw [hs] at hp
  exact hp.integral_comp (MeasurableEquiv.addLeft A).measurableEmbedding f

section
variable {b : ℝ} (hb : 0 < b)
include hb

theorem gamma_translated_monomial_integrable 
    A m :
    IntegrableOn (fun v  => (A + v) ^ m * Real.exp (-(b * v))) (Ici 0) := by
  have he : (fun v : ℝ => (A + v) ^ m * Real.exp (-(b * v))) =
      fun v => ∑ l ∈ Finset.range (m + 1),
        (A ^ l * (m.choose l : ℝ)) * (v ^ (m - l) * Real.exp (-(b * v))) := by
    funext v
    rw [add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he]
  exact integrable_finsetSum _ fun l _ => (gamma_monomial_integrable hb (m - l)).const_mul _

/-- Exact exponential tail of an integer-shape Gamma density. The right-hand
side is a finite polynomial, derived by translation and the binomial theorem. -/
theorem gamma_polynomial_tail_integral  A m :
    (∫ u : ℝ in Ici A, u ^ m * Real.exp (-(b * u)) / m.factorial) =
      Real.exp (-(b * A)) *
        ∑ l ∈ Finset.range (m + 1), A ^ l / (l.factorial * b ^ (m + 1 - l)) := by
  rw [← integral_Ici_translate A]
  have he : (fun v : ℝ => (A + v) ^ m * Real.exp (-(b * (A + v))) / (m.factorial : ℝ)) =
      fun v => (Real.exp (-(b * A)) / (m.factorial : ℝ)) *
        ∑ l ∈ Finset.range (m + 1),
          (A ^ l * (m.choose l : ℝ)) * (v ^ (m - l) * Real.exp (-(b * v))) := by
    funext v
    rw [show -(b * (A + v)) = -(b * A) + -(b * v) by ring, Real.exp_add,
      add_pow, Finset.sum_mul, Finset.sum_div]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he, integral_const_mul, integral_finsetSum _ (fun l _ =>
    (gamma_monomial_integrable hb (m - l)).const_mul _)]
  simp_rw [integral_const_mul, gamma_monomial_integral hb]
  rw [div_mul_eq_mul_div, div_eq_mul_inv, mul_assoc]
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l hl
  have hlm  := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
  have hf : (m.factorial : ℝ) ≠ 0 := by positivity
  have hfl : (l.factorial : ℝ) ≠ 0 := by positivity
  have hfr : ((m - l).factorial : ℝ) ≠ 0 := by positivity
  have hp  := ne_of_gt hb
  have hchoose := Nat.cast_choose ℝ hlm
  grind

/-- The original tail integrand is genuinely integrable, including at an
arbitrary translated boundary. -/
theorem gamma_polynomial_tail_integrable  A m :
    IntegrableOn (fun u  => u ^ m * Real.exp (-(b * u)) / m.factorial)
      (Ici A) := by
  have hp := (measurePreserving_add_left (volume : Measure ℝ) A).restrict_preimage
    (s := Ici A) measurableSet_Ici
  have hs : (fun v : ℝ => A + v) ⁻¹' Ici A = Ici 0 := by
    simp_all
  rw [hs] at hp
  apply (hp.integrable_comp_emb (MeasurableEquiv.addLeft A).measurableEmbedding).mp
  have h := (gamma_translated_monomial_integrable hb A m).const_mul
    (Real.exp (-(b * A)) / (m.factorial : ℝ))
  convert h using 1
  funext v
  simp only [Function.comp_apply]
  rw [show -(b * (A + v)) = -(b * A) + -(b * v) by ring, Real.exp_add]
  ring
end


end NearlyMinimax
