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
variable {b : ℝ} (hb : 0 < b) (r : ℕ)
include hb

/-- The actual Gamma moment, with respect to Lebesgue measure on the positive
half-line. -/
theorem gamma_monomial_integrable :
    IntegrableOn (fun v : ℝ => v ^ r * Real.exp (-(b * v))) (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (r : ℝ)) (p := 1)
    (b := b) (by linarith) (by norm_num) hb
  simp_all

theorem gamma_monomial_integral :
    (∫ v : ℝ in Ici 0, v ^ r * Real.exp (-(b * v))) =
      (r.factorial : ℝ) / b ^ (r + 1) := by
  rw [integral_Ici_eq_integral_Ioi]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (r : ℝ) + 1)
    (r := b) (by positivity) hb
  simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  rw [h]
  have he : (r : ℝ) + 1 = ((r + 1 : ℕ) : ℝ) := by norm_num
  rw [he, Real.rpow_natCast] <;> ring

end

/-- Translate the linear Laplace tail to the two Gamma moments of order zero and one. -/
theorem gamma_linear_tail {b : ℝ} (hb : 0 < b) (A : ℝ) :
    IntegrableOn (fun u : ℝ => u * Real.exp (-(b * u))) (Ici A) ∧
    (∫ u : ℝ in Ici A, u * Real.exp (-(b * u))) =
      (1 + A*b) * Real.exp (-(A*b)) / b^2 := by
  let e := MeasurableEquiv.addLeft A
  have hp : MeasurePreserving e (volume.restrict (Ici 0)) (volume.restrict (Ici A)) := by
    simpa [e] using (measurePreserving_add_left (volume : Measure ℝ) A).restrict_preimage (s := Ici A) measurableSet_Ici
  let f (r : ℕ) (v : ℝ) := v ^ r * Real.exp (-(b*v))
  have he (v : ℝ) : e v * Real.exp (-(b*e v)) = Real.exp (-(b*A)) * (A*f 0 v + f 1 v) := by
    simp [e, f, mul_add, Real.exp_add] <;> ring
  have h0 := (gamma_monomial_integrable hb 0).const_mul A
  have h1 := gamma_monomial_integrable hb 1
  refine ⟨(hp.integrable_comp_emb e.measurableEmbedding).mp ?_, ?_⟩
  · change Integrable (fun v => e v * Real.exp (-(b*e v))) (volume.restrict (Ici 0))
    simp_rw [he]
    exact (h0.add h1).const_mul _
  · rw [← hp.integral_comp e.measurableEmbedding (fun u => u * Real.exp (-(b*u)))]
    simp_rw [he]
    rw [integral_const_mul, integral_add h0 h1, integral_const_mul]
    change Real.exp (-(b*A)) * (A * (∫ v in Ici 0, f 0 v) + ∫ v in Ici 0, f 1 v) = _
    simp only [f, gamma_monomial_integral hb]
    rw [mul_comm b A]
    norm_num [Nat.factorial, pow_succ]
    field_simp
    ring

end NearlyMinimax
