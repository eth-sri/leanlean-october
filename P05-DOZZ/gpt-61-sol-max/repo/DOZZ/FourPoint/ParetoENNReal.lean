/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.ParetoProductIncrement
public import DOZZ.GMC.RealMoment
import Mathlib.Tactic

/-! The signed Pareto estimate with extended-real moment inputs. -/
public section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
namespace DOZZ.Proofs

/-- One conversion of moments handles both fusion kernels and both full and cut reflection
masses. In particular the reflection mass need not be strictly positive. -/
theorem ennreal_pareto_product_increment_error
    {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (R : Measure Λ) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (p a : ℝ) (hp : 0 < p) (ha : 0 < a) (ha1 : a < 1)
    (A : Ω → ℝ≥0∞) (b : Ω → ℝ) (S : Λ → ℝ≥0∞)
    (hA : ∀ᵐ ω ∂P, 0 < (A ω).toReal) (hb : ∀ ω, 0 < b ω)
    (hAm : AEMeasurable A P) (hbm : AEMeasurable b P) (hSm : AEMeasurable S R)
    (hF0 : (∫⁻ ω, ENNReal.ofReal ((b ω)^a)*A ω ^(-(p+a)) ∂P) < ⊤)
    (hF1 : (∫⁻ ω, ENNReal.ofReal (b ω)*A ω ^(-(p+1)) ∂P) < ⊤)
    (hSa : (∫⁻ v, S v ^a ∂R) < ⊤) (hS1 : (∫⁻ v, S v ∂R) < ⊤) :
    let E := fun v : Ω × Λ => ∫ w,
      (((A v.1).toReal+b v.1*(S v.2).toReal*w)^(-p)-(A v.1).toReal ^(-p))
        ∂paretoMeasure 1 a
    Integrable E (P.prod R) ∧
      |(∫ v, E v ∂P.prod R)-(a*Real.Gamma (-a)*Real.Gamma (p+a)/Real.Gamma p)*
        (∫⁻ ω, ENNReal.ofReal ((b ω)^a)*A ω ^(-(p+a)) ∂P).toReal*
        (∫⁻ v, S v ^a ∂R).toReal| ≤
      (a*p/(1-a))*(∫⁻ ω, ENNReal.ofReal (b ω)*A ω ^(-(p+1)) ∂P).toReal*
        (∫⁻ v, S v ∂R).toReal := by
  have h0 := weighted_real_moment_of_finite hAm hbm (fun ω => (hb ω).le) hF0.ne
  have h1 := weighted_real_moment_of_finite hAm hbm (fun ω => (hb ω).le)
    (s := 1) (q := -(p+1)) (by simpa only [Real.rpow_one] using hF1.ne)
  have he0 := hA.mono fun ω hω =>
    (reflected_pareto_parameter_weights p a (A ω).toReal (b ω) hω (hb ω).le).1
  have he1 := hA.mono fun ω hω =>
    (reflected_pareto_parameter_weights p a (A ω).toReal (b ω) hω (hb ω).le).2
  have he : ∀ q : ℝ, -(p+q) = -p-q := by intro q; ring
  simp only [he, Real.rpow_one] at h0 h1
  have hSa' : Integrable (fun v => (S v).toReal ^a) R ∧
      (∫ v, (S v).toReal ^a ∂R) = (∫⁻ v, S v ^a ∂R).toReal := by
    simpa only [ENNReal.toReal_rpow] using real_moment_of_finite (hSm.pow_const a) hSa.ne
  have hS1' := real_moment_of_finite hSm hS1.ne
  have hi := reflected_pareto_product_increment_error_nonneg P R p a hp ha ha1
    (fun ω => (A ω).toReal) b (fun v => (S v).toReal) hA (ae_of_all P hb)
    (ae_of_all R fun _ => ENNReal.toReal_nonneg) (h0.1.congr (Filter.EventuallyEq.symm he0))
    (h1.1.congr (Filter.EventuallyEq.symm he1)) hSa'.1 hS1'.1 hAm.ennreal_toReal hbm hSm.ennreal_toReal
  rw [integral_congr_ae he0, integral_congr_ae he1, h0.2, h1.2, hSa'.2, hS1'.2] at hi
  simpa only [he] using hi

end DOZZ.Proofs
