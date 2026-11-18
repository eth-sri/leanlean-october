/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
public import DOZZ.Upsilon.Malmsten
import DOZZ.Upsilon.IntegralBounds
import DOZZ.Upsilon.IntegralHolomorphy
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.Complex.Convex
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# DOZZ Upsilon shifts on the defining strip

The strip overlap equations are proved from the defining integral, before using
its entire continuation.
-/

@[expose] public section
noncomputable section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ.Proofs

variable {γ : ℝ}


private def upsilonRealIntegrand (γ z t : ℝ) : ℝ :=
  ((Q γ / 2 - z) ^ 2 * Real.exp (-t) -
    Real.sinh ((Q γ / 2 - z) * (t / 2)) ^ 2 /
      (Real.sinh (t * γ / 4) * Real.sinh (t / γ))) / t

private lemma Q_eq_b (hγ : 0 < γ) : Q γ = γ / 2 + (γ / 2)⁻¹ := by
  unfold Q; field_simp [hγ.ne']; ring

private lemma upsilonRealIntegrand_shift_b_scaled {γ z u : ℝ} (hγ : 0 < γ) (hu : 0 < u) :
    let b := γ / 2
    b * (upsilonRealIntegrand γ (z + b) (b * u) - upsilonRealIntegrand γ z (b * u)) =
      malmstenRealIntegrand (b * z) u - malmstenRealIntegrand (1 - b * z) u +
        (2 * b * z - 1) * (u⁻¹ * (Real.exp (-b * u) - Real.exp (-u))) := by
  intro b
  have hb : 0 < b := by dsimp [b]; positivity
  have hQ : Q γ = b + b⁻¹ := Q_eq_b hγ
  have hγb : γ = 2 * b := by dsimp [b]; ring
  let eb := Real.exp (b ^ 2 * u / 4)
  let eu := Real.exp (u / 4)
  let ez := Real.exp (b * z * u / 2)
  have heb0 : eb ≠ 0 := Real.exp_ne_zero _
  have heu0 : eu ≠ 0 := Real.exp_ne_zero _
  have hez0 : ez ≠ 0 := Real.exp_ne_zero _
  have hs1 : Real.sinh (b * u * γ / 4) = (eb ^ 2 - eb⁻¹ ^ 2) / 2 := by
    rw [hγb, Real.sinh_eq, inv_pow, ← Real.exp_nat_mul, ← Real.exp_neg]
    dsimp [eb]; congr 3 <;> ring
  have hs2 : Real.sinh (b * u / γ) = (eu ^ 2 - eu⁻¹ ^ 2) / 2 := by
    rw [hγb, Real.sinh_eq, inv_pow, ← Real.exp_nat_mul, ← Real.exp_neg]
    dsimp [eu]
    have : b * u / (2 * b) = u / 2 := by field_simp [hb.ne']
    rw [this]; congr 3 <;> ring
  have hs1_ne : (eb ^ 2 - eb⁻¹ ^ 2) / 2 ≠ 0 := by
    rw [← hs1]; exact (Real.sinh_pos_iff.2 (by positivity)).ne'
  have hs2_ne : (eu ^ 2 - eu⁻¹ ^ 2) / 2 ≠ 0 := by
    rw [← hs2]; exact (Real.sinh_pos_iff.2 (div_pos (mul_pos hb hu) hγ)).ne'
  have hnum0 : Real.sinh ((Q γ / 2 - z) * (b * u / 2)) =
      (eb * eu * ez⁻¹ - eb⁻¹ * eu⁻¹ * ez) / 2 := by
    rw [hQ, Real.sinh_eq]
    have e1 : ((b + b⁻¹) / 2 - z) * (b * u / 2) = b ^ 2 * u / 4 + u / 4 - b * z * u / 2 := by
      field_simp [hb.ne']; ring
    rw [e1, show -(b ^ 2 * u / 4 + u / 4 - b * z * u / 2) = -(b ^ 2 * u / 4) - u / 4 + b * z * u / 2 by ring,
      Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_sub, Real.exp_neg]
    dsimp [eb, eu, ez]; field_simp [hez0, heu0]
  have hnum1 : Real.sinh ((Q γ / 2 - (z + b)) * (b * u / 2)) =
      (eb⁻¹ * eu * ez⁻¹ - eb * eu⁻¹ * ez) / 2 := by
    rw [hQ, Real.sinh_eq]
    have e1 : ((b + b⁻¹) / 2 - (z + b)) * (b * u / 2) = -(b ^ 2 * u / 4) + u / 4 - b * z * u / 2 := by
      field_simp [hb.ne']; ring
    rw [e1, show -(-(b ^ 2 * u / 4) + u / 4 - b * z * u / 2) = b ^ 2 * u / 4 - u / 4 + b * z * u / 2 by ring,
      Real.exp_sub, Real.exp_add, Real.exp_neg, Real.exp_add, Real.exp_sub]
    dsimp [eb, eu, ez]; field_simp [hez0, heu0]
  have he_u : Real.exp (-u) = eu⁻¹ ^ 4 := by
    rw [inv_pow, ← Real.exp_nat_mul, ← Real.exp_neg]; dsimp [eu]; congr 1; ring
  have he_bz : Real.exp (-(b * z) * u) = ez⁻¹ ^ 2 := by
    rw [inv_pow, ← Real.exp_nat_mul, ← Real.exp_neg]; dsimp [ez]; congr 1; ring
  have he_1bz : Real.exp (-(1 - b * z) * u) = eu⁻¹ ^ 4 * ez ^ 2 := by
    rw [inv_pow, ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_add]
    dsimp [eu, ez]; congr 1; ring
  have h1_eu : 1 - eu⁻¹ ^ 4 ≠ 0 := by rw [← he_u]; linarith [Real.exp_lt_one_iff.2 (neg_neg_of_pos hu)]
  have heb4 : eb ^ 4 - 1 ≠ 0 := by
    have : 1 < eb ^ 4 := one_lt_pow₀ (Real.one_lt_exp_iff.2 (by positivity)) (by norm_num)
    linarith
  have heu4 : eu ^ 4 - 1 ≠ 0 := by
    have : 1 < eu ^ 4 := one_lt_pow₀ (Real.one_lt_exp_iff.2 (by positivity)) (by norm_num)
    linarith
  have hQdiff : (Q γ / 2 - (z + b)) ^ 2 - (Q γ / 2 - z) ^ 2 = 2 * b * z - 1 := by
    rw [hQ]; field_simp [hb.ne']; ring
  unfold upsilonRealIntegrand malmstenRealIntegrand
  rw [hs1, hs2, hnum0, hnum1, show -(b * u) = -b * u by ring, he_bz, he_1bz, he_u]
  have hcancel : (((eb⁻¹ * eu * ez⁻¹ - eb * eu⁻¹ * ez) / 2) ^ 2 -
        ((eb * eu * ez⁻¹ - eb⁻¹ * eu⁻¹ * ez) / 2) ^ 2) /
      (((eb ^ 2 - eb⁻¹ ^ 2) / 2) * ((eu ^ 2 - eu⁻¹ ^ 2) / 2)) =
      -(ez⁻¹ ^ 2 - eu⁻¹ ^ 4 * ez ^ 2) / (1 - eu⁻¹ ^ 4) := by
    field_simp [heb0, heu0, hez0, hs1_ne, hs2_ne, h1_eu, heb4, heu4]
    ring
  have hsub_sq : ((Q γ / 2 - (z + b)) ^ 2 * Real.exp (-b * u) -
        ((eb⁻¹ * eu * ez⁻¹ - eb * eu⁻¹ * ez) / 2) ^ 2 / (((eb ^ 2 - eb⁻¹ ^ 2) / 2) * ((eu ^ 2 - eu⁻¹ ^ 2) / 2))) / (b * u) -
      ((Q γ / 2 - z) ^ 2 * Real.exp (-b * u) -
        ((eb * eu * ez⁻¹ - eb⁻¹ * eu⁻¹ * ez) / 2) ^ 2 / (((eb ^ 2 - eb⁻¹ ^ 2) / 2) * ((eu ^ 2 - eu⁻¹ ^ 2) / 2))) / (b * u) =
      (((Q γ / 2 - (z + b)) ^ 2 - (Q γ / 2 - z) ^ 2) * Real.exp (-b * u) -
        (((eb⁻¹ * eu * ez⁻¹ - eb * eu⁻¹ * ez) / 2) ^ 2 - ((eb * eu * ez⁻¹ - eb⁻¹ * eu⁻¹ * ez) / 2) ^ 2) /
          (((eb ^ 2 - eb⁻¹ ^ 2) / 2) * ((eu ^ 2 - eu⁻¹ ^ 2) / 2))) / (b * u) := by ring
  rw [hsub_sq, hQdiff, hcancel]
  field_simp [hb.ne', hu.ne', h1_eu]
  ring

private lemma exp_frullani {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => u⁻¹ * (Real.exp (-b * u) - Real.exp (-u))) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), u⁻¹ * (Real.exp (-b * u) - Real.exp (-u)) = -Real.log b := by
  have hI : IntegrableOn (fun u : ℝ => u⁻¹ * (Real.exp (-b * u) - Real.exp (-u))) (Ioi 0) :=
    (((malmstenRealIntegrand_integrableOn (add_pos hb one_pos)).sub
      (malmstenRealIntegrand_integrableOn hb)).neg).congr
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu;
          change -(malmstenRealIntegrand (b + 1) u - malmstenRealIntegrand b u) = _;
          rw [malmstenRealIntegrand_add_one_sub hu]; ring)
  refine ⟨hI, ?_⟩
  have hfr := Frullani.integral_Ioi_eq
    ((Continuous.continuousOn (by fun_prop)).locallyIntegrableOn measurableSet_Ioi)
    hb one_pos (by simpa using (Continuous.continuousAt (by fun_prop : Continuous fun u : ℝ => Real.exp (-u))).tendsto.mono_left nhdsWithin_le_nhds)
    Real.tendsto_exp_neg_atTop_nhds_zero (by simpa [smul_eq_mul, one_mul, neg_mul] using hI)
  simpa [smul_eq_mul, one_mul, neg_mul, Real.log_div one_ne_zero hb.ne'] using hfr

private lemma exp_upsilonLog_shift_b_real {γ z : ℝ} (hγ : 0 < γ) (hz0 : 0 < z) (hzQ : z < 2 / γ)
    (hI₀ : IntegrableOn (upsilonRealIntegrand γ z) (Ioi 0))
    (hI₁ : IntegrableOn (upsilonRealIntegrand γ (z + γ / 2)) (Ioi 0)) :
    Complex.exp (upsilonLog γ ((z + γ / 2 : ℝ) : ℂ)) =
      lFun ((γ / 2 : ℂ) * (z : ℂ)) * ((γ / 2 : ℝ) : ℂ) ^ ((1 - γ * z : ℝ) : ℂ) *
        Complex.exp (upsilonLog γ (z : ℂ)) := by
  let b := γ / 2
  let x := b * z
  have hb : 0 < b := by dsimp [b]; positivity
  have hx0 : 0 < x := mul_pos hb hz0
  have hx1 : 0 < 1 - x := by
    have hm := mul_lt_mul_of_pos_left hzQ hb
    have hc : b * (2 / γ) = 1 := by dsimp [b]; field_simp [hγ.ne']
    dsimp [x]; linarith
  have huLog (y : ℝ) : upsilonLog γ (y : ℂ) = ((∫ t in Ioi (0 : ℝ), upsilonRealIntegrand γ y t : ℝ) : ℂ) := by
    unfold upsilonLog
    rw [setIntegral_congr_fun measurableSet_Ioi fun t _ =>
      (by simp [upsilonLogIntegrand, upsilonRealIntegrand] :
        upsilonLogIntegrand γ (y : ℂ) t = (upsilonRealIntegrand γ y t : ℂ))]
    exact integral_ofReal
  obtain ⟨hfrI, hfrV⟩ := exp_frullani hb
  have hxI := malmstenRealIntegrand_integrableOn hx0
  have hyI := malmstenRealIntegrand_integrableOn hx1
  have hrealInt : (∫ t in Ioi (0 : ℝ), upsilonRealIntegrand γ (z + b) t) -
      ∫ t in Ioi (0 : ℝ), upsilonRealIntegrand γ z t =
      malmstenRealH x - malmstenRealH (1 - x) + (1 - 2 * x) * Real.log b := by
    rw [← integral_sub hI₁ hI₀,
      show (∫ t in Ioi (0 : ℝ), upsilonRealIntegrand γ (z + b) t - upsilonRealIntegrand γ z t) =
        b * ∫ u in Ioi (0 : ℝ), (upsilonRealIntegrand γ (z + b) (b * u) - upsilonRealIntegrand γ z (b * u)) by
        simpa [smul_eq_mul] using (integral_comp_mul_left_Ioi'
          (fun t => upsilonRealIntegrand γ (z + b) t - upsilonRealIntegrand γ z t) 0 hb).symm,
      ← integral_const_mul,
      setIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) => upsilonRealIntegrand_shift_b_scaled hγ hu]
    have hadd : (∫ u in Ioi (0 : ℝ), (malmstenRealIntegrand x - malmstenRealIntegrand (1 - x)) u +
        (2 * x - 1) * (u⁻¹ * (Real.exp (-b * u) - Real.exp (-u)))) =
        malmstenRealH x - malmstenRealH (1 - x) + (1 - 2 * x) * Real.log b := by
      rw [integral_add (hxI.sub hyI) (hfrI.const_mul _),
        show (∫ u in Ioi (0 : ℝ), (malmstenRealIntegrand x - malmstenRealIntegrand (1 - x)) u) =
          ∫ u in Ioi (0 : ℝ), malmstenRealIntegrand x u - malmstenRealIntegrand (1 - x) u from rfl,
        integral_sub hxI hyI, integral_const_mul, hfrV]
      simp only [malmstenRealH]; ring
    simpa only [Pi.sub_apply, x, b, mul_assoc] using hadd
  have hdiff : upsilonLog γ ((z + γ / 2 : ℝ) : ℂ) =
      ((malmstenRealH x - malmstenRealH (1 - x) + (1 - 2 * x) * Real.log b : ℝ) : ℂ) + upsilonLog γ (z : ℂ) := by
    rw [huLog, huLog]; exact_mod_cast eq_add_of_sub_eq hrealInt
  rw [hdiff, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_add, Real.exp_sub,
    malmstenRealH_exp_eq_Gamma hx0, malmstenRealH_exp_eq_Gamma hx1,
    mul_comm (1 - 2 * x), ← Real.rpow_def_of_pos hb, Complex.ofReal_mul, Complex.ofReal_div,
    ← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal, Complex.ofReal_cpow hb.le]
  unfold lFun
  congr 2
  · congr 1
    · congr 1; dsimp [x, b]; push_cast; ring
    · congr 1; dsimp [x, b]; push_cast; ring
  · congr 1; dsimp [x, b]; push_cast; ring

/-- Forward strip shift from the defining integral, assuming the source integral and its
derivative are available on the full strip. This form also applies to the dual parameter. -/
theorem exp_upsilonLog_shift_b_of_integrable (hγ : 0 < γ)
    (hDiff : DifferentiableOn ℂ (fun z => upsilonLog γ z)
      {z | 0 < z.re ∧ z.re < Q γ})
    (hInt : ∀ x : ℝ, 0 < x → x < Q γ →
      IntegrableOn (fun t : ℝ => upsilonLogIntegrand γ (x : ℂ) t) (Ioi 0))
    {z : ℂ} (hz0 : 0 < z.re) (hzQ : z.re < 2 / γ) :
    Complex.exp (upsilonLog γ (z + (γ / 2 : ℂ))) =
      lFun ((γ / 2 : ℂ) * z) * ((γ / 2 : ℝ) : ℂ) ^ (1 - (γ : ℂ) * z) *
        Complex.exp (upsilonLog γ z) := by
  let O : Set ℂ := {w | 0 < w.re ∧ w.re < 2 / γ}
  let T : Set ℂ := {w | 0 < w.re ∧ w.re < Q γ}
  let bC : ℂ := γ / 2
  let f : ℂ → ℂ := fun w => Complex.exp (upsilonLog γ (w + bC))
  let g : ℂ → ℂ := fun w => lFun (bC * w) * ((γ / 2 : ℝ) : ℂ) ^ (1 - (γ : ℂ) * w) * Complex.exp (upsilonLog γ w)
  have hQ : Q γ = γ / 2 + 2 / γ := by unfold Q; ring
  have hOOpen : IsOpen O := (Complex.isOpen_re_gt 0).inter (Complex.isOpen_re_lt (2 / γ))
  have hOsubT : O ⊆ T := fun w hw => ⟨hw.1, by rw [hQ]; linarith [hw.2]⟩
  have hshiftT : MapsTo (fun w => w + bC) O T := fun w hw => by
    refine ⟨?_, ?_⟩ <;> simp [bC] <;> linarith [hw.1, hw.2, hQ, hγ]
  have hf : DifferentiableOn ℂ f O :=
    differentiable_exp.comp_differentiableOn (hDiff.comp (by fun_prop) hshiftT)
  have hg : DifferentiableOn ℂ g O := by
    intro w hw
    have hb_re : 0 < (bC * w).re := by simp [bC, Complex.mul_re]; exact mul_pos (by positivity) hw.1
    have hG1 : DifferentiableAt ℂ (fun v => Complex.Gamma (bC * v)) w :=
      (Complex.differentiableAt_Gamma (bC * w) fun n hn =>
        Complex.Gamma_ne_zero_of_re_pos hb_re (by rw [hn]; exact Complex.Gamma_neg_nat_eq_zero n)).comp w (by fun_prop)
    have hG2 : DifferentiableAt ℂ (fun v => (Complex.Gamma (1 - bC * v))⁻¹) w :=
      Complex.differentiable_one_div_Gamma.differentiableAt.comp w (by fun_prop)
    have hpow : DifferentiableAt ℂ (fun v => ((γ / 2 : ℝ) : ℂ) ^ (1 - (γ : ℂ) * v)) w :=
      DifferentiableAt.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.2 (by positivity)))
    change DifferentiableWithinAt ℂ
      (fun v => Complex.Gamma (bC * v) * (Complex.Gamma (1 - bC * v))⁻¹ *
        ((γ / 2 : ℝ) : ℂ) ^ (1 - (γ : ℂ) * v) * Complex.exp (upsilonLog γ v)) O w
    exact (((hG1.mul hG2).mul hpow).differentiableWithinAt).mul
      (differentiable_exp.differentiableAt.comp_differentiableWithinAt w ((hDiff w (hOsubT hw)).mono hOsubT))
  let x₀ := 1 / γ
  have hw₀ : (x₀ : ℂ) ∈ O := ⟨by simp [x₀]; positivity,
    by simpa [x₀, one_div] using div_lt_div_of_pos_right one_lt_two hγ⟩
  have hcl : (x₀ : ℂ) ∈ closure ({w | f w = g w} \ {(x₀ : ℂ)}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    let d := min (ε / 2) (1 / (2 * γ))
    have hd : 0 < d := lt_min (half_pos hε) (by positivity)
    let r := x₀ + d
    have hr0 : 0 < r := by positivity
    have hrQ : r < 2 / γ := by
      have : d ≤ 1 / (2 * γ) := min_le_right _ _
      have : 1 / γ + 1 / (2 * γ) = (3 / 2) / γ := by field_simp [hγ.ne']; ring
      linarith [div_lt_div_of_pos_right (by norm_num : (3 / 2 : ℝ) < 2) hγ]
    have hrI (y : ℝ) (hy0 : 0 < y) (hyQ : y < Q γ) : IntegrableOn (upsilonRealIntegrand γ y) (Ioi 0) :=
      IntegrableOn.iff_ofReal.2 ((hInt y hy0 hyQ).congr
        (ae_of_all _ fun t => by simp [upsilonLogIntegrand, upsilonRealIntegrand]))
    have hfg : f (r : ℂ) = g (r : ℂ) := by
      have := exp_upsilonLog_shift_b_real hγ hr0 hrQ
        (hrI r hr0 (by rw [hQ]; linarith)) (hrI (r + γ / 2) (by positivity) (by rw [hQ]; linarith))
      simpa [f, g, bC] using this
    refine ⟨(r : ℂ), ⟨hfg, fun heq => hd.ne' (by linarith [Complex.ofReal_inj.1 heq])⟩, ?_⟩
    rw [dist_comm, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      show r - x₀ = d by ring, abs_of_pos hd]
    linarith [min_le_left (ε / 2) (1 / (2 * γ))]
  exact AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure (hf.analyticOnNhd hOOpen)
    (hg.analyticOnNhd hOOpen) ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt (2 / γ))).isPreconnected
    hw₀ hcl ⟨hz0, hzQ⟩

/-- Forward strip shift, using the convergence and holomorphy results for `upsilonLog` on the
defining strip. -/
theorem exp_upsilonLog_shift_b (hγ : 0 < γ) (hγ2 : γ < 2)
    {z : ℂ} (hz0 : 0 < z.re) (hzQ : z.re < 2 / γ) :
    Complex.exp (upsilonLog γ (z + (γ / 2 : ℂ))) =
      lFun ((γ / 2 : ℂ) * z) * ((γ / 2 : ℝ) : ℂ) ^ (1 - (γ : ℂ) * z) *
        Complex.exp (upsilonLog γ z) :=
  exp_upsilonLog_shift_b_of_integrable hγ (upsilonLog_differentiableOn hγ hγ2)
    (fun x hx0 hxQ => upsilonLogIntegrand_integrableOn hγ hγ2 (x : ℂ) (by simpa using hx0) (by simpa using hxQ))
    hz0 hzQ

end DOZZ.Proofs
