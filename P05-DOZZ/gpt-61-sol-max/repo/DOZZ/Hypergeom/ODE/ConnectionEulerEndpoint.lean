/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Planar.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Real Euler-kernel endpoint estimates used to evaluate connection coefficients. -/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace DOZZ.Proofs

/-- The real Euler kernel before division by its beta normalization. -/
noncomputable def realGaussEulerKernelIntegral (a b c x : ℝ) : ℝ :=
  ∫ t : ℝ in Ioc 0 1,
    t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - x * t) ^ (-a)

variable (p q : ℝ) (hp : 0 < p) (hq : 0 < q)

include p q hp hq in
/-- The real beta density with positive parameters is integrable on `(0,1]`. -/
theorem realEulerBetaWeight_integrable  :
    IntegrableOn (fun t : ℝ => t ^ (p - 1) * (1 - t) ^ (q - 1)) (Ioc 0 1) := by
  have hcomplex : IntervalIntegrable
      (fun t : ℝ => (t : ℂ) ^ ((p : ℂ) - 1) * (1 - (t : ℂ)) ^ ((q : ℂ) - 1))
      volume 0 1 := by
    apply Complex.betaIntegral_convergent
    all_goals simp_all
  have hcomplex' : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ ((p : ℂ) - 1) * (1 - (t : ℂ)) ^ ((q : ℂ) - 1))
      (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume)
      (a := (0 : ℝ)) (b := 1) (by norm_num)).mp hcomplex
  have hcast : IntegrableOn
      (fun t : ℝ => (t ^ (p - 1) * (1 - t) ^ (q - 1) : ℝ) : ℝ → ℂ)
      (Ioc 0 1) := by
    apply hcomplex'.congr_fun
    · intro t ht
      have ht0  := le_of_lt ht.1
      have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
      change (t : ℂ) ^ ((p : ℂ) - 1) * (1 - (t : ℂ)) ^ ((q : ℂ) - 1) =
        ((t ^ (p - 1) * (1 - t) ^ (q - 1) : ℝ) : ℂ)
      have hp' : (t : ℂ) ^ ((p : ℂ) - 1) = ((t ^ (p - 1) : ℝ) : ℂ) := by
        rw [show (p : ℂ) - 1 = ((p - 1 : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_cpow ht0]
      have hq' : (1 - (t : ℂ)) ^ ((q : ℂ) - 1) = (((1 - t) ^ (q - 1) : ℝ) : ℂ) := by
        rw [show (q : ℂ) - 1 = ((q - 1 : ℝ) : ℂ) by push_cast; ring,
          show (1 : ℂ) - (t : ℝ) = ((1 - t : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_cpow ht1]
      rw [hp', hq', Complex.ofReal_mul]
    · exact measurableSet_Ioc
  exact (IntegrableOn.iff_ofReal).mpr hcast

variable (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hδ : 0 < c - a - b)

include a b c ha hb hδ in
/-- The Euler kernel converges to the beta density at `z=1` from below, whenever the endpoint
exponents are integrable. This is the dominated-convergence step in Gauss's endpoint formula. -/
theorem realGaussEulerKernelIntegral_tendsto_one  :
    Tendsto (fun x : ℝ => realGaussEulerKernelIntegral a b c x)
      (𝓝[Iio 1] 1)
      (𝓝 (∫ t : ℝ in Ioc 0 1,
        t ^ (b - 1) * (1 - t) ^ (c - a - b - 1))) := by
  let s : Set ℝ := Ioc 0 1
  let F : Filter ℝ := 𝓝[Iio 1] 1
  let w : ℝ → ℝ := fun t => t ^ (b - 1) * (1 - t) ^ (c - a - b - 1)
  let k : ℝ → ℝ → ℝ := fun x t =>
    t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - x * t) ^ (-a)
  have hweight : Integrable w (volume.restrict s) := by
    exact (realEulerBetaWeight_integrable b (c - a - b) hb hδ).integrable
  have hxpos : ∀ᶠ x : ℝ in F, 0 < x := by
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num))
  have hxlt : ∀ᶠ x : ℝ in F, x < 1 := by
    exact eventually_mem_nhdsWithin
  have hxrange : ∀ᶠ x : ℝ in F, x ∈ Ioc 0 1 := by
    filter_upwards [hxpos, hxlt] with x hxp hxl
    exact ⟨hxp, hxl.le⟩
  have hmeas : ∀ᶠ x : ℝ in F,
      AEStronglyMeasurable (fun t : ℝ => k x t) (volume.restrict s) := by
    filter_upwards [hxrange] with x hx
    exact (by fun_prop : Measurable (fun t : ℝ => k x t)).aestronglyMeasurable
  have hbound : ∀ᶠ x : ℝ in F, ∀ᵐ t ∂(volume.restrict s),
      ‖k x t‖ ≤ w t := by
    filter_upwards [hxrange] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (volume.ae_ne (1 : ℝ))]
      with t ht htn
    have ht0  := ht.1
    have ht1  := lt_of_le_of_ne ht.2 htn
    have hx1  := hx.2
    have hbase0 : 0 < 1 - x * t := by nlinarith
    have hbase1 : 0 < 1 - t := by linarith
    have hbase : 1 - t ≤ 1 - x * t := by nlinarith
    have hpow : (1 - x * t) ^ (-a) ≤ (1 - t) ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos hbase1 hbase (by linarith)
    have hfactor : 0 < t ^ (b - 1) * (1 - t) ^ (c - b - 1) := by
      bound
    have hrewrite : (1 - t) ^ (c - b - 1) * (1 - t) ^ (-a) =
        (1 - t) ^ (c - a - b - 1) := by
      rw [← Real.rpow_add hbase1]
      congr 1
      ring_nf
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ k x t)]
    dsimp [k, w]
    calc
      t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - x * t) ^ (-a)
          ≤ t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - t) ^ (-a) :=
            mul_le_mul_of_nonneg_left hpow (le_of_lt hfactor)
      _ = t ^ (b - 1) * (1 - t) ^ (c - a - b - 1) := by
        rw [mul_assoc, hrewrite]
  have hlim : ∀ᵐ t ∂(volume.restrict s),
      Tendsto (fun x : ℝ => k x t) F (𝓝 (w t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (volume.ae_ne (1 : ℝ))] with t ht htn
    have ht1  := lt_of_le_of_ne ht.2 htn
    have hbase : Tendsto (fun x : ℝ => 1 - x * t) F (𝓝 (1 - t)) := by
      have hid : Tendsto (fun x : ℝ => x) F (𝓝 (1 : ℝ)) := by
        exact tendsto_id.mono_left nhdsWithin_le_nhds
      have hmul  :=
        hid.mul_const t
      simpa using tendsto_const_nhds.sub hmul
    have hpow : Tendsto (fun x : ℝ => (1 - x * t) ^ (-a)) F
        (𝓝 ((1 - t) ^ (-a))) := by
      have hcont  :=
        Real.continuousAt_rpow (1 - t, -a)
          (Or.inl (ne_of_gt (by linarith : 0 < 1 - t)))
      have hp : Tendsto (fun x : ℝ => (1 - x * t, -a)) F (𝓝 (1 - t, -a)) :=
        hbase.prodMk_nhds tendsto_const_nhds
      simpa [Function.comp_def] using hcont.tendsto.comp hp
    have hconst : Tendsto (fun _ : ℝ => t ^ (b - 1) * (1 - t) ^ (c - b - 1))
        F (𝓝 (t ^ (b - 1) * (1 - t) ^ (c - b - 1))) := tendsto_const_nhds
    have hmul := hconst.mul hpow
    have hrewrite :
        t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - t) ^ (-a) = w t := by
      dsimp [w]
      rw [mul_assoc, ← Real.rpow_add (by linarith : 0 < 1 - t)]
      congr 1
      ring_nf
    grind
  have hdc := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict s) (l := F) (F := fun x t => k x t) (f := w)
    w hmeas hbound hweight hlim
  assumption_mod_cast

include p q hp hq in
/-- The limiting Euler density is the real beta integral, hence the classical Gamma ratio. -/
theorem realEulerBetaIntegral_eq_gamma_ratio  :
    (∫ t : ℝ in Ioc 0 1, t ^ (p - 1) * (1 - t) ^ (q - 1)) =
      Real.Gamma p * Real.Gamma q / Real.Gamma (p + q) := by
  have hβ := Complex.betaIntegral_eq_Gamma_mul_div
    (p : ℂ) (q : ℂ) (by simp [Complex.ofReal_re]; linarith)
      (by simp [Complex.ofReal_re]; linarith)
  rw [betaIntegral_ofReal] at hβ
  apply Complex.ofReal_injective
  have hβ' := hβ
  rw [← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal] at hβ'
  simp_all

include a b c ha hb hδ in
/-- After division by the Euler beta normalization, the real Euler kernel has the classical Gauss
endpoint value. This is the scalar limit needed by the first connection coefficient. -/
theorem realGaussEulerKernelIntegral_tendsto_gauss_value  :
    Tendsto
      (fun x : ℝ =>
        (Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))) *
          realGaussEulerKernelIntegral a b c x)
      (𝓝[Iio 1] 1)
      (𝓝 (Real.Gamma c * Real.Gamma (c - a - b) /
        (Real.Gamma (c - a) * Real.Gamma (c - b)))) := by
  have hcb : 0 < c - b := by linarith
  have hca : 0 < c - a := by linarith
  have hΓb  := Real.Gamma_pos_of_pos hb
  
  have hΓca  := Real.Gamma_pos_of_pos hca
  have hβ := realEulerBetaIntegral_eq_gamma_ratio b (c - a - b) hb hδ
  have hβ' :
      (∫ t : ℝ in Ioc 0 1, t ^ (b - 1) * (1 - t) ^ (c - a - b - 1)) =
        Real.Gamma b * Real.Gamma (c - a - b) / Real.Gamma (c - a) := by
    simp_all
  have hratio :
      (Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))) *
        (∫ t : ℝ in Ioc 0 1, t ^ (b - 1) * (1 - t) ^ (c - a - b - 1)) =
          Real.Gamma c * Real.Gamma (c - a - b) /
            (Real.Gamma (c - a) * Real.Gamma (c - b)) := by
    grind
  have hlim := realGaussEulerKernelIntegral_tendsto_one a b c ha hb hδ
  have hscaled : Tendsto
      (fun x : ℝ =>
        (Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))) *
          realGaussEulerKernelIntegral a b c x)
      (𝓝[Iio 1] 1)
      (𝓝 ((Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))) *
        (∫ t : ℝ in Ioc 0 1,
          t ^ (b - 1) * (1 - t) ^ (c - a - b - 1)))) := tendsto_const_nhds.mul hlim
  simp_all

end DOZZ.Proofs
