/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Reflection.RtheorAnalytic
public import DOZZ.Statements.Brownian.IsReflectionData
public import DOZZ.Statements.Brownian.IsSourceLateralProjection
public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
public import DOZZ.Statements.Defs.ExtendedSeiberg3
import DOZZ.Brownian.Reflection.PositiveFinite
import DOZZ.Complex.Basic
import DOZZ.DOZZAlgebra.ReflectionShifts
import DOZZ.DOZZAlgebra.ReflectionLimit
import Mathlib.Topology.Instances.Irrational
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import DOZZ.Brownian.Reflection.WitnessIndependence
import DOZZ.Brownian.ReflectionPoleIsolation
import DOZZ.Roots.Existence
import DOZZ.GMC.Assembly.AdmissibleGMC

/-!
# `R = R^DOZZ` from the shift equations

This is the argument of [KRV, §10.6]. Let
`ψ = R / R^DOZZ`, a meromorphic function on a strip around the real axis. The common `γ/2` shift
equation (`reflectionR_first_shift_meromorphic`) makes `ψ` periodic. The `2/γ` shift equations
(`reflectionR_dual_shift_unknown_constant`) make it quasi-periodic, with multiplier
`c_γ / c_γ^DOZZ`. On the physical interval `ψ` is the explicit positive ratio `reflectionDOZZRatio`,
so the multiplier is one. For irrational `γ²` the two periods are rationally independent, so `ψ` is
constant, and the endpoint normalizations `R(Q) = R^DOZZ(Q) = -1` force `ψ = 1`. Continuity of
both coefficients off the Gamma poles then gives equality at every pole-free physical charge. The
remaining couplings follow by continuity in `γ` (`reflection_endpoint_and_gamma_continuity`), since
couplings with irrational square accumulate at every `γ₀`.

The last two theorems prove both Brownian `R_theor` statements from the statements
`DOZZ.reflectionR_first_shift_meromorphic`, `DOZZ.reflectionR_dual_shift_unknown_constant` and
`DOZZ.reflection_endpoint_and_gamma_continuity`.
The three statements are taken verbatim as hypotheses at universe `0`. A reference equator
GFF and its GMC family supply the probability space, and witness independence moves every
coefficient onto one witness family.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs


/-- The first-shift denominator, in the form of the DOZZ shift. -/
noncomputable def reflectionFirstShiftDenom (γ : ℝ) (w : ℂ) : ℂ :=
  lFun (-(γ ^ 2 / 4)) * lFun (γ * w / 2 - γ ^ 2 / 4) * lFun (2 + γ ^ 2 / 2 - γ * w / 2)

/-- The dual-shift denominator, in the form of the DOZZ dual shift. -/
noncomputable def reflectionDualShiftDenom (γ : ℝ) (w : ℂ) : ℂ :=
  lFun (-((4 / γ ^ 2 : ℝ) : ℂ)) * lFun (2 * w / γ) * lFun (2 + (4 / γ ^ 2 : ℝ) - 2 * w / γ)

/-- The multiplier of the DOZZ dual shift. -/
noncomputable def reflectionDOZZDualConst (γ μ : ℝ) : ℂ :=
  ((dozzBase γ μ : ℝ) : ℂ) ^ ((4 / γ ^ 2 : ℝ) : ℂ) / lFun ((4 / γ ^ 2 : ℝ) : ℂ)


/-- The dual-shift denominator vanishes only on a codiscrete exceptional set, when `4/γ²` is not
an integer. -/
theorem reflectionDualShiftDenom_ne_zero {γ : ℝ} (hγ : 0 < γ)
    (hγk : ∀ n : ℤ, 4 / γ ^ 2 ≠ n) :
    ∀ᶠ w in Filter.codiscrete ℂ, reflectionDualShiftDenom γ w ≠ 0 := by
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have h0 : lFun (-((4 / γ ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    refine lFun_ne_zero_of_forall_ne_int fun n hn => hγk (-n) ?_
    push_cast
    linarith only [(by exact_mod_cast hn)]
  filter_upwards [(eventually_affine_lFun_ne_zero (c := 2 / (γ : ℂ)) (d := 0) (div_ne_zero two_ne_zero hγc)), (eventually_affine_lFun_ne_zero (c := -(2 / (γ : ℂ))) (d := 2 + ((4 / γ ^ 2 : ℝ) : ℂ)) (neg_ne_zero.mpr (div_ne_zero two_ne_zero hγc)))] with w hw1 hw2
  unfold reflectionDualShiftDenom
  refine mul_ne_zero (mul_ne_zero h0 ?_) ?_
  · convert hw1 using 2
    ring
  · convert hw2 using 2
    ring

/-- The DOZZ dual multiplier is nonzero when `4/γ²` is not an integer. -/
theorem reflectionDOZZDualConst_ne_zero {γ μ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hγk : ∀ n : ℤ, 4 / γ ^ 2 ≠ n) : reflectionDOZZDualConst γ μ ≠ 0 := by
  refine div_ne_zero ?_ (lFun_ne_zero_of_forall_ne_int fun n hn => hγk n (by exact_mod_cast hn))
  exact (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by
    exact_mod_cast (div_pos (by norm_num : (0 : ℝ) < 4) (by positivity)).ne')).mpr (by exact_mod_cast (dozzBase_pos hγ hγ2 hμ).ne')

/-- Irrationality of `γ²` excludes integer values of `4/γ²`. -/
theorem four_div_sq_ne_int_of_irrational {γ} (hγirr : Irrational (γ ^ 2)) (n : ℤ) :
    4 / γ ^ 2 ≠ n := by
  intro h
  have : γ ≠ 0 := fun h0 => hγirr.ne_zero (by rw [h0]; ring)
  have hmul : γ ^ 2 * (n : ℝ) = 4 := by
    rw [← h]
    field_simp
  exact hγirr ⟨4 / n, (show γ ^ 2 = ((4 / n : ℚ) : ℝ) by push_cast; exact eq_div_of_mul_eq (by intro h0; rw [h0, mul_zero] at hmul; norm_num at hmul) hmul).symm⟩





/-- **`R = R^DOZZ` at irrational `γ²`**, from the two reflection shift equations
(`DOZZ.reflectionR_first_shift_meromorphic`, `DOZZ.reflectionR_dual_shift_unknown_constant`) for
interpolants of the probabilistic coefficient along one witness family, continuity of `R̄` along
that family, and the endpoint limit `R → -1`. -/
theorem reflectionR_eq_reflectionDOZZ_of_shifts
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ μ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγirr : Irrational (γ ^ 2)) (hμ : 0 < μ)
    (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : ∀ α : ℝ, γ / 2 < α → α < Q γ → IsReflectionData P γ α (B α) Z)
    {h₁ h₂ : ℝ} (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) {R₁ R₂ : ℂ → ℂ}
    (hR₁ : MeromorphicOn R₁ {z | |z.im| < h₁}) (hR₂ : MeromorphicOn R₂ {z | |z.im| < h₂})
    (hR₁α : ∀ α : ℝ, γ / 2 < α → α < Q γ → R₁ (α : ℂ) = (reflectionR P γ μ α (B α) Z : ℂ))
    (hR₂α : ∀ α : ℝ, γ / 2 < α → α < Q γ → R₂ (α : ℂ) = (reflectionR P γ μ α (B α) Z : ℂ))
    (hshift₁ : ∀ᶠ z in codiscrete ℂ,
      R₁ (z - γ / 2) =
        -(μ * Real.pi : ℂ) * R₁ z /
          (lFun (-((γ : ℂ) ^ 2) / 4) *
            lFun ((γ : ℂ) * z / 2 - (γ : ℂ) ^ 2 / 4) *
            lFun (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2)))
    {c : ℂ}
    (hshift₂ : ∀ᶠ z in codiscrete ℂ,
      R₂ z = -c * R₂ (z + 2 / γ) /
        (lFun (-4 / (γ : ℂ) ^ 2) * lFun (2 * z / γ) *
          lFun (2 + 4 / (γ : ℂ) ^ 2 - 2 * z / γ)))
    (hBar : ContinuousOn (fun α => reflectionBarR P γ α (B α) Z) (Ioo (γ / 2) (Q γ)))
    (hEnd : Tendsto (fun α => reflectionR P γ μ α (B α) Z) (𝓝[<] (Q γ)) (𝓝 (-1)))
    {α : ℝ} (hα : γ / 2 < α ∧ α < Q γ) (hPole : ReflectionPoleFree γ α) :
    (reflectionR P γ μ α (B α) Z : ℂ) = reflectionDOZZ γ μ (α : ℂ) := by
  have half_add_half_lt_Q : γ / 2 + γ / 2 < Q γ := by
    unfold Q
    linarith only [(show γ / 2 < 2 / γ by rw [div_lt_div_iff₀ two_pos hγ]; exact mul_self_lt_mul_self hγ.le hγ2)]
  have reflectionQuotient_eventually_eq_ratio {R : ℂ → ℂ} (hRα : ∀ α : ℝ, γ / 2 < α → α < Q γ → R (α : ℂ) = (reflectionR P γ μ α (B α) Z : ℂ)) {x} (hx : x ∈ Ioo (γ / 2) (Q γ)) : ∀ᶠ y : ℝ in 𝓝[≠] x, R (y : ℂ) / reflectionDOZZ γ μ (y : ℂ) = (reflectionDOZZRatio γ μ y (reflectionBarR P γ y (B y) Z) : ℂ) := by
    filter_upwards [reflectionPoleFree_eventually_nhdsNE hγ x,
      nhdsWithin_le_nhds (Ioo_mem_nhds hx.1 hx.2)] with y hpole hy
    rw [hRα y hy.1 hy.2]
    exact reflectionR_div_reflectionDOZZ P γ μ y (B y) Z hγ hγ2 hμ ⟨hy.1, hy.2⟩ hpole
  have reflectionQuotient_dualShift {γ : ℝ} {μ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ) (hγirr : Irrational (γ ^ 2)) {R : ℂ → ℂ} {c : ℂ} (hshift : ∀ᶠ z in codiscrete ℂ, R z = -c * R (z + 2 / γ) / (lFun (-4 / (γ : ℂ) ^ 2) * lFun (2 * z / γ) * lFun (2 + 4 / (γ : ℂ) ^ 2 - 2 * z / γ))) : ∀ᶠ w in codiscrete ℂ, R w / reflectionDOZZ γ μ w = c / reflectionDOZZDualConst γ μ * (R (w + 2 / γ) / reflectionDOZZ γ μ (w + 2 / γ)) := by
    have hγk := four_div_sq_ne_int_of_irrational hγirr
    have hden : ∀ w : ℂ, lFun (-4 / (γ : ℂ) ^ 2) * lFun (2 * w / γ) *
        lFun (2 + 4 / (γ : ℂ) ^ 2 - 2 * w / γ) = reflectionDualShiftDenom γ w := by
      intro w
      unfold reflectionDualShiftDenom
      rw [(show (-4 / (γ : ℂ) ^ 2) = -((4 / γ ^ 2 : ℝ) : ℂ) by push_cast; ring), (show (2 + 4 / (γ : ℂ) ^ 2 - 2 * w / γ) = 2 + ((4 / γ ^ 2 : ℝ) : ℂ) - 2 * w / γ by push_cast; ring)]
    exact div_eq_mul_div_comp_add_of_shift (reflectionDOZZDualConst_ne_zero hγ hγ2 hμ hγk) (by filter_upwards [hshift] with w hw; rw [hw, hden]) (show ∀ᶠ w in codiscrete ℂ, reflectionDOZZ γ μ w = -reflectionDOZZDualConst γ μ * reflectionDOZZ γ μ (w + 2 / γ) / reflectionDualShiftDenom γ w by filter_upwards [reflectionDOZZ_shift_binv hγ hγ2 (fun k hk => hγk k (by exact_mod_cast hk)) hμ] with w hw; rw [hw, reflectionDualShiftDenom, reflectionDOZZDualConst])
      (reflectionDualShiftDenom_ne_zero hγ hγk)
  have reflectionQuotient_period {R : ℂ → ℂ} (hshift : ∀ᶠ z in codiscrete ℂ, R (z - γ / 2) = -(μ * Real.pi : ℂ) * R z / (lFun (-((γ : ℂ) ^ 2) / 4) * lFun ((γ : ℂ) * z / 2 - (γ : ℂ) ^ 2 / 4) * lFun (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2))) z : (fun w => R (w + ((γ / 2 : ℝ) : ℂ)) / reflectionDOZZ γ μ (w + ((γ / 2 : ℝ) : ℂ))) =ᶠ[𝓝[≠] z] fun w => R w / reflectionDOZZ γ μ w := by
    have reflectionFirstShiftDenom_ne_zero : ∀ᶠ w in Filter.codiscrete ℂ, reflectionFirstShiftDenom γ w ≠ 0 := by
      have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
      have hq : 0 < γ ^ 2 / 4 := by positivity
      have h0 : lFun (-((γ : ℂ) ^ 2 / 4)) ≠ 0 := by
        refine lFun_ne_zero_of_forall_ne_int fun n hn => ?_
        have hn' : -(γ ^ 2 / 4) = (n : ℝ) := by exact_mod_cast hn
        rcases lt_trichotomy n 0 with hlt | heq | hgt
        · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
          linarith only [hn', this, (show γ ^ 2 / 4 < 1 by linarith only [pow_lt_pow_left₀ hγ2 hγ.le two_ne_zero])]
        · rw [heq, Int.cast_zero] at hn'
          linarith only [hn', hq]
        · have : (1 : ℝ) ≤ n := by exact_mod_cast hgt
          linarith only [hn', this, hq]
      filter_upwards [(eventually_affine_lFun_ne_zero (c := (γ : ℂ) / 2) (d := -((γ : ℂ) ^ 2 / 4)) (div_ne_zero hγc two_ne_zero)), (eventually_affine_lFun_ne_zero (c := -((γ : ℂ) / 2)) (d := 2 + (γ : ℂ) ^ 2 / 2) (neg_ne_zero.mpr (div_ne_zero hγc two_ne_zero)))] with w hw1 hw2
      unfold reflectionFirstShiftDenom
      refine mul_ne_zero (mul_ne_zero h0 ?_) ?_
      · convert hw1 using 2
        ring
      · convert hw2 using 2
        ring
    filter_upwards [eventually_nhdsNE_of_eventually_codiscrete (eventually_codiscrete_comp_add (div_comp_sub_eq_of_shift (neg_ne_zero.mpr (mul_ne_zero (by exact_mod_cast hμ.ne') (by exact_mod_cast Real.pi_ne_zero))) (show ∀ᶠ w in Filter.codiscrete ℂ, R (w - (γ : ℂ) / 2) = -(μ * Real.pi : ℂ) * R w / reflectionFirstShiftDenom γ w by filter_upwards [hshift] with w hw; rw [hw, reflectionFirstShiftDenom, neg_div]) (show ∀ᶠ w in Filter.codiscrete ℂ, reflectionDOZZ γ μ (w - (γ : ℂ) / 2) = -(μ * Real.pi : ℂ) * reflectionDOZZ γ μ w / reflectionFirstShiftDenom γ w by filter_upwards [reflectionDOZZ_shift_b hγ hγ2 hμ] with w hw; rw [hw, reflectionFirstShiftDenom]) (reflectionFirstShiftDenom_ne_zero)) ((γ : ℂ) / 2)) z] with w hw
    rw [(show (((γ / 2 : ℝ)) : ℂ) = (γ : ℂ) / 2 by push_cast; ring)]
    simpa only [add_sub_cancel_right] using hw.symm
  have eventuallyEq_nhdsNE_strip_of_eq_on_Ioo {f : ℂ → ℂ} {g : ℂ → ℂ} (hf : MeromorphicOn f (horizontalStrip h₁)) (hg : MeromorphicOn g (horizontalStrip h₂)) {a : ℝ} {b : ℝ} (hab : a < b) (hfg : ∀ y ∈ Ioo a b, f (y : ℂ) = g (y : ℂ)) : ∀ z ∈ horizontalStrip (min h₁ h₂), f =ᶠ[𝓝[≠] z] g := by
    have hsub₁ : horizontalStrip (min h₁ h₂) ⊆ horizontalStrip h₁ := fun z hz => by
      simp only [horizontalStrip, mem_ofPred_eq] at hz ⊢
      exact lt_of_lt_of_le hz (min_le_left _ _)
    have hsub₂ : horizontalStrip (min h₁ h₂) ⊆ horizontalStrip h₂ := fun z hz => by
      simp only [horizontalStrip, mem_ofPred_eq] at hz ⊢
      exact lt_of_lt_of_le hz (min_le_right _ _)
    have hmem : (((a + b) / 2 : ℝ) : ℂ) ∈ horizontalStrip (min h₁ h₂) :=
      ofReal_mem_horizontalStrip (lt_min hh₁ hh₂) _
    exact eventuallyEq_nhdsNE_of_isPreconnected (convex_horizontalStrip _).isPreconnected
      (hf.mono_set hsub₁) (hg.mono_set hsub₂) hmem (eventuallyEq_nhdsNE_of_eq_on_Ioo ⟨by linarith only [hab], by linarith only [hab]⟩ (hf _ (hsub₁ hmem)) (hg _ (hsub₂ hmem)) hfg)
  have hQ : γ / 2 < Q γ := by linarith only [half_add_half_lt_Q, hγ]
  have hh := lt_min hh₁ hh₂
  have hsub₁ : horizontalStrip (min h₁ h₂) ⊆ {z : ℂ | |z.im| < h₁} := fun z hz => by
    simp only [horizontalStrip, mem_ofPred_eq] at hz ⊢
    exact lt_of_lt_of_le hz (min_le_left _ _)
  set RD := reflectionDOZZ γ μ with hRD_def
  set F : ℂ → ℂ := fun w => R₁ w / RD w with hF_def
  have hFm : MeromorphicOn F (horizontalStrip (min h₁ h₂)) :=
    (hR₁.mono_set hsub₁).div ((meromorphicOn_reflectionDOZZ γ μ hγ hγ2 hμ).mono_set
      (subset_univ _))
  -- the two interpolants share their punctured germs on the common strip
  have hR₁₂ := eventuallyEq_nhdsNE_strip_of_eq_on_Ioo hR₁ hR₂ hQ
      (fun y hy => (hR₁α y hy.1 hy.2).trans (hR₂α y hy.1 hy.2).symm)
  -- first period `γ/2`
  have hp₁ : ∀ z ∈ horizontalStrip (min h₁ h₂),
      (fun w => F (w + ((γ / 2 : ℝ) : ℂ))) =ᶠ[𝓝[≠] z] F :=
    fun z _ => reflectionQuotient_period hshift₁ z
  -- dual quasi-period `2/γ`
  set κ := c / reflectionDOZZDualConst γ μ with hκ_def
  have hq : ∀ z ∈ horizontalStrip (min h₁ h₂),
      F =ᶠ[𝓝[≠] z] fun w => κ * F (w + ((2 / γ : ℝ) : ℂ)) := by
    intro z hz
    have h1 : F =ᶠ[𝓝[≠] z] fun w => R₂ w / RD w :=
      (hR₁₂ z hz).mono fun w hw => by
        show R₁ w / RD w = R₂ w / RD w
        rw [hw]
    filter_upwards [h1, ((tendsto_add_const_nhdsNE z _).eventually (hR₁₂ _ (add_ofReal_mem_horizontalStrip hz _))), eventually_nhdsNE_of_eventually_codiscrete (reflectionQuotient_dualShift (μ := μ) hγ hγ2 hμ hγirr hshift₂) z] with w hw1 hw2 hw3
    rw [hw1, hw3]
    show κ * (R₂ (w + 2 / (γ : ℂ)) / RD (w + 2 / (γ : ℂ))) =
      κ * (R₁ (w + ((2 / γ : ℝ) : ℂ)) / RD (w + ((2 / γ : ℝ) : ℂ)))
    rw [hw2, (show ((2 / γ : ℝ) : ℂ) = 2 / (γ : ℂ) by push_cast; ring)]
  -- positivity and continuity on the physical interval force the multiplier to be one
  have hκ := quasiPeriod_multiplier_eq_one hh hFm (by positivity : (0 : ℝ) < γ / 2)
      (fun z hz => (hp₁ z hz).symm) hq (half_add_half_lt_Q) (continuousOn_reflectionDOZZRatio γ μ hγ hγ2 hμ _ hBar) (fun x hx => reflectionDOZZRatio_pos γ μ x _ hγ hγ2 hμ ⟨hx.1, hx.2⟩ (reflectionBarR_positive_finite P γ x hγ hγ2 ⟨hx.1, hx.2⟩ (B x) Z (hData x hx.1 hx.2)).1) (fun x hx => reflectionQuotient_eventually_eq_ratio hR₁α hx)
  -- the two periods are rationally independent, so the quotient is constant
  have hirr : ∀ q : ℚ, (γ / 2) / (2 / γ) ≠ (q : ℝ) := by
    intro q hq'
    have hsq : γ ^ 2 = ((4 * q : ℚ) : ℝ) := by
      push_cast
      rw [← hq']
      field_simp
      norm_num
    exact hγirr ⟨4 * q, hsq.symm⟩
  obtain ⟨c₀, hc₀, -⟩ := meromorphicOn_strip_constant_of_dense_periods (min h₁ h₂) hh F hFm
    (γ / 2) (2 / γ) (by positivity) (by positivity) hirr hp₁ (by intro z hz; filter_upwards [hq z hz] with w hw; rw [hw, hκ, one_mul])
  -- the endpoint normalizations identify the constant
  have hleft : Tendsto (fun y : ℝ => (y : ℂ)) (𝓝[<] (Q γ)) (𝓝[≠] ((Q γ : ℝ) : ℂ)) :=
    (tendsto_ofReal_nhdsNE (Q γ)).mono_left (nhdsWithin_mono _ fun y hy => ne_of_lt hy)
  have hnum : Tendsto (fun y : ℝ => (reflectionR P γ μ y (B y) Z : ℂ)) (𝓝[<] (Q γ))
      (𝓝 (-1)) := by
    have h := (Complex.continuous_ofReal.tendsto (-1 : ℝ)).comp hEnd
    rw [Complex.ofReal_neg, Complex.ofReal_one] at h
    exact h
  have hratio : Tendsto (fun y : ℝ => F (y : ℂ)) (𝓝[<] (Q γ)) (𝓝 1) := by
    have h := hnum.div ((reflectionDOZZ_tendsto_Q hγ hγ2 hμ).comp hleft) (by norm_num)
    rw [show ((-1 : ℂ) / -1) = 1 by norm_num] at h
    refine h.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hQ] with y hy
    show (reflectionR P γ μ y (B y) Z : ℂ) / RD y = R₁ y / RD y
    rw [hR₁α y hy.1 hy.2]
  have hc₁ : c₀ = 1 :=
    tendsto_nhds_unique (tendsto_const_nhds.congr' ((hleft.eventually (hc₀ _ (ofReal_mem_horizontalStrip hh _))).mono fun y hy => hy.symm)) hratio
  -- equality off the poles, by continuity of both coefficients
  have heq : ∀ᶠ y : ℝ in 𝓝[≠] α, (reflectionR P γ μ y (B y) Z : ℂ) = RD (y : ℂ) := by
    filter_upwards [(show ∀ᶠ y : ℝ in 𝓝[≠] α, F (y : ℂ) = 1 by simpa only [hc₁] using ((tendsto_ofReal_nhdsNE α).eventually (hc₀ _ (ofReal_mem_horizontalStrip hh α)))), reflectionPoleFree_eventually_nhdsNE hγ α,
      nhdsWithin_le_nhds (Ioo_mem_nhds hα.1 hα.2)] with y hy hpole hyI
    rw [← hR₁α y hyI.1 hyI.2]
    exact (div_eq_one_iff_eq (reflectionDOZZ_ofReal_ne_zero γ μ y hγ hγ2 hμ ⟨hyI.1, hyI.2⟩ hpole)).mp hy
  exact tendsto_nhds_unique (((Complex.continuous_ofReal.continuousAt.comp (continuousAt_reflectionR_formula hγ hμ hα hPole (hBar.continuousAt (Ioo_mem_nhds hα.1 hα.2)))).tendsto.mono_left nhdsWithin_le_nhds).congr' heq)
    ((continuousAt_reflectionDOZZ_ofReal hγ hγ2 hμ hα hPole).tendsto.mono_left nhdsWithin_le_nhds)

end DOZZ.Proofs

end
