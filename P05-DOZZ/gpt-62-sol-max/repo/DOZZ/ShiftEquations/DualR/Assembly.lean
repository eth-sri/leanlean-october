/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import DOZZ.ShiftEquations.Gluing.ReflectedClosed
import DOZZ.ShiftEquations.Inversion.Reduction
public import DOZZ.ShiftEquations.DualR.Generic
public import DOZZ.ShiftEquations.DualR.AnalyticR
public import DOZZ.Statements.FourPoint.DualCrossingL
import DOZZ.ShiftEquations.Residual.Joint
import DOZZ.ShiftEquations.Gluing.Meromorphy
import DOZZ.ShiftEquations.Shift.ShiftGluing
import DOZZ.Brownian.Reflection.RtheorAnalytic
public import DOZZ.ShiftEquations.Representatives

/-!
# The dual shift of the reflection coefficient, from its inputs

Route ([KRV, §10.5]): the dual shift holds at generic real points just below `γ/2`
(`dualShift_eventually`), hence by the identity theorem near every point of the strip of the
representative `R` from `DOZZ.reflectionR_first_shift_meromorphic`; cutting `R` off outside a
thinner strip makes it hold along the codiscrete filter of `ℂ`. The constant `c_γ = (γ²/4) μπ R(γ)`
is nonzero since `R(γ) ≠ 0`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- The dual shift of the reflection coefficient, with a nonzero constant determined by `R(γ)`. -/
theorem reflectionR_dual_shift_unknown_constant
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγirr : Irrational (γ ^ 2)) (hμ : 0 < μ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hSeed : HasDualCrossing P X M γ μ) :
    HasDualReflectionShift P X M γ μ := by
  have hShiftGluing := fun η hη =>
    structureConstant_reflected_shift_and_gluing P X M γ μ η hγ hγ2 hμ hη hX hM
  obtain ⟨B, Z, hproj, hBd, h, hh, R, hRm, hRv, hshift⟩ :=
    reflectionR_first_shift_meromorphic P X M γ μ hγ hγ2 hμ hX hM
  obtain ⟨B₅, Z₅, -, hB₅, h₅, hh₅, R₅, hR₅m, hR₅v, hinv⟩ :=
    reflectionR_inversion_meromorphic_of_reflected_shift_and_gluing P X M γ μ hγ hγ2 hμ hX hM hShiftGluing
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hγh := half_gamma_lt_two_div hγ hγ2
  have hγc : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ.ne'
  have hRγ := analyticAt_reflection_gamma P X M hγ hγ2 hμ hγirr hX hM hh hRm hBd hRv
  have hev := dualShift_eventually P X M hγ hγ2 hγirr hμ hX hM hSeed hShiftGluing hh hRm hBd hRv hshift
    hRγ hh₅ hR₅m hB₅ hR₅v hinv
  set cγ : ℂ := (γ : ℂ) ^ 2 / 4 * (μ * Real.pi : ℂ) * R γ with hcγ
  set D : ℂ → ℂ := fun z => reflectionDualShiftDenom γ z with hD
  set G : ℂ → ℂ := fun z => -cγ * R (z + ((2 / γ : ℝ) : ℂ)) / D z with hG
  have hGm : MeromorphicOn G (horizontalStrip h) := by
    intro z hz
    have hRs := MeromorphicOn.comp_add_ofReal (h := h) hRm (2 / γ) z hz
    have hDm : MeromorphicAt D z :=
      ((meromorphicAt_lFun_comp' analyticAt_const).fun_mul
        (meromorphicAt_lFun_comp' (f := fun w : ℂ => 2 * w / γ) (by fun_prop))).fun_mul
        (meromorphicAt_lFun_comp' (f := fun w : ℂ => 2 + 4 / (γ : ℂ) ^ 2 - 2 * w / γ)
          (by fun_prop))
    exact ((MeromorphicAt.const _ z).fun_mul hRs).fun_div hDm
  -- frequent agreement near `3γ/8`
  have hfreq : ∃ᶠ z in 𝓝[≠] ((γ / 2 - γ / 8 : ℝ) : ℂ), R z = G z := by
    have ht := tendsto_affine_nhdsNE (z₀ := ((γ / 2 - γ / 8 : ℝ) : ℂ)) (a := -1) (by norm_num)
    refine ht.frequently (Eventually.frequently ?_)
    filter_upwards [hev] with u hu
    have e : ((γ / 2 - γ / 8 : ℝ) : ℂ) + (u : ℂ) * (-1) = ((γ / 2 - (γ / 8 + u) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e, hu]
    simp only [hG, hD, hcγ]
    push_cast
    ring
  have hrel : ∀ w ∈ horizontalStrip h, ∀ᶠ z in 𝓝[≠] w,
      R (z + ((0 : ℝ) : ℂ)) = (fun z => -cγ / D z) z * R (z + ((2 / γ : ℝ) : ℂ)) := by
    intro w hw
    have hg := ShiftGluing.meromorphicOn_eventuallyEq_of_frequently hRm hGm
      (isPreconnected_horizontalStrip h) (ofReal_mem_horizontalStrip hh _) hw hfreq
    filter_upwards [hg] with z hz
    rw [Complex.ofReal_zero, add_zero, hz]
    simp only [hG]
    ring
  have hcut := cutoff_relation_codiscrete hh 0 (2 / γ) hrel
  have hRt : ∀ x : ℝ, cutoffStrip (h / 2) R (x : ℂ) = R x := fun x =>
    cutoffStrip_of_lt (by simp only [Complex.ofReal_im, abs_zero]; positivity)
  refine ⟨B, Z, hproj, hBd, h / 2, half_pos hh, cutoffStrip (h / 2) R,
    meromorphicOn_cutoffStrip hRm (half_le_self hh.le), fun α h1 h2 => by rw [hRt]; exact hRv α h1 h2,
    (γ : ℂ) ^ 2 / 4 * (μ * Real.pi : ℂ) * cutoffStrip (h / 2) R γ, ?_, rfl, ?_⟩
  · rw [hRt, hRv γ (by linarith) (by linarith)]
    have hR0 := reflectionR_gamma_ne_zero P (μ := μ) hγ hγ2 hμ hγirr (hBd γ (by linarith)
      (by linarith))
    refine mul_ne_zero (mul_ne_zero (div_ne_zero (pow_ne_zero 2 hγc) (by norm_num)) ?_)
      (Complex.ofReal_ne_zero.mpr hR0)
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hμ.ne')
      (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')
  · filter_upwards [hcut] with z hz
    rw [Complex.ofReal_zero, add_zero] at hz
    rw [hz, hRt]
    simp only [hD, hcγ]
    push_cast
    ring

end DOZZ.Proofs

end
