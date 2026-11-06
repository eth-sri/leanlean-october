/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ReflectionMassMeasurability
public import DOZZ.Brownian.ReflectionExponentBounds
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Order.Compact

/-!
# Positivity of reflection moments from lateral intensity

Positive lateral intensity on one bounded interval gives positive probability of nonzero interval
mass. The Brownian exponential weight is strictly positive at every point, so the two-sided mass,
and each positive power of it, is positive on a set of positive probability. This proves strict
positivity of the moment without assuming that the lateral interval mass is positive almost surely.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs



/-- For source-characterized reflection data, the lateral first-moment intensity already implies
strict positivity of the reflection coefficient whenever its defining moment is finite. The only
remaining hypothesis is the subcritical moment bound; it is not hidden in the source predicate. -/
theorem reflectionBarR_pos_of_reflectionData_of_moment_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) γ α
    (hγ : 0 < γ) (_hγ2 : γ < 2) (hα : γ / 2 < α ∧ α < Q γ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α B Z)
    (hMoment : (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ B Z ω)
      (reflectionExponent γ α) ∂P) < ⊤) :
    0 < reflectionBarR P γ α B Z ∧
      (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ B Z ω)
        (reflectionExponent γ α) ∂P) < ⊤ := by
  have twoSidedReflectionMoment_pos_of_lateralIntensity p (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ) (hZmeas : AEMeasurable Z P) (hMassMeas : AEMeasurable (fun ω => twoSidedReflectionMass γ B Z ω) P) (hIntensity : 0 < ∫⁻ ω, Z ω (Set.Ioc 0 1) ∂P) (hp : 0 < p) : 0 < ∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ B Z ω) p ∂P := by
    have twoSidedReflectionMass_pos_of_Ioc_mass_pos ω (hZ : 0 < Z ω (Set.Ioc 0 1)) : 0 < twoSidedReflectionMass γ B Z ω := by
      let I : Set ℝ := Set.Ioc 0 1
      let f : ℝ → ℝ≥0∞ := fun s =>
        ENNReal.ofReal (Real.exp (γ * twoSidedConditionedValue B ω s))
      let g : ℝ≥0 → ℝ := fun t => γ * (B ω).1 t
      obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn
        (nonempty_Icc.mpr (by norm_num : (0 : ℝ≥0) ≤ 1)) (show Continuous g by fun_prop).continuousOn
      let c₀ : ℝ≥0∞ := ENNReal.ofReal (Real.exp (g s₀))
      have hlower : ∀ s ∈ I, c₀ ≤ f s := by
        intro s hs
        have hs0 : 0 < s := hs.1
        let t : ℝ≥0 := ⟨s, hs0.le⟩
        have htK : t ∈ (Set.Icc 0 1) := by
          refine ⟨t.property, ?_⟩
          exact_mod_cast hs.2
        change ENNReal.ofReal (Real.exp (g s₀)) ≤
          ENNReal.ofReal (Real.exp (γ * twoSidedConditionedValue B ω s))
        rw [(show twoSidedConditionedValue B ω s = (B ω).1 t by simp [twoSidedConditionedValue, t, hs0.le])]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hmin htK))
      have hset : c₀ * Z ω I ≤ ∫⁻ s in I, f s ∂Z ω := by
        calc
          c₀ * Z ω I = ∫⁻ s in I, c₀ ∂Z ω := by rw [setLIntegral_const]
          _ ≤ ∫⁻ s in I, f s ∂Z ω := by
            apply setLIntegral_mono' measurableSet_Ioc
            intro s hs
            exact hlower s hs
      have hle : (∫⁻ s in I, f s ∂Z ω) ≤ ∫⁻ s, f s ∂Z ω := by
        rw [← lintegral_indicator measurableSet_Ioc]
        apply lintegral_mono
        intro s
        by_cases hs : s ∈ I
        · simp [I, hs]
        · simp [I, hs]
      rw [(rfl : twoSidedReflectionMass γ B Z ω = ∫⁻ s, f s ∂Z ω)]
      exact lt_of_lt_of_le (lt_of_lt_of_le (ENNReal.mul_pos (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))) (ne_of_gt hZ)) hset) hle
    let V : Ω → ℝ≥0∞ := fun ω => Z ω (Set.Ioc 0 1)
    have hV : AEMeasurable V P :=
      (Measure.measurable_coe measurableSet_Ioc).comp_aemeasurable hZmeas
    let Vm : Ω → ℝ≥0∞ := hV.mk V
    have hVtoVm : V =ᵐ[P] Vm := hV.ae_eq_mk
    let S : Set Ω := {ω | 0 < Vm ω}
    let F : Ω → ℝ≥0∞ := fun ω =>
      ENNReal.rpow (twoSidedReflectionMass γ B Z ω) p
    have hF : AEMeasurable F P := by
      exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hMassMeas
    let Fm : Ω → ℝ≥0∞ := hF.mk F
    have hFtoFm : F =ᵐ[P] Fm := hF.ae_eq_mk
    have hSsupport : ∀ᵐ ω ∂P, ω ∈ S → ω ∈ Function.support Fm := by
      filter_upwards [hVtoVm, hFtoFm] with ω hVω hFω
      intro hSω
      change Fm ω ≠ 0
      rw [← hFω]
      exact ne_of_gt (ENNReal.rpow_pos_of_nonneg (twoSidedReflectionMass_pos_of_Ioc_mass_pos ω (by simpa [V] using (show 0 < V ω by rw [hVω]; exact hSω))) (le_of_lt hp))
    calc
      0 < ∫⁻ ω, Fm ω ∂P := ((lintegral_pos_iff_support hF.measurable_mk).2 (lt_of_lt_of_le (by rw [← (show Function.support Vm = S by ext ω; simp [Function.mem_support, S, pos_iff_ne_zero])]; exact (lintegral_pos_iff_support hV.measurable_mk).mp (by rw [← lintegral_congr_ae hVtoVm]; exact hIntensity)) (measure_mono_ae hSsupport)))
      _ = ∫⁻ ω, F ω ∂P := (lintegral_congr_ae hFtoFm).symm
  rcases hData with ⟨hBrownian, hLateral, _hIndependent⟩
  rcases hBrownian with ⟨⟨hB₁, _hLaw₁⟩, ⟨hB₂, _hLaw₂⟩, _hIndependentSides⟩
  rcases hLateral with ⟨_hγpos, _hγlt, _hP, hZ, hZlocal, _hTranslation,
    _hReflection, hIntensity, _hSource⟩
  have hPair := (hB₁.prodMk hB₂).prodMk hZ
  have hLocal : ∀ᵐ ω ∂P, LocallyFiniteOnTranslationWindows (Z ω) := by
    filter_upwards [hZlocal] with ω hω
    intro n
    simpa [LocallyFiniteOnTranslationWindows, translationWindow] using
      hω (-(n : ℝ)) (n : ℝ)
  exact ⟨(by simpa [reflectionBarR] using (ENNReal.toReal_pos (ne_of_gt (twoSidedReflectionMoment_pos_of_lateralIntensity (reflectionExponent γ α) B Z hZ (by change AEMeasurable (fun ω => twoSidedReflectionMassInput γ (B ω, Z ω)) P; exact (aemeasurable_reflectionMassInput_map_of_locallyFinite P γ (fun ω => (B ω, Z ω)) hPair hLocal).comp_aemeasurable hPair) (by rw [hIntensity 0 1 (by norm_num)]; exact ENNReal.ofReal_pos.mpr (by positivity)) (reflectionExponent_in_subcritical_range γ α hγ hα).2.1)) hMoment.ne)), hMoment⟩

end DOZZ.Proofs

end
