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

section
variable {Ω : Type*} [MeasurableSpace Ω]

private theorem twoSidedReflectionMass_pos_of_Ioc_mass_pos
    (γ : ℝ) (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (ω : Ω) (hZ : 0 < Z ω (Set.Ioc 0 1)) :
    0 < twoSidedReflectionMass γ B Z ω := by
  let I : Set ℝ := Set.Ioc 0 1
  let f  := fun s =>
    ENNReal.ofReal (Real.exp (γ * twoSidedConditionedValue B ω s))
  let K : Set ℝ≥0 := Set.Icc 0 1
  let g  := fun t => γ * (B ω).1 t
  have hg : Continuous g := by fun_prop
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (by norm_num : (0 : ℝ≥0) ≤ 1)) hg.continuousOn
  let c₀  := ENNReal.ofReal (Real.exp (g s₀))
  have hc₀ : 0 < c₀ := ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hlower : ∀ s ∈ I, c₀ ≤ f s := by
    intro s hs
    have hs0  := hs.1
    let t : ℝ≥0 := ⟨s, hs0.le⟩
    have htK : t ∈ K := by
      refine ⟨t.property, ?_⟩
      exact_mod_cast hs.2
    have hvalue : twoSidedConditionedValue B ω s = (B ω).1 t := by
      simp [twoSidedConditionedValue, t, hs0.le]
    have hExp  :=
      Real.exp_le_exp.mpr (hmin htK)
    change ENNReal.ofReal (Real.exp (g s₀)) ≤
      ENNReal.ofReal (Real.exp (γ * twoSidedConditionedValue B ω s))
    rw [hvalue]
    exact ENNReal.ofReal_le_ofReal hExp
  have hset : c₀ * Z ω I ≤ ∫⁻ s in I, f s ∂Z ω := by
    calc
      c₀ * Z ω I = ∫⁻ s in I, c₀ ∂Z ω := by rw [setLIntegral_const]
      _ ≤ ∫⁻ s in I, f s ∂Z ω := by
        apply setLIntegral_mono' measurableSet_Ioc
        assumption
  have hIpos  :=
    lt_of_lt_of_le (ENNReal.mul_pos (ne_of_gt hc₀) (ne_of_gt hZ)) hset
  have hfull : twoSidedReflectionMass γ B Z ω = ∫⁻ s, f s ∂Z ω := rfl
  have hle : (∫⁻ s in I, f s ∂Z ω) ≤ ∫⁻ s, f s ∂Z ω := by
    rw [← lintegral_indicator measurableSet_Ioc]
    apply lintegral_mono
    intro s
    by_cases hs : s ∈ I
    · simp [I, hs]
    · simp [I, hs]
  rw [hfull]
  exact lt_of_lt_of_le hIpos hle

/-- Positive interval intensity implies a positive reflection moment of every positive order. -/
theorem twoSidedReflectionMoment_pos_of_lateralIntensity
    (P : Measure Ω) (γ p : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hZmeas : AEMeasurable Z P)
    (hMassMeas : AEMeasurable (fun ω => twoSidedReflectionMass γ B Z ω) P)
    (hIntensity : 0 < ∫⁻ ω, Z ω (Set.Ioc 0 1) ∂P)
    (hp : 0 < p) :
    0 < ∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ B Z ω) p ∂P := by
  let V : Ω → ℝ≥0∞ := fun ω => Z ω (Set.Ioc 0 1)
  have hV : AEMeasurable V P :=
    (Measure.measurable_coe measurableSet_Ioc).comp_aemeasurable hZmeas
  let Vm : Ω → ℝ≥0∞ := hV.mk V
  have hVm : Measurable Vm := hV.measurable_mk
  have hVtoVm : V =ᵐ[P] Vm := hV.ae_eq_mk
  let S : Set Ω := {ω | 0 < Vm ω}
  have hSmeas : MeasurableSet S := measurableSet_lt measurable_const hVm
  have hVint : 0 < ∫⁻ ω, Vm ω ∂P := by
    rw [← lintegral_congr_ae hVtoVm]
    exact hIntensity
  have hsuppV : Function.support Vm = S := by
    ext ω
    simp [Function.mem_support, S, pos_iff_ne_zero]
  have hSpos : 0 < P S := by
    rw [← hsuppV]
    exact (lintegral_pos_iff_support hVm).mp hVint
  exact let F := fun ω => (twoSidedReflectionMass γ B Z ω).rpow p;
  have hF := Measurable.comp_aemeasurable (Continuous.measurable ENNReal.continuous_rpow_const) hMassMeas;
  let Fm := AEMeasurable.mk F hF;
  have hFm := AEMeasurable.measurable_mk hF;
  have hFtoFm := AEMeasurable.ae_eq_mk hF;
  have hSsupport :=
    Filter.mp_mem hFtoFm
      (Filter.mp_mem hVtoVm
        (Filter.univ_mem'
          (id fun ω hVω hFω hSω =>
            have hVpositive := Eq.mpr (id (congrArg (fun _a => 0 < _a) hVω)) hSω;
            have hMasspositive := twoSidedReflectionMass_pos_of_Ioc_mass_pos γ B Z ω hVpositive;
            have hFpositive := ENNReal.rpow_pos_of_nonneg hMasspositive (le_of_lt hp);
            id (Eq.mpr (id (congrArg (fun _a => _a ≠ 0) (Eq.symm hFω))) (ne_of_gt hFpositive)))));
  have hFsupportPositive := lt_of_lt_of_le hSpos (measure_mono_ae hSsupport);
  have hFmint := (lintegral_pos_iff_support hFm).mpr hFsupportPositive;
  Trans.trans hFmint (Eq.symm (lintegral_congr_ae hFtoFm))

/-- For source-characterized reflection data, the lateral first-moment intensity already implies
strict positivity of the reflection coefficient whenever its defining moment is finite. The only
remaining hypothesis is the subcritical moment bound; it is not hidden in the source predicate. -/
theorem reflectionBarR_pos_of_reflectionData_of_moment_finite (P : Measure Ω) (γ α : ℝ)
    (hγ : 0 < γ) (_hγ2 : γ < 2) (hα : γ / 2 < α ∧ α < Q γ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α B Z)
    (hMoment : (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ B Z ω)
      (reflectionExponent γ α) ∂P) < ⊤) :
    0 < reflectionBarR P γ α B Z ∧
      (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ B Z ω)
        (reflectionExponent γ α) ∂P) < ⊤ := by
  rcases hData with ⟨hBrownian, hLateral, _hIndependent⟩
  rcases hBrownian with ⟨⟨hB₁, _hLaw₁⟩, ⟨hB₂, _hLaw₂⟩, _hIndependentSides⟩
  rcases hLateral with ⟨_hγpos, _hγlt, _hP, hZ, hZlocal, _hTranslation,
    _hReflection, hIntensity, _hSource⟩
  have hB  := hB₁.prodMk hB₂
  have hPair  := hB.prodMk hZ
  have hLocal : ∀ᵐ ω ∂P, LocallyFiniteOnTranslationWindows (Z ω) := by
    filter_upwards [hZlocal] with ω hω
    intro n
    apply hω
  have hMassInput := aemeasurable_reflectionMassInput_map_of_locallyFinite P γ
      (fun ω => (B ω, Z ω)) hPair hLocal
  have hMass : AEMeasurable (fun ω => twoSidedReflectionMass γ B Z ω) P := by
    apply hMassInput.comp_aemeasurable <;> assumption
  have hνhp := reflectionExponent_in_subcritical_range γ α hγ hα
  have hIntensityPos : 0 < ∫⁻ ω, Z ω (Set.Ioc 0 1) ∂P := by
    rw [hIntensity 0 1 (by norm_num)]
    positivity
  exact ⟨ENNReal.toReal_pos
      (ne_of_gt
        (twoSidedReflectionMoment_pos_of_lateralIntensity P γ (reflectionExponent γ α) B Z hZ hMass hIntensityPos
          hνhp.right.left))
      (LT.lt.ne hMoment),
    hMoment⟩

end

end DOZZ.Proofs

end
