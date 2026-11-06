/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitShiftLaw
public import DOZZ.Brownian.Lateral.UpperConditionedBlocks
public import DOZZ.Brownian.LateralTranslation
public import DOZZ.Statements.Brownian.TwoSidedReflectionCutMass
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The discarded reflection mass after a last-exit cut

The tail beyond the last visit to the barrier is a translated one-sided entrance mass. This is
the pathwise input to the last-cut moment estimate; no independence between the retained and
discarded masses is used.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The mass discarded by cutting the two-sided integral at the negative-side last exit. -/
noncomputable def twoSidedReflectionTailMass {Ω : Type*}
    (γ c : ℝ) (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ s in Iio (-((negativeLastExitTime (B ω).2 c : ℝ))),
    ENNReal.ofReal (Real.exp (γ * twoSidedConditionedValue B ω s)) ∂Z ω

/-- The full mass is the sum of the retained cut and the discarded tail. -/
theorem twoSidedReflectionMass_eq_cut_add_tail {Ω : Type*}
    γ c (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ) ω :
    twoSidedReflectionMass γ B Z ω =
      twoSidedReflectionCutMass γ c B Z ω + twoSidedReflectionTailMass γ c B Z ω := by
  let b := -((negativeLastExitTime (B ω).2 c : ℝ))
  let f : ℝ → ℝ≥0∞ := fun s =>
    ENNReal.ofReal (Real.exp (γ * twoSidedConditionedValue B ω s))
  have hcut : twoSidedReflectionCutMass γ c B Z ω = ∫⁻ s in Ici b, f s ∂Z ω := by
    unfold twoSidedReflectionCutMass
    rw [← lintegral_indicator measurableSet_Ici]
    apply lintegral_congr_ae
    exact ae_of_all _ fun s => by simp [f, b, Set.indicator]
  calc
    twoSidedReflectionMass γ B Z ω = ∫⁻ s, f s ∂Z ω := rfl
    _ = ∫⁻ s in Ici b, f s ∂Z ω + ∫⁻ s in (Ici b)ᶜ, f s ∂Z ω :=
      (lintegral_add_compl f measurableSet_Ici).symm
    _ = twoSidedReflectionCutMass γ c B Z ω + twoSidedReflectionTailMass γ c B Z ω := by
      rw [← hcut, ← (show twoSidedReflectionTailMass γ c B Z ω = ∫⁻ s in (Ici b)ᶜ, f s ∂Z ω by rw [show (Ici b)ᶜ = Iio b by ext s; simp]; rfl)]

/-- Reflect and shift the lateral measure so positive times measure distance past the cut. -/
noncomputable def lastExitReflectedMeasure {Ω : Type*}
    (c : ℝ) (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ) (ω : Ω) : Measure ℝ :=
  (Z ω).map (fun s => -s - (negativeLastExitTime (B ω).2 c : ℝ))

/-- Random translation by the last-exit time, followed by reflection, preserves the lateral law
and remains independent of the negative-side path. -/
theorem lastExitReflectedMeasure_law_independent
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) γ c
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable (fun ω => (B ω).2) P)
    (hZ : IsLateralGMCOf P γ Z)
    (hInd : IndepFun (fun ω => (B ω).2) Z P) :
    AEMeasurable (fun ω => lastExitReflectedMeasure c B Z ω) P ∧
      P.map (fun ω => lastExitReflectedMeasure c B Z ω) = P.map Z ∧
      IndepFun (fun ω => (B ω).2) (fun ω => lastExitReflectedMeasure c B Z ω) P := by
  let D : Ω → BrownianPath := fun ω => (B ω).2
  let T : BrownianPath → ℝ := fun p => (negativeLastExitTime p c : ℝ)
  let Y : Ω → Measure ℝ := fun ω => (Z ω).map (fun s => s + T (D ω))
  let R : Measure ℝ → Measure ℝ := fun μ => μ.map (fun s => -s)
  let M : Ω → Measure ℝ := fun ω => R (Y ω)
  have hY := lateralGMC_random_translation P γ Z hZ D hB hInd T (by change Measurable (fun p => (negativeLastExitTime p c : ℝ)); exact NNReal.continuous_coe.measurable.comp (measurable_negativeLastExitTime_joint.comp (measurable_const.prodMk measurable_id)))
  have hR : Measurable R := Measure.measurable_map _ (by fun_prop)
  have hcomp ω : M ω = lastExitReflectedMeasure c B Z ω := by
    dsimp [M, R, Y, D, T, lastExitReflectedMeasure]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext s
    simp only [Function.comp_apply]
    ring_nf
  have hsymm : (P.map Z).map R = P.map Z := by
    calc
      (P.map Z).map R = P.map (R ∘ Z) := by
        exact AEMeasurable.map_map_of_aemeasurable hR.aemeasurable hZ.2.2.2.1
      _ = P.map Z := by
        change P.map (fun ω => (Z ω).map (fun s => -s)) = P.map Z
        exact hZ.2.2.2.2.2.2.1
  have hMlaw : P.map M = P.map Z := by
    calc
      P.map M = (P.map Y).map R :=
        (AEMeasurable.map_map_of_aemeasurable hR.aemeasurable hY.1).symm
      _ = (P.map Z).map R := by rw [hY.2.1]
      _ = P.map Z := hsymm
  refine ⟨(hR.comp_aemeasurable hY.1).congr (Filter.Eventually.of_forall hcomp), ?_, ?_⟩
  · calc
      P.map (fun ω => lastExitReflectedMeasure c B Z ω) = P.map M :=
        Measure.map_congr (Filter.Eventually.of_forall fun ω => (hcomp ω).symm)
      _ = P.map Z := hMlaw
  · have hInd' : IndepFun D (fun ω => lastExitReflectedMeasure c B Z ω) P := by
      exact (hY.2.2.comp measurable_id hR).congr (Filter.Eventually.of_forall fun _ => rfl)
        (Filter.Eventually.of_forall hcomp)
    exact hInd'

/-- The post-last-exit negative-side path and reflected translated chaos have the same joint law
as the original negative-side path and lateral measure. This uses path-law preservation and the
independence of the lateral measure from the path; it asserts no independence between the cut and
discarded masses. -/
theorem postLastExit_reflectedJointLaw_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) ν γ c
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hB : IsNegativeConditionedBrownianProcess P (fun ω => (B ω).2) ν)
    (hν : 0 < ν) (hc : 0 < c) (hZ : IsLateralGMCOf P γ Z)
    (hInd : IndepFun B Z P) :
    P.map (fun ω =>
      (negativeConditionedPostLastExitPath c (B ω).2, lastExitReflectedMeasure c B Z ω)) =
      P.map (fun ω => ((B ω).2, Z ω)) := by
  let D : Ω → BrownianPath := fun ω => (B ω).2
  let U : Ω → BrownianPath := fun ω => negativeConditionedPostLastExitPath c (D ω)
  let M : Ω → Measure ℝ := fun ω => lastExitReflectedMeasure c B Z ω
  let : IsProbabilityMeasure P := hZ.2.2.1
  have hD := hB.1
  have hUlaw : P.map U = P.map D := by
    change P.map (negativeConditionedPostLastExitPath c ∘ D) = P.map D
    calc
      P.map (negativeConditionedPostLastExitPath c ∘ D) =
          (P.map D).map (negativeConditionedPostLastExitPath c) :=
        (AEMeasurable.map_map_of_aemeasurable
          (measurable_negativeConditionedPostLastExitPath c).aemeasurable hD).symm
      _ = P.map D := (negativeConditioned_postLastExit_law ν c hν hc (P.map D) hB.2).2
  have hIndDZ : IndepFun D Z P := hInd.comp measurable_snd measurable_id
  have hTrans := lastExitReflectedMeasure_law_independent P γ c B Z hD hZ hIndDZ
  calc
    P.map (fun ω => (negativeConditionedPostLastExitPath c (B ω).2,
        lastExitReflectedMeasure c B Z ω)) = P.map (fun ω => (U ω, M ω)) := by
          rfl
    _ = (P.map U).prod (P.map M) := ((indepFun_iff_map_prod_eq_prod_map_map ((measurable_negativeConditionedPostLastExitPath c).comp_aemeasurable hD) hTrans.1).1 (hTrans.2.2.comp (measurable_negativeConditionedPostLastExitPath c) measurable_id))
    _ = (P.map D).prod (P.map Z) := by rw [hUlaw, hTrans.2.1]
    _ = P.map (fun ω => ((B ω).2, Z ω)) := ((indepFun_iff_map_prod_eq_prod_map_map hD hZ.2.2.2.1).1 hIndDZ).symm

/-- Changing variables from the discarded negative half-line to positive time gives the entrance
mass of the post-last-exit path, with the exact factor `exp (-γ c)`. -/
theorem twoSidedReflectionTailMass_eq_postLastExit_entranceMass {Ω : Type*}
    γ c (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ) ω :
    twoSidedReflectionTailMass γ c B Z ω =
      ENNReal.ofReal (Real.exp (-γ * c)) *
        positiveLateralMass γ (negativeConditionedPostLastExitPath c (B ω).2)
          (lastExitReflectedMeasure c B Z ω) := by
  let τ : ℝ := (negativeLastExitTime (B ω).2 c : ℝ)
  let g : ℝ → ℝ := fun s => -s - τ
  let φ : ℝ → ℝ≥0∞ := fun u =>
    ENNReal.ofReal (Real.exp (γ * (negativeConditionedPostLastExitPath c (B ω).2
      (Real.toNNReal u))))
  have hg : Measurable g := by fun_prop
  have hφ : Measurable φ := by
    unfold φ
    fun_prop
  have hpre : g ⁻¹' Ioi (0 : ℝ) = Iio (-τ) := by
    ext s
    simp only [mem_preimage, mem_Ioi, mem_Iio, g]
    constructor <;> intro h <;> linarith
  have hval s (hs : s ∈ Iio (-τ)) :
      ENNReal.ofReal (Real.exp (γ * twoSidedConditionedValue B ω s)) =
        ENNReal.ofReal (Real.exp (-γ * c)) * φ (g s) := by
    have hs0 : s < 0 := by
      have : 0 ≤ τ := by dsimp [τ]; exact (negativeLastExitTime (B ω).2 c).2
      dsimp [Iio] at hs
      linarith
    have htime : τ + Real.toNNReal (g s) = -s := by
      rw [(Real.coe_toNNReal _ (show 0 < g s by simpa [mem_preimage, mem_Ioi] using (show s ∈ g ⁻¹' Ioi (0 : ℝ) by rw [hpre]; exact hs)).le)]
      dsimp [g]
      ring
    have harg : negativeLastExitTime (B ω).2 c + Real.toNNReal (g s) =
        (⟨-s, by linarith⟩ : ℝ≥0) := by
      apply Subtype.ext
      change (negativeLastExitTime (B ω).2 c : ℝ) +
        (Real.toNNReal (g s) : ℝ) = -s
      rw [show (negativeLastExitTime (B ω).2 c : ℝ) = τ by rfl, htime]
    rw [(show twoSidedConditionedValue B ω s = (B ω).2 ⟨-s, by linarith⟩ by simp [twoSidedConditionedValue, not_le.mpr hs0])]
    change ENNReal.ofReal (Real.exp (γ * (B ω).2 ⟨-s, by linarith⟩)) =
      ENNReal.ofReal (Real.exp (-γ * c)) *
        ENNReal.ofReal (Real.exp (γ *
          negativeConditionedPostLastExitPath c (B ω).2 (Real.toNNReal (g s))))
    rw [(show negativeConditionedPostLastExitPath c (B ω).2 (Real.toNNReal (g s)) = (B ω).2 ⟨-s, by linarith⟩ + c by change (B ω).2 (negativeLastExitTime (B ω).2 c + Real.toNNReal (g s)) + c = _; rw [harg])]
    rw [(show Real.exp (γ * ((B ω).2 ⟨-s, by linarith⟩)) = Real.exp (-γ * c) * Real.exp (γ * ((B ω).2 ⟨-s, by linarith⟩ + c)) by rw [show γ * (B ω).2 ⟨-s, by linarith⟩ = (-γ * c) + γ * ((B ω).2 ⟨-s, by linarith⟩ + c) by ring, Real.exp_add]), ENNReal.ofReal_mul (Real.exp_nonneg _)]
  have hmap : ∫⁻ u in Ioi (0 : ℝ), φ u ∂(Z ω).map g =
      ∫⁻ s in Iio (-τ), φ (g s) ∂Z ω := by
    calc
      _ = ∫⁻ s in g ⁻¹' Ioi (0 : ℝ), φ (g s) ∂Z ω :=
        setLIntegral_map measurableSet_Ioi hφ hg
      _ = _ := by rw [hpre]
  change ∫⁻ s in Iio (-τ),
      ENNReal.ofReal (Real.exp (γ * twoSidedConditionedValue B ω s)) ∂Z ω = _
  calc
    _ = ∫⁻ s in Iio (-τ),
        ENNReal.ofReal (Real.exp (-γ * c)) * φ (g s) ∂Z ω := by
          apply setLIntegral_congr_fun measurableSet_Iio
          intro s hs
          exact hval s hs
    _ = ENNReal.ofReal (Real.exp (-γ * c)) *
        ∫⁻ s in Iio (-τ), φ (g s) ∂Z ω := by
          calc
            _ = ∫⁻ s, ENNReal.ofReal (Real.exp (-γ * c)) *
                (Iio (-τ)).indicator (φ ∘ g) s ∂Z ω := by
                  rw [← lintegral_indicator measurableSet_Iio]
                  apply lintegral_congr
                  intro s
                  by_cases hs : s ∈ Iio (-τ) <;> simp [hs]
            _ = ENNReal.ofReal (Real.exp (-γ * c)) *
                ∫⁻ s, (Iio (-τ)).indicator (φ ∘ g) s ∂Z ω :=
                  lintegral_const_mul _ ((hφ.comp hg).indicator measurableSet_Iio)
            _ = _ := by
              rw [lintegral_indicator measurableSet_Iio]
              simp only [Function.comp_apply]
    _ = ENNReal.ofReal (Real.exp (-γ * c)) *
        ∫⁻ u in Ioi (0 : ℝ), φ u ∂(Z ω).map g := by
          congr 1
          exact hmap.symm
    _ = ENNReal.ofReal (Real.exp (-γ * c)) *
        positiveLateralMass γ (negativeConditionedPostLastExitPath c (B ω).2)
        (lastExitReflectedMeasure c B Z ω) := by
          rw [positiveLateralMass, lastExitReflectedMeasure]

/-- The subunit-power increment is controlled by the derivative at the left endpoint. This is
the pointwise estimate used with the inverse moment of the retained cut mass. -/
theorem real_rpow_add_increment_le_subunit (x d p : ℝ)
    (hx : 0 < x) (hd : 0 ≤ d) (hp : 0 < p) (hp1 : p ≤ 1) :
    (x + d) ^ p - x ^ p ≤ p * d * x ^ (p - 1) := by
  let t := d / x
  have := div_nonneg hd hx.le
  calc
    (x + d) ^ p - x ^ p ≤ x ^ p * (1 + p * t) - x ^ p := by
      rw [(show (x + d) ^ p = x ^ p * (1 + t) ^ p by rw [(show x + d = x * (1 + t) by dsimp [t]; field_simp [hx.ne']), Real.mul_rpow hx.le (by positivity)])]
      exact sub_le_sub_right (mul_le_mul_of_nonneg_left (rpow_one_add_le_one_add_mul_self (p := p) (by linarith) hp.le hp1)
        (Real.rpow_nonneg hx.le p)) _
    _ = p * d * x ^ (p - 1) := by
      rw [Real.rpow_sub hx p 1]
      dsimp [t]
      field_simp [hx.ne']
      simp only [Real.rpow_one]
      ring

/-- The superunit-power increment is controlled by the derivative at the right endpoint. This is
the pointwise estimate used with a positive moment of the full reflection mass. -/
theorem real_rpow_add_increment_le_superunit (x d p : ℝ)
    (hx : 0 < x) (hd : 0 ≤ d) (hp1 : 1 ≤ p) :
    (x + d) ^ p - x ^ p ≤ p * d * (x + d) ^ (p - 1) := by
  let y := x + d
  let t := d / y
  have hy : 0 < y := by dsimp [y]; linarith
  have := div_nonneg hd hy.le
  have : t ≤ 1 := by
    dsimp [t, y]
    rw [div_le_one hy]
    linarith
  have hxform : x = y * (1 - t) := by
    dsimp [t, y]
    field_simp [ne_of_gt hy]
    ring
  have hbern' : 1 - p * t ≤ (1 - t) ^ p := by
    calc
      1 - p * t = 1 + p * (-t) := by ring
      _ ≤ (1 + (-t)) ^ p := (one_add_mul_self_le_rpow_one_add (p := p) (by linarith) hp1)
      _ = (1 - t) ^ p := by
        congr 1
  calc
    (x + d) ^ p - x ^ p = y ^ p - x ^ p := by rfl
    _ ≤ y ^ p - y ^ p * (1 - p * t) := (sub_le_sub_left (by rw [(show x ^ p = y ^ p * (1 - t) ^ p by rw [hxform, Real.mul_rpow hy.le (by linarith)])]; exact mul_le_mul_of_nonneg_left hbern' (Real.rpow_nonneg hy.le p)) _)
    _ = p * d * y ^ (p - 1) := by
      rw [Real.rpow_sub hy p 1]
      dsimp [t]
      field_simp [ne_of_gt hy]
      simp only [Real.rpow_one]
      ring

end DOZZ.Proofs

end
