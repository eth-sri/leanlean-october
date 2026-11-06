/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.OffCenterWickCopy
public import DOZZ.GMC.Moments.InversionSpatialLaw

/-! Pin-copy Wick integral laws over the actual finite spatial reference measure. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Wick normalization gives integrable sections over any finite spatial reference. -/
theorem ae_integrable_wick_finite
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Nonempty S]
    {P : Measure Ω} [IsProbabilityMeasure P] (ν : FiniteMeasure S)
    (W : Ω → S → ℝ) (v : S → ℝ≥0) w γ
    (hW : Measurable (fun p : Ω × S => W p.1 p.2))
    (hv : Measurable v) (hw : Measurable w)
    (hLaw : ∀ x, HasLaw (fun ω => W ω x) (gaussianReal 0 (v x)) P)
    (hw0 : ∀ x, 0 ≤ w x) (hwi : Integrable w (ν : Measure S)) :
    ∀ᵐ ω ∂P, Integrable (fun x => w x * Real.exp (γ*W ω x-γ^2/2*v x)) (ν : Measure S) := by
  have hmeasure := congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) ν.self_eq_mass_smul_normalize
  by_cases hm : ν.mass = 0
  · rw [hmeasure, hm, zero_smul]
    exact ae_of_all _ fun ω => integrable_zero_measure
  · have hwi' : Integrable w (ν.normalize : Measure S) := by
      rw [hmeasure] at hwi
      exact (integrable_smul_measure (ENNReal.coe_ne_zero.mpr hm) ENNReal.coe_ne_top).mp hwi
    filter_upwards [(ae_integrable_weighted_wick_sections (ν.normalize : Measure S) W v w γ hW hv hw hLaw hw0 hwi')] with ω hω
    rw [hmeasure]
    exact (integrable_smul_measure (ENNReal.coe_ne_zero.mpr hm) ENNReal.coe_ne_top).mpr hω

/-- The entire finite vector of copied Wick integrals has the original field's law. -/
theorem offCenter_wick_copy_finite_law
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Nonempty S]
    (P : Measure Ω) X Xc
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun q : Ω × (ℂ × ℝ) => Xc q.1 q.2.1 q.2.2))
    z (hz : 2 ≤ ‖z‖) (ν : FiniteMeasure S)
    p (hp : Measurable p) γ
    {m} (w : Fin m → S → ℝ) (hw : ∀ j, Measurable (w j))
    (hw0 : ∀ j x, 0 ≤ w j x) (hwi : ∀ j, Integrable (w j) (ν : Measure S)) :
    P.map (fun ω j => ∫ x, w j x * Real.exp
      (γ * Xc ω (z + (p x).val.1) (p x).val.2 - γ ^ 2 / 2 *
        ((p x).val.2 + 2 * Real.log ‖z + (p x).val.1‖).toNNReal) ∂(ν : Measure S)) =
    (P.prod P).map (fun q j => ∫ x, w j x * Real.exp
      (γ * copiedCircle Xc z q (p x) - γ ^ 2 / 2 *
        ((p x).val.2 + 2 * Real.log ‖z + (p x).val.1‖).toNNReal) ∂(ν : Measure S)) := by
  let : IsProbabilityMeasure P := hX.1
  let U : Ω → S → ℝ := fun ω x => Xc ω (z + (p x).val.1) (p x).val.2
  let V : Ω × Ω → S → ℝ := fun q x => copiedCircle Xc z q (p x)
  let v : S → ℝ≥0 := fun x => ((p x).val.2 + 2 * Real.log ‖z + (p x).val.1‖).toNNReal
  have hpv := measurable_subtype_coe.comp hp
  have hU : Measurable (fun q : Ω × S => U q.1 q.2) :=
    hm.comp (measurable_fst.prodMk
      ((measurable_const.add (hpv.fst.comp measurable_snd)).prodMk
        (hpv.snd.comp measurable_snd)))
  have hV : Measurable (fun q : (Ω × Ω) × S => V q.1 q.2) := by
    unfold V copiedCircle
    have h1 : Measurable (fun q : (Ω × Ω) × S => Xc q.1.1 z 0) :=
      hm.comp (measurable_fst.fst.prodMk (measurable_const (a := (z, (0 : ℝ)))))
    have h2 : Measurable (fun q : (Ω × Ω) × S => Xc q.1.2 z 0) :=
      hm.comp (measurable_fst.snd.prodMk (measurable_const (a := (z, (0 : ℝ)))))
    exact (h2.add ((hU.comp ((measurable_fst.fst).prodMk measurable_snd)).sub h1)).add ((show Measurable (fun q : (Ω × Ω) × S => localPinCoefficient z (p q.2).val.1) by unfold localPinCoefficient; fun_prop).mul (h2.sub h1))
  have hv : Measurable v := by
    dsimp [v]
    fun_prop
  let φ : Fin m → S → ℝ → ℝ := fun j x t => w j x * Real.exp (γ*t-γ^2/2*v x)
  exact spatialIntegral_vector_law_of_fdd_finite ν U V φ hU hV (fun j => by exact ((hw j).comp measurable_fst).mul ((measurable_snd.const_mul γ).sub ((hv.comp measurable_fst).coe_nnreal_real.const_mul _)).exp)
    (fun j => ae_integrable_wick_finite ν U v (w j) γ hU hv (hw j)
      (fun x => offCenter_circle_hasLaw P X Xc hX hc z hz (p x))
      (hw0 j) (hwi j))
    (fun j => ae_integrable_wick_finite ν V v (w j) γ hV hv (hw j)
      (fun x => copied_circle_hasLaw P X Xc hX hc hm z hz (p x))
      (hw0 j) (hwi j))
    (fun r xs => copied_circle_fdd_law P X Xc hX hc hm z hz
      (fun i => p (xs i)))


end DOZZ.Proofs
