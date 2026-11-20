/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionAdmissibleLaw
public import DOZZ.GMC.Moments.ReferenceFinite
public import DOZZ.GMC.Moments.InversionRadialCircleLaw

/-! Inversion invariance of arbitrary GMC test vectors on annular charts. -/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Distributions ENNReal

namespace DOZZ.Proofs

section
variable {Ω : Type*} [MeasurableSpace Ω] {k l : ℕ} (P : Measure Ω) (X : Ω → Distr)
  (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc) (γ : ℝ) (hγ : 0 < γ)
  (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
include Ω X hX hc γ hγ hγ2 hM

/-- Annular inversion of the actual GMC retains its joint law with the reversed
concentric source coordinates. -/
theorem gmc_inversion_annular_joint_test_vector_law
    (U : Set ℂ) (hUopen : IsOpen U) {m R : ℝ} (hm : 0 < m) (hR : 0 ≤ R)
    (hU : ∀ x ∈ U, 2 * m ≤ ‖x‖ ∧ ‖x‖ ≤ R)
    (s : Fin l → ℝ) (f : Fin k → BoundedContinuousFunction ℂ ℝ)
    (hfc : ∀ j, HasCompactSupport (f j : ℂ → ℝ))
    (hfU : ∀ j, tsupport (f j : ℂ → ℝ) ⊆ U) :
    P.map (fun ω => (fun i => Xc ω 0 (-s i), fun j => ∫ x, f j x ∂(M ω).map
      (fun z : ℂ => z⁻¹))) =
      P.map (fun ω => (fun i => Xc ω 0 (s i), fun j => ∫ x, f j x ∂M ω)) := by
  let  := hX.1
  obtain ⟨g, hg, Z, N, hgap, hmem, hlim, hZ, hN, hNae⟩ :=
    isGMCOf_inversion_annular_version P X hX γ hγ hγ2 M hM Xc hc U hUopen hm hR hU
  obtain ⟨A, hA, _hAfin, hAae⟩ :=
    isGMCOf_restrict_admissible_version P X hX γ hγ hγ2 M hM Xc hc U hUopen
  have hY := isCircleAverage_admissible P X hX Xc hc U hUopen
  let : IsFiniteMeasure gmcReferenceMeasure := ⟨lt_top_iff_ne_top.mpr gmcReferenceMeasure_univ_ne_top⟩
  have href : logRegularizationReference U (fun x => normPlus x ^ (-4 : ℝ)) =
      gmcReferenceMeasure.restrict U := by
    rw [logRegularizationReference_restrict_of_subset univ U
      (fun x => normPlus x ^ (-4 : ℝ)) hUopen.measurableSet (subset_univ _)]
    simp only [logRegularizationReference, Measure.restrict_univ, gmcReferenceMeasure]
  let : IsFiniteMeasure (logRegularizationReference U (fun x => normPlus x ^ (-4 : ℝ))) := by
    rw [href]; infer_instance
  let V := fun ω i => Xc ω 0 (-s i)
  let V' := fun ω i => Xc ω 0 (s i)
  have hV : Measurable V := measurable_pi_iff.mpr fun i =>
    (hc.1 (-s i)).comp (measurable_id.prodMk measurable_const)
  have hV' : Measurable V' := measurable_pi_iff.mpr fun i =>
    (hc.1 (s i)).comp (measurable_id.prodMk measurable_const)
  have hfdd ε (_hε : 0 < ε) (_hεb : ε ≤ min (min (m / 2) 1) 1) n (xs : Fin n → ℂ) := inversionCircle_radial_joint_fdd_law P X Xc hX hc Z g hg hgap hmem hlim
      s (fun i => (xs i, Real.log (1 / ε)))
  have hlaw := admissibleLogChaos_limit_joint_vector_law_of_fdd P P U
    (fun x => normPlus x ^ (-4 : ℝ)) (min (m / 2) 1) 1
    (fun ω ε x => Z ω x (Real.log (1 / ε)))
    (fun ω ε x => Xc ω x (Real.log (1 / ε))) hZ hY γ N A hN hA V V' hV hV' hfdd f hfc hfU
  have heq (μ : Measure ℂ) (j : Fin k)  :=
    integral_restrict_eq_integral_of_zero_on_compl μ U hUopen.measurableSet (f j)
      (boundedContinuousFunction_eq_zero_off_tsupport_subset (f j) U (hfU j))
  have hrestrict (V : Ω → Fin l → ℝ) {L L' : Ω → Measure ℂ}
      (h : L =ᵐ[P] (fun ω => (L' ω).restrict U)) :
      (fun ω => (V ω, fun j => ∫ x, f j x ∂L ω)) =ᵐ[P]
        (fun ω => (V ω, fun j => ∫ x, f j x ∂L' ω)) := by
    filter_upwards [h] with ω hω
    simp only [hω, heq]
  have hleft := hrestrict V hNae
  have hright := hrestrict V' (hAae.mono fun _ h => h.symm)
  exact (Measure.map_congr hleft).symm.trans (hlaw.trans (Measure.map_congr hright))

end

end DOZZ.Proofs
