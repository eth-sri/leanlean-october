/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionAdmissibleLaw
public import DOZZ.GMC.Moments.ReferenceFinite

/-! Inversion invariance of arbitrary GMC test vectors on annular charts. -/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Distributions ENNReal

namespace DOZZ.Proofs

/-- Every finite vector of compact annular test integrals of an arbitrary GMC has the same
law after inversion. No preferred version of the chaos is used. -/
theorem gmc_inversion_annular_test_vector_law
    {Ω : Type*} [MeasurableSpace Ω] {k}
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    γ (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    U (hUopen : IsOpen U) {m R} (hm : 0 < m) (hR : 0 ≤ R)
    (hU : ∀ x ∈ U, 2 * m ≤ ‖x‖ ∧ ‖x‖ ≤ R)
    (f : Fin k → BoundedContinuousFunction ℂ ℝ)
    (hfc : ∀ j, HasCompactSupport (f j : ℂ → ℝ))
    (hfU : ∀ j, tsupport (f j : ℂ → ℝ) ⊆ U) :
    P.map (fun ω j => ∫ x, f j x ∂(M ω).map (fun z : ℂ => z⁻¹)) =
      P.map (fun ω j => ∫ x, f j x ∂M ω) := by
  let : IsProbabilityMeasure P := hX.1
  obtain ⟨Xc, hXc, _hconv⟩ := hM.2
  obtain ⟨g, hg, Z, N, hgap, hmem, hlim, hZ, hN, hNae⟩ :=
    isGMCOf_inversion_annular_version P X hX γ hγ hγ2 M hM Xc hXc U hUopen hm hR hU
  obtain ⟨A, hA, _hAfin, hAae⟩ :=
    isGMCOf_restrict_admissible_version P X hX γ hγ hγ2 M hM Xc hXc U hUopen
  let : IsFiniteMeasure gmcReferenceMeasure := ⟨lt_top_iff_ne_top.mpr gmcReferenceMeasure_univ_ne_top⟩
  let : IsFiniteMeasure (logRegularizationReference U (fun x => normPlus x ^ (-4 : ℝ))) := by
    rw [(show logRegularizationReference U (fun x => normPlus x ^ (-4 : ℝ)) = gmcReferenceMeasure.restrict U by rw [logRegularizationReference_restrict_of_subset univ U (fun x => normPlus x ^ (-4 : ℝ)) hUopen.measurableSet (subset_univ _)]; simp only [logRegularizationReference, Measure.restrict_univ, gmcReferenceMeasure])]
    infer_instance
  have heq (μ : Measure ℂ) (j : Fin k) := integral_restrict_eq_integral_of_zero_on_compl μ U hUopen.measurableSet (f j)
      (boundedContinuousFunction_eq_zero_off_tsupport_subset (f j) U (hfU j))
  have hright : (fun ω j => ∫ x, f j x ∂A ω) =ᵐ[P] fun ω j => ∫ x, f j x ∂M ω := by
    filter_upwards [hAae] with ω hω
    funext j
    rw [← hω, heq]
  exact (Measure.map_congr (by filter_upwards [hNae] with ω hω; funext j; rw [hω, heq])).symm.trans ((admissibleLogChaos_limit_vector_law_of_fdd P P U (fun x => normPlus x ^ (-4 : ℝ)) (min (m / 2) 1) 1 (fun ω ε x => Z ω x (Real.log (1 / ε))) (fun ω ε x => Xc ω x (Real.log (1 / ε))) hZ (isCircleAverage_admissible P X hX Xc hXc U hUopen) γ N A hN hA (fun ε (_hε : 0 < ε) (_hεb : ε ≤ min (min (m / 2) 1) 1) n (xs : Fin n → ℂ) => by exact inversionCircle_fdd_law P X hX P X hX Xc hXc (fun i => (xs i, Real.log (1 / ε))) (fun i ω => Z ω (xs i) (Real.log (1 / ε))) (fun i => hmem _ _) (fun i => g (xs i, Real.log (1 / ε))) (fun i => hg _) (fun i => hgap _) (fun i => hlim _)) f hfc hfU).trans (Measure.map_congr hright))

end DOZZ.Proofs
