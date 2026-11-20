/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.IndependentRegroup
public import DOZZ.FourPoint.Reflected.CopiedPolarTransport
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
/-! Signed expectations under the joint source Williams law. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- A measurable signed expectation is transported by the joint law, with both source
and reference observables explicitly measurable. -/
theorem dual_copied_joint_law_integral
    {Ω Λ ζ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ] [MeasurableSpace ζ]
    (P : Measure Ω) (R : Measure Λ) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (Y : Ω → ζ) (hY : AEMeasurable Y P) (V : Ω × Ω → ℝ≥0∞)
    (hV : AEMeasurable V (P.prod P)) (J : Λ → ℝ≥0∞) (hJ : AEMeasurable J R)
    (hLaw : (P.prod P).map (fun ω => (Y ω.1,V ω)) = (P.map Y).prod (R.map J))
    (G : ζ × ℝ≥0∞ → ℝ) (hG : Measurable G) :
    (∫ ω : Ω × Ω, G (Y ω.1,V ω) ∂P.prod P) =
      ∫ ω : Ω × Λ, G (Y ω.1,J ω.2) ∂P.prod R := by
  have hs : AEMeasurable (fun ω : Ω × Ω => (Y ω.1,V ω)) (P.prod P) := hY.comp_fst.prodMk hV
  have hr : AEMeasurable (fun ω : Ω × Λ => (Y ω.1,J ω.2)) (P.prod R) := hY.comp_fst.prodMk hJ.comp_snd
  rw [← map_prod_of_aemeasurable P R Y J hY hJ] at hLaw
  rw [← integral_map hs hG.aestronglyMeasurable,
    ← integral_map hr hG.aestronglyMeasurable, hLaw]

end DOZZ.Proofs
