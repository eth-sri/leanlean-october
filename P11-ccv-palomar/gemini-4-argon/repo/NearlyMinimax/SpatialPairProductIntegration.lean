module

public import NearlyMinimax.ExponentialSpatialKernels
public import Mathlib.Probability.Independence.Integration


@[expose] public section

/-! Actual independent spatial-coordinate projections and pair integrations. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- Scaling each genuine finite coordinate measure scales its product by the cardinal power. -/
theorem spatialPi_const_smul  [Fintype J] [MeasurableSpace E]
    (π : Measure E) [SigmaFinite π] (c : ℝ≥0∞) [SigmaFinite (c • π)] :
    Measure.pi (fun _ : J => c • π) = c^(Fintype.card J) • Measure.pi (fun _ : J => π) := by
  apply Measure.pi_eq (μ := fun _ => c • π)
  intro S hS
  rw [Measure.smul_apply, smul_eq_mul, Measure.pi_pi]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

/-- The actual uniform probability law on the source local cube. -/
def spatialPatchProbability (d ) : Measure (Covariate d) :=
  ((2 : ℝ≥0∞)^d)⁻¹ • volume.restrict (spatialPatchBox d)

instance spatialPatchProbability_isProbability (d : ℕ) : IsProbabilityMeasure (spatialPatchProbability d) := by
  constructor
  rw [spatialPatchProbability, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ, spatialPatchBox_volume]
  exact ENNReal.inv_mul_cancel (by positivity) (by finiteness)

/-- Genuine factorization of functions of two disjoint iid coordinate pairs. -/
theorem spatialPi_two_pair_functions_factor  [Fintype J] [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (q : Fin 4 ↪ J)
    (F : E × E → ℝ) (hF : Measurable F) :
    (∫ U : J → E, F (U (q 0), U (q 1)) * F (U (q 2), U (q 3))
      ∂Measure.pi (fun _ => π)) = (∫ xy, F xy ∂π.prod π)^2 := by
  have h_spatialPi_pair_integral (i) (j) (hij : i ≠ j) (F : E × E → ℝ) (hF : Measurable F) : (∫ U : J → E, F (U i, U j) ∂Measure.pi (fun _ => π)) = ∫ z, F z ∂π.prod π := by
    have h_spatialPi_pair_preserving : MeasurePreserving (fun U : J → E => (U i, U j))
        (Measure.pi (fun _ : J => π)) (π.prod π) := by
      let e : Fin 2 ↪ J := ⟨![i,j], by
        intro a b h
        fin_cases a <;> fin_cases b <;> simp_all⟩
      have h_spatialPi_projection_preserving {I} {J} [Fintype I] [Fintype J] (e : I ↪ J) : MeasurePreserving (fun U : J → E => fun i => U (e i))
          (Measure.pi (fun _ : J => π)) (Measure.pi (fun _ : I => π)) := by
        have hc : iIndepFun (fun j (U : J → E) => U j) (Measure.pi (fun _ : J => π)) :=
          iIndepFun_pi (X := fun _ => (id : E → E)) (fun _ => aemeasurable_id)
        have hs := iIndepFun.precomp e.injective hc
        refine ⟨measurable_pi_iff.mpr (fun i => measurable_pi_apply (e i)), ?_⟩
        simpa only [(measurePreserving_eval (fun _ => π) _).map_eq] using ((iIndepFun_iff_map_fun_eq_pi_map (fun i => (measurable_pi_apply (e i)).aemeasurable)).mp hs)
      convert (measurePreserving_finTwoArrow π).comp (h_spatialPi_projection_preserving e) using 1
      funext U
      simp [MeasurableEquiv.finTwoArrow, e]
    have hp := h_spatialPi_pair_preserving
    exact (integral_map hp.measurable.aemeasurable hF.aestronglyMeasurable).symm.trans
      (congrArg (fun μ => ∫ z, F z ∂μ) hp.map_eq)
  have hc : iIndepFun (fun j (U : J → E) => U j) (Measure.pi (fun _ => π)) :=
    iIndepFun_pi (X := fun _ => (id : E → E)) (fun _ => aemeasurable_id)
  have hne (i j : Fin 4) (h : i ≠ j) : q i ≠ q j := fun he => h (q.injective he)
  have hind0 := hc.indepFun_prodMk_prodMk (fun j => measurable_pi_apply j)
    (q 0) (q 1) (q 2) (q 3)
    (hne 0 2 (by decide)) (hne 0 3 (by decide))
    (hne 1 2 (by decide)) (hne 1 3 (by decide))
  have he := (hind0.comp hF hF).integral_mul_eq_mul_integral (hF.comp ((measurable_pi_apply (q 0)).prodMk (measurable_pi_apply (q 1)))).aestronglyMeasurable (hF.comp ((measurable_pi_apply (q 2)).prodMk (measurable_pi_apply (q 3)))).aestronglyMeasurable
  change (∫ U : J → E, F (U (q 0), U (q 1)) * F (U (q 2), U (q 3))
    ∂Measure.pi (fun _ => π)) = _ at he
  simp only [Function.comp_def] at he
  rw [h_spatialPi_pair_integral (q 0) (q 1) (hne 0 1 (by decide)) F hF,
    h_spatialPi_pair_integral (q 2) (q 3) (hne 2 3 (by decide)) F hF] at he
  simpa only [pow_two] using he

end NearlyMinimax
