module

public import NearlyMinimax.HighMarkedSpatialDesign
public import NearlyMinimax.HighConditionalScoreEnergy


@[expose] public section

/-! The actual complete marked periodic-frame generator in the genuine
normalized iid design/response experiment. The source overlap factor
3^d multiplies a derived factorial series of true Q^r numerator envelopes. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

section
variable {E : Type*} [MeasurableSpace E]

def highFrameFullMarkedScore {d k D : ℕ} (n : ℕ) [NeZero k]
    (π : HighWindowLabels d k → Measure E) (activation : HighWindowLabels d k → E → ℝ)
    (a V η : ℝ) (p : Covariate d → ℝ)
    (pReset : HighWindowLabels d k → E → Covariate d → ℝ)
    (cReset : HighWindowLabels d k → E → HighFrameVector d D)
    (c : HighWindowLabels d k → HighFrameVector d D)
    (z : IndexedSample d n) : ℝ :=
  ∑ j, highFrameMarkedScore π activation a V η (p ∘ z.1)
    (fun j e => pReset j e ∘ z.1) cReset c z.1 j z.2

variable (d k D n : ℕ) [NeZero k]

theorem highFrameFullMarkedScore_measurable
    (π : HighWindowLabels d k → Measure E) [∀ j, SFinite (π j)]
    {activation : HighWindowLabels d k → E → ℝ} (hAct : ∀ j, Measurable (activation j))
    (a V η : ℝ) {p : Covariate d → ℝ} (hp : Measurable p)
    {pReset : HighWindowLabels d k → E → Covariate d → ℝ}
    (hReset : ∀ j, Measurable (Function.uncurry (pReset j)))
    {cReset : HighWindowLabels d k → E → HighFrameVector d D}
    (hcReset : ∀ j γ, Measurable (fun e => cReset j e γ))
    (c : HighWindowLabels d k → HighFrameVector d D) :
    Measurable (highFrameFullMarkedScore n π activation a V η p pReset cReset c) := by
  apply measurable_from_prod_countable_left
  intro y
  apply Finset.measurable_sum
  intro j hj
  let g := highLocalFieldWithout η c j
  let w := highPeriodicTensor j
  let φ : Covariate d → HighFrameVector d D := fun x => highLocalFrameFeature j x
  have hg  := (highLocalFieldWithout_continuous η c j).measurable
  have hw  := (highPeriodicTensor_contDiff j).continuous.measurable
  have hφ : ∀ γ, Measurable (fun x => φ x γ) := highLocalFrameFeature_measurable j
  have hR := highMarkedSampleNumerator_measurable (π j) (hAct j)
    a V η hp (hReset j) (hcReset j) hg hw hφ (c j) y
  exact hR.div ((Finset.measurable_prod _ (fun i _ => by fun_prop)).mul (Finset.measurable_prod _ (fun i _ => (highMarkedResponseMass_measurable a V η hg hw hφ (c j) (y i)).comp (measurable_pi_apply i))))

theorem high_frame_complete_design_spatial_series (hk : 4 ≤ k)
    {π : HighWindowLabels d k → Measure E} [∀ j, SFinite (π j)]
    {activation : HighWindowLabels d k → E → ℝ}
    (hAct : ∀ j, Measurable (activation j)) (hActI : ∀ j, Integrable (activation j) (π j))
    {a V η pMinus pPlus cMass : ℝ} (ha : a ≠ 0) (hpMinus : 0 < pMinus)
    (hpPlus : 0 ≤ pPlus) (hcMass : 0 < cMass)
    {p : Covariate d → ℝ} (hp : Measurable p)
    (hraw : ∀ x, pMinus ≤ p x ∧ p x ≤ pPlus)
    {pReset : HighWindowLabels d k → E → Covariate d → ℝ}
    (hReset : ∀ j, Measurable (Function.uncurry (pReset j)))
    (hBound : ∀ j e x, |pReset j e x| ≤ pPlus)
    (hOutside : ∀ j e x, x ∉ highTorusPatch j → pReset j e x = p x)
    {cReset : HighWindowLabels d k → E → HighFrameVector d D}
    (hcReset : ∀ j γ, Measurable (fun e => cReset j e γ))
    {c : HighWindowLabels d k → HighFrameVector d D}
    (hq : ∀ x y, cMass ≤ ternaryMass a (highFrameField k η (fun l => highFramePolynomial (c l)) x) V y)
    (hqReset : ∀ j e x y, 0 ≤ highMarkedResponseMass a V η
      (highLocalFieldWithout η c j) (highPeriodicTensor j)
      (fun x => highLocalFrameFeature j x) (cReset j e) x y)
    (hDensity : ∀ j (x : DesignSample d n),
      (∫ e, activation j e * ∏ i, pReset j e (x i) ∂π j) = 0)
    {H : HighWindowLabels d k → (r : ℕ) → (DesignSample d r) → ℝ}
    (hH : ∀ j r, Integrable (H j r) (Measure.pi (fun _ => volume.restrict (spatialPatchBox d))))
    (hH0 : ∀ j r u, 0 ≤ H j r u)
    (hdom : ∀ j r x, (∀ i, x i ∈ highTorusPatch j) →
      selectedRawSquareEnergy (highMarkedSampleNumerator r (π j) (activation j) a V η p (pReset j)
        (cReset j) (highLocalFieldWithout η c j) (highPeriodicTensor j)
          (fun x => highLocalFrameFeature j x) (c j)) x ≤ H j r (highPatchProductChart j x)) :
    let F := highFrameField k η (fun l => highFramePolynomial (c l))
    let hF : Measurable F := (highFrameField_contDiff d k η _).continuous.measurable
    let S := highFrameFullMarkedScore n π activation a V η p pReset cReset c
    Integrable (fun z => S z ^ 2) ((Measure.pi (fun _ => highNormalizedDesignLaw p)).compProd
      (responseSampleIndexKernel n a V hF)) ∧
    (∫ z, S z ^ 2 ∂(Measure.pi (fun _ => highNormalizedDesignLaw p)).compProd
      (responseSampleIndexKernel n a V hF)) ≤
      (3 ^ d : ℕ) * ∑ j, ∑ r ∈ Finset.range (n + 1),
        (n * highFixedScoreDenominator pMinus cMass * (2 / k) ^ d) ^ r /
          r.factorial * ∫ u, H j r u
            ∂Measure.pi (fun _ => volume.restrict (spatialPatchBox d)) := by
  let F := highFrameField k η (fun l => highFramePolynomial (c l))
  have hF : Measurable F := (highFrameField_contDiff d k η _).continuous.measurable
  let μ := Measure.pi (fun _ : Fin n => highNormalizedDesignLaw p)
  let _ := high_normalized_design_probability hp hpMinus (Filter.Eventually.of_forall hraw)
  let Eglobal := finiteResponseSquareEnergy a V F (highFrameFullMarkedScore n π activation a V η p pReset cReset c)
  let Elocal j := highMarkedSampleConditionalEnergy n (π j) (activation j)
    a V η p (pReset j) (cReset j) (highLocalFieldWithout η c j)
      (highPeriodicTensor j) (fun x => highLocalFrameFeature j x) (c j)
  have hqLocal j x y :
      cMass ≤ highMarkedResponseMass a V η (highLocalFieldWithout η c j)
        (highPeriodicTensor j) (fun x => highLocalFrameFeature j x) (c j) x y := by
    unfold highMarkedResponseMass
    rw [← highFrameField_local_decomposition hk η c j x]
    exact hq x y
  have hlocal j := high_marked_original_design_spatial_series hk n (hAct j) ha hpMinus hcMass hp hraw (hReset j) (hcReset j)
    (highLocalFieldWithout_continuous η c j).measurable
    (highPeriodicTensor_contDiff j).continuous.measurable (highLocalFrameFeature_measurable j)
    (hqLocal j) (fun x hx => by
      by_contra h
      exact hx (highPeriodicTensor_supported_patch j h))
    (hOutside j) (hH j) (hH0 j) (hdom j)
  have hSm  := highFrameFullMarkedScore_measurable d k D n π hAct
    a V η hp hReset hcReset c
  have hEm : Measurable Eglobal := by
    apply Finset.measurable_sum
    intro y hy
    fun_prop
  have hEn x : 0 ≤ Eglobal x :=
    Finset.sum_nonneg (fun y _ => mul_nonneg
      (Finset.prod_nonneg (fun i _ => hcMass.le.trans (hq ..))) (sq_nonneg _))
  have hpoint x : Eglobal x ≤ (3 ^ d : ℕ) * ∑ j, Elocal j x := by
    have he := highFrameMarkedScore_energy_bound hk hActI a V η pPlus ha hpPlus
      (p ∘ x) (fun j e => pReset j e ∘ x)
      (fun j i => (hReset j).comp (measurable_id.prodMk measurable_const))
      (fun j e i => hBound ..) hcReset c x
      (fun i => (hpMinus.trans_le (hraw (x i)).1).ne')
      (fun i y => hcMass.trans_le (hq (x i) y))
      (fun j e i y => by bound) (fun j => hDensity j x)
    dsimp only at he
    rw [ternary_index_product_integral] at he
    have hloc j :
        (∫ y, highFrameMarkedScore π activation a V η (p ∘ x)
          (fun j e => pReset j e ∘ x) cReset c x j y ^ 2
          ∂Measure.pi (fun i => ternaryIndexMeasure (F (x i)) V ha
            (fun y => (hcMass.trans_le (hq (x i) y)).le))) = Elocal j x := by
      have hreg := highFrameField_coefficientRegression hk η c j x
      change coefficientRegression η (highLocalFieldWithout η c j ∘ x)
        (highPeriodicTensor j ∘ x) ((fun x => highLocalFrameFeature j x) ∘ x) (c j) =
          _ at hreg
      have hs := high_marked_sample_energy_integral (π j) (activation j) a V η ha p (pReset j)
        (cReset j) (highLocalFieldWithout η c j) (highPeriodicTensor j)
          (fun x => highLocalFrameFeature j x) (c j) x
            (fun x y => hcMass.trans_le (hqLocal ..))
      rw [ternary_index_product_integral] at hs
      rw [hreg] at hs
      rw [ternary_index_product_integral]
      exact hs
    dsimp [F] at hloc
    simp_rw [hloc] at he
    exact he
  have hu : Integrable (fun x => (3 ^ d : ℕ) * ∑ j, Elocal j x) μ :=
    (integrable_finsetSum _ (fun j _ => (hlocal j).1)).const_mul _
  have hEI : Integrable Eglobal μ := by
    apply hu.mono' hEm.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hEn x)]
      exact hpoint x)
  have hs := response_sample_square_integrable_integral ha hF
    (fun x y => hcMass.le.trans (hq x y)) hSm hEI
  refine ⟨hs.1, ?_⟩
  rw [hs.2]
  calc
    _ ≤ _ := integral_mono hEI hu hpoint
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun j _ => (hlocal j).1)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => (hlocal j).2)) (Nat.cast_nonneg _)

end
end NearlyMinimax
