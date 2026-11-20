module

public import NearlyMinimax.HighSeparatedScoreBounds
public import NearlyMinimax.HighUnionScore


@[expose] public section

/-! Genuine all-count Taylor bounds for arbitrary finite density-response
atom tensors and their true absolute positive reference law. Both ordinary
and fine three-point density selectors are instances of these tensors. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable

section
variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem responseTensor_slice_all_count_bound {n : ℕ} (q : ℕ) (hn : 1 ≤ n)
    {C a V η ρ pPlus : ℝ} (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η)
    (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ/2) (hpPlus : 0 ≤ pPlus)
    (weights : J → ℝ) (A : ι → ι → ℝ) {pReset : J → Fin n → ℝ}
    {g w : Fin n → ℝ} {φ : Fin n → ι → ℝ} {c : ι → ℝ}
    (hc : ∑ γ, |c γ| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ γ, |v γ|) ≤ C⁻¹ → ∀ i, |∑ γ, φ i γ*v γ| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y)
    (hReset : ∀ e i, |pReset e i| ≤ pPlus) (y : TernaryVector n) :
    let product := highResponseProduct a V η g w φ
    |∑ e : J × HighResponseMarkIndex ι q,
      weights e.1 * highResponseMarkWeight C A e.2 * (∏ i, pReset e.1 i) *
        product
          (coefficientReset c (highResponseMarkAtom C e.2).2
            (highResponseMarkAtom C e.2).1) y| ≤
      (pPlus^n * highSeparatedDerivativeBudget a ρ * (n : ℝ)^2 * η^2) *
        ∑ e : J × HighResponseMarkIndex ι q, |weights e.1 * highResponseMarkWeight C A e.2| := by
  intro product
  have he : (∑ e : J × HighResponseMarkIndex ι q,
      weights e.1 * highResponseMarkWeight C A e.2 * (∏ i, pReset e.1 i) *
        product
          (coefficientReset c (highResponseMarkAtom C e.2).2
            (highResponseMarkAtom C e.2).1) y) =
      highDensityResponseAction q C weights (fun _ => A) c
        (fun e => ∏ i, pReset e i) (fun v => product v y) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro e _
    have hh (r : HighResponseMarkIndex ι q) :
        weights e * highResponseMarkWeight C A r * (∏ i, pReset e i) *
          product
            (coefficientReset c (highResponseMarkAtom C r).2 (highResponseMarkAtom C r).1) y =
        (weights e*(∏ i, pReset e i)) * (highResponseMarkWeight C A r *
          product
            (coefficientReset c (highResponseMarkAtom C r).2 (highResponseMarkAtom C r).1) y) := by ring
    simp only [hh, ← Finset.mul_sum]
    rw [highResponseMark_action q C A c (fun v => product v y)]
  rw [he]
  apply (high_density_response_product_abs_bound q hn hC ha hη hρ hηρ hpPlus
    weights (fun _ => A) hc hg hw hφ hp hReset y).trans_eq
  rw [Fintype.sum_prod_type]
  simp
  simp_rw [← Finset.mul_sum]
  rw [highResponseMark_variation q C A]
  unfold highResponsePacketCost highLocalDerivativeConstant highSeparatedDerivativeBudget
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  ring

end

section Reference
variable {ι J Z : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace Z]

/-- Actual absolute-reference all-count raw response action is bounded by
its true variation mass and an η² Taylor factor. The variation is an
integral of the constructed signed atom weights. -/
theorem responseTensor_reference_all_count_bound {n : ℕ}
    {σ : Measure Z} [IsFiniteMeasure σ] {q : ℕ} (hn : 1 ≤ n)
    {C a V η ρ pPlus : ℝ} (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η)
    (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ/2) (hpPlus : 0 ≤ pPlus)
    {weights : J → ℝ} {A : Z → ι → ι → ℝ}
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < signedMarkMass (σ.prod Measure.count) (responseTensorWeight weights q C A))
    {pReset : Z × J → Fin n → ℝ}
    (hmReset : ∀ i, Measurable (fun e => pReset e i))
    (hReset : ∀ e i, |pReset e i| ≤ pPlus)
    {g w : Fin n → ℝ} {φ : Fin n → ι → ℝ} {c : ι → ℝ}
    (hc : ∑ γ, |c γ| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ γ, |v γ|) ≤ C⁻¹ → ∀ i, |∑ γ, φ i γ*v γ| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y)
    (y : TernaryVector n) :
    |highMarkedResponseAction
      (absoluteMarkLaw (σ.prod Measure.count) (responseTensorWeight weights q C A))
      (absoluteActivation (σ.prod Measure.count) (responseTensorWeight weights q C A)) a V η
      (fun e => pReset (e.1,e.2.1))
      (fun e => coefficientReset c (highResponseMarkAtom C e.2.2).2 (highResponseMarkAtom C e.2.2).1)
      g w φ y| ≤
      (pPlus^n * highSeparatedDerivativeBudget a ρ * (n : ℝ)^2 * η^2) *
        signedMarkMass (σ.prod Measure.count) (responseTensorWeight weights q C A) := by
  have hm := tensorWeight_measurable weights q C hA
  have hi := tensorWeight_integrable weights q C hA hcost
  let ν : Measure (Z × (J × HighResponseMarkIndex ι q)) := σ.prod Measure.count
  let W := responseTensorWeight weights q C A
  let Φ : (ι → ℝ) → ℝ := fun v => highResponseProduct a V η g w φ v y
  let O : Z × (J × HighResponseMarkIndex ι q) → ℝ := fun e => (∏ i, pReset (e.1,e.2.1) i) *
    Φ (coefficientReset c (highResponseMarkAtom C e.2.2).2 (highResponseMarkAtom C e.2.2).1)
  let K := pPlus^n * highSeparatedDerivativeBudget a ρ * (n : ℝ)^2 * η^2
  have hResetJoint (i) : Measurable (fun e : Z × (J × HighResponseMarkIndex ι q) => pReset (e.1,e.2.1) i) :=
    (hmReset i).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hCoef (γ) : Measurable (fun e : Z × (J × HighResponseMarkIndex ι q) =>
      coefficientReset c (highResponseMarkAtom C e.2.2).2 (highResponseMarkAtom C e.2.2).1 γ) :=
    (measurable_of_countable (fun e : J × HighResponseMarkIndex ι q =>
      coefficientReset c (highResponseMarkAtom C e.2).2 (highResponseMarkAtom C e.2).1 γ)).comp measurable_snd
  have hO : Measurable O := (Finset.measurable_fun_prod _ (fun i _ => hResetJoint i)).mul
    (highMarkedResponseProduct_measurable a V η _ hCoef g w φ y)
  have hΦ (r : HighResponseMarkIndex ι q) :
      |Φ (coefficientReset c (highResponseMarkAtom C r).2 (highResponseMarkAtom C r).1)| ≤ 1 := by
    have hb := coefficientReset_mem_ball C c (highResponseMarkAtom C r).2
      (highResponseMarkAtom C r).1 (responseNode_mem_unit q r.2.2) hc
      (covarianceAtom_mem_ball hC _ _ _ _)
    exact highResponseProduct_ball_abs_le_one ha.ne' hη hηρ hg hw hφ hp hb y
  have hOb (e) : ‖O e‖ ≤ pPlus^n := by
    change |(∏ i, pReset (e.1,e.2.1) i)*Φ _| ≤ _
    rw [abs_mul]
    exact (mul_le_mul (finite_density_product_abs_bound _ hpPlus (hReset (e.1,e.2.1)))
      (hΦ e.2.2) (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  have hWO := hi.mul_bdd hO.aestronglyMeasurable (Filter.Eventually.of_forall hOb)
  have hSlice (ζ) : |∫ e : J × HighResponseMarkIndex ι q, W (ζ,e)*O (ζ,e) ∂Measure.count| ≤
      K * ∫ e : J × HighResponseMarkIndex ι q, |W (ζ,e)| ∂Measure.count := by
    simp
    simpa only [W,O,Φ,K,responseTensorWeight,mul_assoc] using
      responseTensor_slice_all_count_bound q hn hC ha hη hρ hηρ hpPlus
        weights (A ζ) hc hg hw hφ hp (fun e => hReset (ζ,e)) y
  unfold highMarkedResponseAction
  have he : (fun e => absoluteActivation ν W e * (∏ i, pReset (e.1,e.2.1) i) *
      highResponseProduct a V η g w φ
        (coefficientReset c (highResponseMarkAtom C e.2.2).2 (highResponseMarkAtom C e.2.2).1) y) =
      (fun e => absoluteActivation ν W e * O e) := by funext e; dsimp [O,Φ]; ring
  rw [he,absoluteMarkLaw_activation_integral hm hpos O,integral_prod _ hWO]
  apply abs_integral_le_integral_abs.trans
  apply (integral_mono hWO.integral_prod_left.abs (hi.abs.integral_prod_left.const_mul K) hSlice).trans_eq
  rw [integral_const_mul, ← integral_prod _ hi.abs]
  rfl

end Reference
end NearlyMinimax
