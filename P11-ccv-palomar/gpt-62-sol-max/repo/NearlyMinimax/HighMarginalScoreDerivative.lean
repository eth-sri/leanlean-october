module

public import NearlyMinimax.HighMarginalScore
public import NearlyMinimax.HighObservableRegularity
public import NearlyMinimax.RealDensity


@[expose] public section

/-! Genuine observed-data score derivative for the actual high experiment. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

variable {dependent : J → J → Prop} {Δ : ℕ} {T Ba : ℝ}
  {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
  {π : Measure E} [IsProbabilityMeasure π] {activation : E → ℝ}
  (P : HistoryPriorBounds dependent Δ π activation T Ba)
  {d : ℕ} (n : ℕ) (a v η aRaw bRaw : ℝ) (ha : 0 < a) (haRaw : 0 < aRaw)
  (p F : HistoryMarked dependent E → Covariate d → ℝ)
  (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
  (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
  (hmass : ∀ u ∈ Icc 0 T,
    (historyMarkedPrior dependent Δ u π activation).map (fun ω => highRawDensityMass (p ω)) =
    (historyMarkedPrior dependent Δ 0 π activation).map (fun ω => highRawDensityMass (p ω)))

local notation "ν" => (fun t : ℝ => historyMarkedPrior dependent Δ t π activation)
local notation "V" => (fun t : ℝ => v - η ^ 2 * t)
local notation "D" => (fun t => highDataLaw (ν t) n a (V t) p F hp hF)
local notation "Z" => (fun t => massPowerNormalizer (ν t) (fun ω => highRawDensityMass (p ω)) n)
local notation "L" => (fun t => highMarginalRawLikelihood (ν t) n a (V t) p F)
local notation "A" => (fun t => highMarginalLikelihoodDerivative dependent P.symm (ν t) π activation n a (V t) η p F)
local notation "score" => (fun t => highMarginalRealScore dependent P.symm (ν t) π activation n a (V t) η p F)

private theorem lipschitz_congr_on {f g : ℝ → ℝ} {s : Set ℝ} {K : NNReal}
    (hf : LipschitzOnWith K f s) (he : EqOn g f s) : LipschitzOnWith K g s := by
  intro x hx y hy
  rw [he hx, he hy]
  exact hf hx hy

theorem time_ae_of_Ioo {Q : ℝ → Prop} (h : ∀ t ∈ Ioo 0 T, Q t) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Icc 0 T → Q t := by
  filter_upwards [Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)) (a := 0) (b := T)] with t ht hmem
  exact h t (ht.mpr hmem)

local notation "Raw" => (fun t (z : HistoryMarked dependent E × TernarySample d n) =>
  highRawSampleLikelihood n a (V t) (p (Prod.fst z)) (F (Prod.fst z)) (Prod.snd z))
local notation "Heat" => (fun t (z : HistoryMarked dependent E × TernarySample d n) =>
  -η ^ 2 * highRawSampleVarianceDerivative n a (V t) (p (Prod.fst z)) (F (Prod.fst z)) (Prod.snd z))
local notation "C₀" => (|bRaw| ^ n)
local notation "C₁" => (η ^ 2 * (C₀ * ((n : ℝ) / a ^ 2)))
local notation "C₂" => ((Fintype.card J : ℝ) * (Ba * C₀) + C₁)

section Bounds
variable (hq : ∀ u ∈ Icc 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v - η ^ 2 * u) y)

include aRaw ha haRaw hraw hp hF hq in
private theorem raw_path_bounds : BoundedPath (Icc 0 T) Raw C₀ ∧ BoundedPath (Icc 0 T) Heat C₁ := by
  have hb := highRawDensity_abs_bound haRaw.le hraw
  refine ⟨.of_abs (fun u => highRawSampleLikelihood_joint_measurable n a (V u) p F hp hF)
    (by positivity) (fun u hu z => highRawSampleLikelihood_abs_le n a (V u) |bRaw|
      _ _ (hb z.1) ha.ne' (hq u hu z.1) z.2),
    .of_abs (fun u => (highRawSampleVarianceDerivative_joint_measurable n a (V u) p F hp hF).const_mul _)
      (by positivity) ?_⟩
  intro u hu z
  rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg η)]
  exact mul_le_mul_of_nonneg_left (highRawSampleVarianceDerivative_abs_le n a (V u) |bRaw| ha
    (abs_nonneg _) _ _ (hb z.1) (hq u hu z.1) z.2) (sq_nonneg η)

include P in
private theorem prior_sFinite (t : ℝ) : SFinite (ν t) := by
  let _ := P.reference_probability
  dsimp only
  rw [historyMarkedPrior_eq_withDensity dependent Δ t π activation P.measurable]
  infer_instance

include aRaw ha haRaw hraw hp hF hq in
private theorem derivative_path_bound : BoundedPath (Icc 0 T) A C₂ := by
  have hR : BoundedPath (Icc 0 T) (fun t (z : HistoryMarked dependent E × TernarySample d n) =>
      highHistoryLikelihoodDerivative dependent P.symm π activation n a (V t) η p F z.1 z.2) C₂ :=
    .of_abs (fun u => highHistoryLikelihoodDerivative_measurable dependent P.symm π activation P.measurable
      n a (V u) η p F hp hF) (by have := P.bound_nonneg; positivity)
      (fun u hu z => highHistoryLikelihoodDerivative_abs_le π dependent P.symm activation
        Ba P.bound_nonneg P.bound n a (V u) η |bRaw| (abs_nonneg _) ha p F
        (highRawDensity_abs_bound haRaw.le hraw) (hq u hu) z.1 z.2)
  exact hR.marginal (prior_sFinite P) (fun _ ht => P.probability ht)

include aRaw ha haRaw hraw hp hF hq in
private theorem marginal_hasDerivAt (hL : BoundedPath (Icc 0 T) Raw C₀)
    (hD : BoundedPath (Icc 0 T) Heat C₁) (z : TernarySample d n) (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun u => L u z) (A t z) t := by
  have hm : Measurable (fun ω : HistoryMarked dependent E => (ω,z)) := measurable_id.prodMk measurable_const
  have hd := historyMarkedPrior_observable_product_rule P ht
    ((hL.mono Ioo_subset_Icc_self).comp hm) ((hD.mono Ioo_subset_Icc_self).comp hm)
    (fun ω u _ => highRawSampleLikelihood_hasDerivAt_path n a v η u (p ω) (F ω) z)
  apply hd.congr_deriv
  let _ := P.probability (Ioo_subset_Icc_self ht)
  have hti := Ioo_subset_Icc_self ht
  have hg (j : J) : Integrable (fun e => highAppendLikelihoodAction dependent P.symm π activation
      n a (V t) p F j e z) (ν t) :=
    Integrable.of_bound ((highAppendLikelihoodAction_measurable dependent P.symm π activation P.measurable
      n a (V t) p F hp hF j).comp hm).aestronglyMeasurable (Ba * C₀)
      (.of_forall fun ω => by
        rw [Real.norm_eq_abs]
        exact highAppendLikelihoodAction_abs_le π dependent P.symm activation Ba P.bound_nonneg P.bound
          n a (V t) |bRaw| (abs_nonneg _) ha.ne' p F (highRawDensity_abs_bound haRaw.le hraw)
          (hq t hti) j ω z)
  have hgen (j : J) : (∫ e : HistoryMarked dependent E × E,
      Raw t (historyMarkedAppend dependent P.symm j e,z) * activation e.2 ∂(ν t).prod π) =
      ∫ ω, highAppendLikelihoodAction dependent P.symm π activation n a (V t) p F j ω z ∂ν t := by
    have hF₀ : Measurable (fun e : HistoryMarked dependent E × E =>
        Raw t (historyMarkedAppend dependent P.symm j e,z) * activation e.2) :=
      ((hL.measurable t).comp (hm.comp (historyMarkedAppend_measurable dependent P.symm j))).mul
        (P.measurable.comp measurable_snd)
    have hi := Integrable.of_bound (μ := (ν t).prod π) hF₀.aestronglyMeasurable (C₀ * Ba)
      (.of_forall fun e => (norm_mul _ _).le.trans (mul_le_mul (hL.norm_le t hti _) (by
        simpa only [Real.norm_eq_abs] using P.bound e.2) (norm_nonneg _) (by positivity)))
    rw [integral_prod _ hi]
    simp only [highAppendLikelihoodAction, mul_comm]
  have hiD := (hD.comp hm).integrable (μ := ν t) hti
  unfold highMarginalLikelihoodDerivative
  simp only [historyMarkedPriorGenerator, hgen]
  -- The integral of the local derivative is the sum of the append and heat integrals.
  have heq : (fun ω => highHistoryLikelihoodDerivative dependent P.symm π activation n a (V t) η p F ω z) =
      (fun ω => (∑ j, highAppendLikelihoodAction dependent P.symm π activation n a (V t) p F j ω z) +
        Heat t (ω,z)) := by
    funext ω
    simp only [highHistoryLikelihoodDerivative, neg_mul]
    ring
  rw [heq, integral_add (integrable_finsetSum _ (fun j _ => hg j)) hiD,
    integral_finsetSum _ (fun j _ => hg j), add_comm]

end Bounds

section Observable
variable (H : ObservedSample d n → ℝ) (hH : Measurable H)
  (B : ℝ) (hB : 0 ≤ B) (hHb : ∀ z, |H z| ≤ B)

local notation "mean" => (fun t => ∫ z, H z ∂D t)
local notation "test" => (fun z => H (encodeDesignResponse a z))
local notation "weighted" => (fun u z => test z * L u z)
local notation "weighted'" => (fun u z => test z * A u z)
local notation "ref" => highSampleReference d n

include hH hB hHb in
private theorem test_path : BoundedPath (Icc 0 T) (fun _ => test) B :=
  .of_abs (fun _ => hH.comp (encodeDesignResponse_measurable a)) hB (fun _ _ _ => hHb _)

include P aRaw bRaw ha haRaw hraw hmass hH in
private theorem dataMean_eq_raw
    (hq : ∀ u ∈ Icc 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    (t : ℝ) (ht : t ∈ Icc 0 T) : mean t = (Z 0)⁻¹ * ∫ z, weighted t z ∂ref := by
  let _ := P.probability ht
  dsimp only
  rw [highDataLaw_integral_marginal (ν t) n a (V t) p F hp hF aRaw bRaw haRaw ha.ne' hraw (hq t ht) H hH,
    massPowerNormalizer_eq_of_massLaw _ _ _ (highRawDensityMass_joint_measurable p hp) n (hmass t ht)]
  simp only [div_eq_mul_inv, mul_comm]

include P aRaw bRaw ha haRaw hraw hmass hH hB hHb in
theorem historyMarkedPrior_dataMean_regularity
    (hq : ∀ u ∈ Icc 0 T, ∀ ω x y, 0 < ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval mean 0 T ∧
    ∀ t ∈ Ioo 0 T, HasDerivAt mean (∫ z, H z * score t z ∂D t) t := by
  have hq0 u hu ω x y := (hq u hu ω x y).le
  obtain ⟨hRaw, hHeat⟩ := raw_path_bounds n a v η aRaw bRaw ha haRaw p F hp hF hraw hq0
  have hM : BoundedPath (Icc 0 T) L C₀ :=
    hRaw.marginal (prior_sFinite P) (fun _ ht => P.probability ht)
  have hTest := test_path (T := T) n a H hH B hB hHb
  have hWeighted := hTest.mul hM
  have he := dataMean_eq_raw P n a v η aRaw bRaw ha haRaw p F hp hF hraw hmass H hH hq0
  constructor
  · have hL' (z : TernarySample d n) := historyMarkedPrior_variable_observable_lipschitz P
      (hRaw.comp (measurable_id.prodMk (measurable_const (a := z))))
      (fun ω => hHeat.lipschitzOnWith (convex_Icc 0 T)
        (fun u _ e => highRawSampleLikelihood_hasDerivAt_path n a v η u (p e.1) (F e.1) e.2) (ω,z))
    let K : NNReal := ⟨C₁ * (3 / 2 : ℝ) ^ Fintype.card J +
      C₀ * ((historyReferenceRho Δ)⁻¹ * (Fintype.card J : ℝ) * Ba * (3 / 2 : ℝ) ^ Fintype.card J),
      by have := historyReferenceRho_pos Δ; have := P.bound_nonneg; positivity⟩
    have hk (z : TernarySample d n) : LipschitzOnWith K (fun u => L u z) (Icc 0 T) := by
      convert hL' z using 1 <;> first | rfl | (apply Subtype.ext; rfl)
    have htL := hWeighted.lipschitzIntegral (μ := ref)
      (hTest.lipschitzMul hM (fun _ => (LipschitzWith.const _).lipschitzOnWith) hk)
    have h := lipschitz_congr_on ((lipschitzWith_smul ((Z 0)⁻¹)).comp_lipschitzOnWith htL)
      (fun u hu => he u hu)
    exact (h.mono (by rw [uIcc_of_le hT])).absolutelyContinuousOnInterval
  · intro t ht
    have hti := Ioo_subset_Icc_self ht
    let _ := P.probability hti
    have hL := hWeighted.mono Ioo_subset_Icc_self
    have hA := (hTest.mul (derivative_path_bound P n a v η aRaw bRaw ha haRaw p F hp hF hraw hq0)).mono
      Ioo_subset_Icc_self
    have hd := (hL.hasDerivAt_integral (μ := ref) hA (Ioo_mem_nhds ht.1 ht.2) (fun u hu z =>
      (marginal_hasDerivAt P n a v η aRaw bRaw ha haRaw p F hp hF hraw hq0 hRaw hHeat z u hu).const_mul (test z))).const_mul
        ((Z 0)⁻¹)
    have hl (z) : 0 < L t z := highMarginalRawLikelihood_pos (ν t) n a (V t) |bRaw| (abs_nonneg _) ha.ne'
      p F hp hF (fun ω x => haRaw.trans_le (hraw ω x).1) (highRawDensity_abs_bound haRaw.le hraw) (hq t hti) z
    have hs : (∫ z, H z * score t z ∂D t) = (Z 0)⁻¹ * ∫ z, weighted' t z ∂ref := by
      have hm := hH.mul (highMarginalRealScore_measurable dependent P.symm (ν t) π activation P.measurable
        n a (V t) η p F hp hF)
      refine (dataMean_eq_raw P n a v η aRaw bRaw ha haRaw p F hp hF hraw hmass
        (fun z => H z * score t z) hm hq0 t hti).trans (congrArg ((Z 0)⁻¹ * ·) ?_)
      apply integral_congr_ae
      exact .of_forall fun z => by
        simp only [highMarginalRealScore_encode _ _ _ _ _ ha, highMarginalIndexScore]
        field_simp [(hl z).ne']
    rw [hs]
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    exact he u (Ioo_subset_Icc_self hu)

end Observable

include aRaw bRaw ha haRaw hraw hmass in
private theorem historyMarkedPrior_dataScore_centered
    (hq : ∀ u ∈ Icc 0 T, ∀ ω x y, 0 < ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    (t : ℝ) (ht : 0 < t) (htT : t < T) : (∫ z, score t z ∂D t) = 0 := by
  have hd := (historyMarkedPrior_dataMean_regularity P n a v η aRaw bRaw ha haRaw p F hp hF
    hraw hmass (fun _ => 1) measurable_const 1 zero_le_one (by simp) hq (ht.trans htT).le).2 t ⟨ht, htT⟩
  have he : (fun u => ∫ _z, (1 : ℝ) ∂D u) =ᶠ[𝓝 t] (fun _ => 1) := by
    filter_upwards [Ioo_mem_nhds ht htT] with u hu
    have hui : u ∈ Icc 0 T := ⟨hu.1.le, hu.2.le⟩
    let _ := P.probability hui
    let _ := highMassPowerTilt_isProbability (ν u) n p hp haRaw hraw
    let _ := highRealSampleKernel_markov n a (V u) p F hp hF aRaw bRaw haRaw hraw ha.ne'
      (fun ω x y => (hq u hui ω x y).le)
    simp
  simpa only [one_mul] using hd.unique ((hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq he)

include aRaw bRaw ha haRaw hraw hmass in
theorem historyMarkedPrior_dataScore_centered_ae
    (hq : ∀ u ∈ Icc 0 T, ∀ ω x y, 0 < ternaryMass a (F ω x) (v - η ^ 2 * u) y) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Icc 0 T → (∫ z, score t z ∂D t) = 0 :=
  time_ae_of_Ioo fun t ht => historyMarkedPrior_dataScore_centered P n a v η aRaw bRaw ha haRaw
    p F hp hF hraw hmass hq t ht.1 ht.2

end NearlyMinimax
