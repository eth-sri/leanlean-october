module

public import NearlyMinimax.BoundedPairMeanOperators
public import NearlyMinimax.FieldLiftCovariance
public import NearlyMinimax.Moments

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal RealInnerProductSpace

namespace NearlyMinimax

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

-- 1. Three-block sample splitting & minimax RMS helper

def threeBlockSize (n : ℕ) : ℕ := n / 3

theorem threeBlockSize_two_le {n : ℕ} (hn : 6 ≤ n) : 2 ≤ threeBlockSize n := by
  unfold threeBlockSize; omega

theorem threeBlockSize_fraction {n : ℕ} (hn : 6 ≤ n) :
    (1 / 4 : ℝ) * n ≤ threeBlockSize n := by
  have h : (n : ℝ) ≤ 4 * (threeBlockSize n : ℝ) := by
    exact_mod_cast (show n ≤ 4 * threeBlockSize n by unfold threeBlockSize; omega)
  linarith

def threeBlockSplit (d n : ℕ) :
    (Fin n → Observation d) →
      ((Fin (threeBlockSize n) → Observation d) × (Fin (threeBlockSize n) → Observation d)) ×
        (Fin (threeBlockSize n) → Observation d) :=
  let m := threeBlockSize n
  let r := n - (m + m + m)
  let idx : (((Fin m ⊕ Fin m) ⊕ Fin m) ⊕ Fin r) ≃ Fin n :=
    (((Equiv.sumCongr (Equiv.sumCongr finSumFinEquiv (.refl _)) (.refl _)).trans
      (Equiv.sumCongr finSumFinEquiv (.refl _))).trans finSumFinEquiv).trans
      (finCongr (by dsimp [m, r, threeBlockSize]; omega))
  let e1 := (MeasurableEquiv.piCongrLeft
    (fun _ : ((Fin m ⊕ Fin m) ⊕ Fin m) ⊕ Fin r => Observation d) idx.symm).trans
    (MeasurableEquiv.sumPiEquivProdPi _)
  let e2 := (MeasurableEquiv.sumPiEquivProdPi (fun _ : (Fin m ⊕ Fin m) ⊕ Fin m => Observation d)).trans
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin m => Observation d))
      (MeasurableEquiv.refl (Fin m → Observation d)))
  fun z => e2 (e1 z).1

theorem threeBlockSplit_measurable (d n : ℕ) : Measurable (threeBlockSplit d n) := by
  unfold threeBlockSplit
  exact MeasurableEquiv.measurable _ |>.comp (measurable_fst.comp (MeasurableEquiv.measurable _))

private theorem threeBlockSplit_measurePreserving {d n : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    MeasurePreserving (threeBlockSplit d n) (sampleLaw θ n)
      (((sampleLaw θ (threeBlockSize n)).prod (sampleLaw θ (threeBlockSize n))).prod
        (sampleLaw θ (threeBlockSize n))) := by
  let _ := observationLaw_isProbability C θ hθ
  let m := threeBlockSize n
  let r := n - (m + m + m)
  let _ := sampleLaw_isProbability C θ hθ m
  let _ := sampleLaw_isProbability C θ hθ r
  let idx : (((Fin m ⊕ Fin m) ⊕ Fin m) ⊕ Fin r) ≃ Fin n :=
    (((Equiv.sumCongr (Equiv.sumCongr finSumFinEquiv (.refl _)) (.refl _)).trans
      (Equiv.sumCongr finSumFinEquiv (.refl _))).trans finSumFinEquiv).trans
      (finCongr (by dsimp [m, r, threeBlockSize]; omega))
  have h1 := (measurePreserving_sumPiEquivProdPi
    (fun _ : ((Fin m ⊕ Fin m) ⊕ Fin m) ⊕ Fin r => observationLaw θ)).comp
    (measurePreserving_piCongrLeft _ idx.symm)
  have h2 : MeasurePreserving
      (Prod.fst : ((Fin m ⊕ Fin m) ⊕ Fin m → Observation d) × (Fin r → Observation d) → _)
      ((Measure.pi fun _ => observationLaw θ).prod (sampleLaw θ r))
      (Measure.pi fun _ => observationLaw θ) := measurePreserving_fst
  have h3 := ((measurePreserving_sumPiEquivProdPi
    (fun _ : Fin m ⊕ Fin m => observationLaw θ)).prod (MeasurePreserving.id (sampleLaw θ m))).comp
    (measurePreserving_sumPiEquivProdPi (fun _ : (Fin m ⊕ Fin m) ⊕ Fin m => observationLaw θ))
  exact h3.comp (h2.comp h1)

theorem minimaxRMS_le_of_estimator_rms {d n : ℕ} (C : ModelConstants d)
    (T : Estimator d n) {B : ℝ≥0∞}
    (hT : ∀ θ : RegressionParameter d, Admissible C θ → meanSquaredRisk T θ ^ (1 / 2 : ℝ) ≤ B) :
    minimaxRMS C n ≤ B := by
  refine (ENNReal.rpow_le_rpow (minimaxRisk_le_worstCaseRisk C T) (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans ?_
  let φ := ENNReal.orderIsoRpow (1 / 2 : ℝ) (by norm_num)
  change φ (⨆ θ : {θ : RegressionParameter d // Admissible C θ}, meanSquaredRisk T θ.val) ≤ B
  rw [φ.map_iSup]
  exact iSup_le fun θ => hT θ.val θ.property

-- 2. MemLp sections & localized two-stage pair U-statistic variance

private theorem memLp_sections_left {Ω W H : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
    [NormedAddCommGroup H] {μ : Measure Ω} {M : Measure W} [SFinite μ] [SFinite M]
    {η : Ω → W → H} (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M)) :
    ∀ᵐ x ∂μ, MemLp (η x) 2 M := by
  filter_upwards [hη.aestronglyMeasurable.prodMk_left, hη.norm.integrable_sq.prod_right_ae] with x hm hi
  exact (memLp_two_iff_integrable_sq_norm hm).mpr hi

namespace PairUStatistic

def weightedSymmetrization {E : Type*} (weight : ℝ) (G : E × E → ℝ) (z : E × E) : ℝ :=
  weight / 4 * (G z + G z.swap)

def fieldPairAverage {P Ω E : Type*} (n : ℕ) (weight : ℝ) (G : P → E × E → ℝ)
    (X : Fin n → Ω → E) (z : P × Ω) : ℝ :=
  pairAverage n (weightedSymmetrization weight (G z.1)) (fun i => X i z.2)

def fieldPairMean {P E : Type*} [MeasurableSpace E] {μ : Measure E}
    (weight : ℝ) (G : P → E × E → ℝ) (p : P) : ℝ :=
  weight / 2 * ∫ z, G p z ∂μ.prod μ

theorem fieldPairAverage_measurable {P Ω E : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
    [MeasurableSpace E] (n : ℕ) (weight : ℝ) {G : P → E × E → ℝ}
    (hmG : Measurable (fun z : P × (E × E) => G z.1 z.2))
    (X : Fin n → Ω → E) (hX : ∀ i, Measurable (X i)) :
    Measurable (fieldPairAverage n weight G X) := by
  unfold fieldPairAverage pairAverage weightedSymmetrization
  refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_) _
  refine Measurable.const_mul ?_ _
  exact (hmG.comp (measurable_fst.prodMk (((hX i).comp measurable_snd).prodMk ((hX j).comp measurable_snd)))).add
    (hmG.comp (measurable_fst.prodMk (((hX j).comp measurable_snd).prodMk ((hX i).comp measurable_snd))))

theorem fieldPairAverage_add_smul {P Ω E : Type*} (n : ℕ) (weight V : ℝ)
    (G H : P → E × E → ℝ) (X : Fin n → Ω → E) (z : P × Ω) :
    fieldPairAverage n weight (fun p w => G p w + V * H p w) X z =
      fieldPairAverage n weight G X z + V * fieldPairAverage n weight H X z := by
  unfold fieldPairAverage pairAverage weightedSymmetrization
  simp only [Prod.swap_prod_mk]
  have hpt (i j : Fin n) :
      weight / 4 * (G z.1 (X i z.2, X j z.2) + V * H z.1 (X i z.2, X j z.2) +
        (G z.1 (X j z.2, X i z.2) + V * H z.1 (X j z.2, X i z.2))) =
      weight / 4 * (G z.1 (X i z.2, X j z.2) + G z.1 (X j z.2, X i z.2)) +
      V * (weight / 4 * (H z.1 (X i z.2, X j z.2) + H z.1 (X j z.2, X i z.2))) := by ring
  simp_rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum]; ring

theorem fieldPairAverage_memLp {P Ω E : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
    [MeasurableSpace E] {π : Measure P} {ν : Measure Ω} {μ : Measure E}
    [IsProbabilityMeasure π] [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {n : ℕ} (weight : ℝ) {G : P → E × E → ℝ}
    (hG : MemLp (fun z : P × (E × E) => G z.1 z.2) 2 (π.prod (μ.prod μ)))
    (X : Fin n → Ω → E) (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ) :
    MemLp (fieldPairAverage n weight G X) 2 (π.prod ν) := by
  have hsym : MemLp (fun z : P × (E × E) => weightedSymmetrization weight (G z.1) z.2) 2 (π.prod (μ.prod μ)) :=
    (hG.add (hG.comp_measurePreserving ((MeasurePreserving.id π).prod Measure.measurePreserving_swap))).const_mul (weight / 4)
  unfold fieldPairAverage
  simp only [pairAverage_eq_orderedPairs]
  apply MemLp.const_mul
  apply memLp_finsetSum
  intro p hp
  have hm : MeasurePreserving (fun z : P × Ω => (z.1, (X p.1 z.2, X p.2 z.2)))
      (π.prod ν) (π.prod (μ.prod μ)) :=
    (MeasurePreserving.id π).prod (pair_measurePreserving X hind hX (Finset.mem_filter.mp hp).2)
  exact hsym.comp_measurePreserving hm

theorem fieldPairAverage_centered_sq_le {P Ω E I : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace I] [MeasurableSingletonClass I]
    {π : Measure P} {ν : Measure Ω} {μ : Measure E}
    [IsProbabilityMeasure π] [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) (X : Fin n → Ω → E) (hind : iIndepFun X ν)
    (hX : ∀ i, MeasurePreserving (X i) ν μ)
    (label : E → I) (hlabel : Measurable label)
    {G : P → E × E → ℝ} (hmG : Measurable (fun z : P × (E × E) => G z.1 z.2))
    (hG : MemLp (fun z : P × (E × E) => G z.1 z.2) 2 (π.prod (μ.prod μ)))
    (hsupport : ∀ p x y, label x ≠ label y → G p (x, y) = 0)
    {weight cap bound d c : ℝ} (hw : 0 < weight) (hcap : 0 ≤ cap)
    (hmass : ∀ i, μ.real (label ⁻¹' {i}) ≤ cap) (hbound : weight * cap ≤ bound)
    (hmean2 : MemLp (fieldPairMean (μ := μ) weight G) 2 π)
    (hmean : (∫ p, (fieldPairMean (μ := μ) weight G p - c) ^ 2 ∂π) ≤ d) :
    (∫ z, (fieldPairAverage n weight G X z - c) ^ 2 ∂π.prod ν) ≤
      2 * (bound / (n : ℝ) + weight / (2 * (n : ℝ) * (n - 1 : ℕ))) *
        (weight * ∫ z : P × (E × E), G z.1 z.2 ^ 2 ∂π.prod (μ.prod μ)) + 2 * d := by
  let T := fieldPairAverage n weight G X
  let L := fieldPairMean (μ := μ) weight G
  let a := bound / (n : ℝ) + weight / (2 * (n : ℝ) * (n - 1 : ℕ))
  have hT : MemLp T 2 (π.prod ν) := fieldPairAverage_memLp weight hG X hind hX
  have hL_comp : MemLp (fun z : P × Ω => L z.1) 2 (π.prod ν) := hmean2.comp_measurePreserving measurePreserving_fst
  have hTL : MemLp (fun z : P × Ω => T z - L z.1) 2 (π.prod ν) := hT.sub hL_comp
  have hLc : MemLp (fun z : P × Ω => L z.1 - c) 2 (π.prod ν) := hL_comp.sub (memLp_const c)
  have hsplit : (∫ z, (T z - c) ^ 2 ∂π.prod ν) ≤
      2 * (∫ z, (T z - L z.1) ^ 2 ∂π.prod ν) + 2 * (∫ p, (L p - c) ^ 2 ∂π) := by
    have hmono := integral_mono (hT.sub (memLp_const c)).integrable_sq
      ((hTL.integrable_sq.const_mul 2).add (hLc.integrable_sq.const_mul 2))
      fun z => show (T z - c) ^ 2 ≤ 2 * (T z - L z.1) ^ 2 + 2 * (L z.1 - c) ^ 2 by
        nlinarith [sq_nonneg ((T z - L z.1) - (L z.1 - c))]
    change (∫ z, (T z - c) ^ 2 ∂π.prod ν) ≤ ∫ z, 2 * (T z - L z.1) ^ 2 + 2 * (L z.1 - c) ^ 2 ∂π.prod ν at hmono
    rw [integral_add (f := fun z => 2 * (T z - L z.1) ^ 2) (g := fun z => 2 * (L z.1 - c) ^ 2)
      (hTL.integrable_sq.const_mul 2) (hLc.integrable_sq.const_mul 2),
      integral_const_mul, integral_const_mul] at hmono
    have h2 : (∫ z : P × Ω, (L z.1 - c) ^ 2 ∂π.prod ν) = ∫ p, (L p - c) ^ 2 ∂π := by
      simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using
        integral_fun_fst (μ := π) (ν := ν) fun p => (L p - c) ^ 2
    rwa [h2] at hmono
  -- Pointwise section U-statistic bound for almost every `p`
  have hcond : ∀ᵐ p ∂π, (∫ x, (T (p, x) - L p) ^ 2 ∂ν) ≤ a * (weight * ∫ z, G p z ^ 2 ∂μ.prod μ) := by
    filter_upwards [NearlyMinimax.memLp_sections_left (H := ℝ) hG] with p hp
    let K := weightedSymmetrization weight (G p)
    have hmK : Measurable K :=
      ((hmG.comp (measurable_const.prodMk measurable_id)).add
        ((hmG.comp (measurable_const.prodMk measurable_id)).comp measurable_swap)).const_mul _
    have hK : MemLp K 2 (μ.prod μ) := (hp.add (hp.comp_measurePreserving Measure.measurePreserving_swap)).const_mul _
    have hsym (x y : E) : K (x, y) = K (y, x) := by simp [K, weightedSymmetrization, add_comm]
    have hsuppK (x y : E) (hxy : label x ≠ label y) : K (x, y) = 0 := by
      simp [K, weightedSymmetrization, hsupport p x y hxy, hsupport p y x (Ne.symm hxy)]
    -- Row energy localization for `K`
    have hrow : (∫ x, rowIntegral (μ := μ) K x ^ 2 ∂μ) ≤ cap * ∫ z, K z ^ 2 ∂μ.prod μ := by
      have hsec := NearlyMinimax.memLp_sections_left (H := ℝ) (η := fun x y => K (x, y)) hK
      refine (integral_mono_ae (rowIntegral_sq_integrable hK)
        (hK.integrable_sq.integral_prod_left.const_mul cap) ?_).trans_eq
        (by rw [integral_const_mul, integral_prod _ hK.integrable_sq])
      filter_upwards [hsec] with x hKx
      let S := label ⁻¹' {label x}
      have hS : MeasurableSet S := (measurableSet_singleton _).preimage hlabel
      have he1 : S.indicator (fun y => K (x, y)) = fun y => K (x, y) := funext fun y => by
        by_cases hy : y ∈ S
        · exact indicator_of_mem hy _
        · rw [indicator_of_notMem hy]; exact (hsuppK x y (by simpa [S, ne_comm] using hy)).symm
      have he2 : S.indicator (fun y => K (x, y) ^ 2) = fun y => K (x, y) ^ 2 := funext fun y => by
        by_cases hy : y ∈ S
        · exact indicator_of_mem hy _
        · rw [indicator_of_notMem hy, hsuppK x y (by simpa [S, ne_comm] using hy)]; norm_num
      calc rowIntegral (μ := μ) K x ^ 2
        _ = (∫ y in S, K (x, y) ∂μ) ^ 2 := by rw [← integral_indicator hS, he1]; rfl
        _ ≤ (μ.restrict S).real univ * ∫ y in S, K (x, y) ^ 2 ∂μ :=
            LocalizationL2.integral_sq_le_mass_mul_integral_sq (hKx.restrict S)
        _ = μ.real S * ∫ y, K (x, y) ^ 2 ∂μ := by
            rw [Measure.real, Measure.restrict_apply_univ, ← Measure.real, ← integral_indicator hS, he2]
        _ ≤ cap * ∫ y, K (x, y) ^ 2 ∂μ :=
            mul_le_mul_of_nonneg_right (hmass (label x)) (integral_nonneg fun _ => sq_nonneg _)
    -- Mean and energy of `K`
    have hKmean : (∫ z, K z ∂μ.prod μ) = L p := by
      have h1 := hp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have h2 := (hp.comp_measurePreserving Measure.measurePreserving_swap).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have ha' := integral_add h1 h2
      simp only [Function.comp_def] at ha'
      simp only [K, L, fieldPairMean, weightedSymmetrization]
      rw [integral_const_mul, ha', integral_prod_swap (G p)]; ring
    have hKenergy : (∫ z, K z ^ 2 ∂μ.prod μ) ≤ weight ^ 2 / 4 * ∫ z, G p z ^ 2 ∂μ.prod μ := by
      have h1 := hp.integrable_sq
      have h2 := (hp.comp_measurePreserving Measure.measurePreserving_swap).integrable_sq
      refine (integral_mono hK.integrable_sq ((h1.add h2).const_mul (weight ^ 2 / 8)) fun z => ?_).trans_eq ?_
      · dsimp [K, weightedSymmetrization]
        have hs : (G p z + G p z.swap) ^ 2 ≤ 2 * (G p z ^ 2 + G p z.swap ^ 2) := by
          nlinarith [sq_nonneg (G p z - G p z.swap)]
        have hh := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ weight ^ 2 / 16)
        nlinarith
      · have ha' := integral_add (f := fun z => G p z ^ 2) (g := fun z => G p z.swap ^ 2) h1 h2
        change (∫ z : E × E, weight ^ 2 / 8 * (G p z ^ 2 + G p z.swap ^ 2) ∂μ.prod μ) = _
        rw [integral_const_mul, ha', integral_prod_swap (fun z => G p z ^ 2)]; ring
    have hv := pairAverage_centered_sq_le hn X hind hX hmK hK hsym
    rw [hKmean] at hv
    change (∫ x, (T (p, x) - L p) ^ 2 ∂ν) ≤ _ at hv
    have hv' : (∫ x, (T (p, x) - L p) ^ 2 ∂ν) ≤
        (4 / (n : ℝ) * cap + 2 / ((n : ℝ) * (n - 1 : ℕ))) * ∫ z, K z ^ 2 ∂μ.prod μ := by
      refine hv.trans ?_
      have hr' := mul_le_mul_of_nonneg_left hrow (by positivity : 0 ≤ 4 / (n : ℝ))
      nlinarith
    refine (hv'.trans (mul_le_mul_of_nonneg_left hKenergy (by positivity))).trans ?_
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hm0 : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
    have hscale : (4 / (n : ℝ) * cap + 2 / ((n : ℝ) * (n - 1 : ℕ))) * (weight ^ 2 / 4) =
        (weight * cap / (n : ℝ) + weight / (2 * (n : ℝ) * (n - 1 : ℕ))) * weight := by field_simp; ring
    rw [← mul_assoc, hscale]
    dsimp only [a]; rw [← mul_assoc]
    gcongr
  have hb_int : Integrable (fun p => a * (weight * ∫ z, G p z ^ 2 ∂μ.prod μ)) π :=
    (hG.integrable_sq.integral_prod_left.const_mul weight).const_mul a
  have heval : (∫ z, (T z - L z.1) ^ 2 ∂π.prod ν) ≤
      a * (weight * ∫ z : P × (E × E), G z.1 z.2 ^ 2 ∂π.prod (μ.prod μ)) := by
    rw [integral_prod _ hTL.integrable_sq]
    refine (integral_mono_ae hTL.integrable_sq.integral_prod_left hb_int hcond).trans_eq ?_
    rw [integral_const_mul, integral_const_mul, integral_prod _ hG.integrable_sq]
  linarith [hsplit, heval, hmean]

end PairUStatistic

-- 3. Abstract `PilotFields` bilinear fluctuation & masked operator kernel

namespace PilotFields

def test {Ω W H : Type*} [MeasurableSpace W] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {M : Measure W} (η : Ω → W → H) (v : W → H) (x : Ω) : ℝ :=
  ∫ w, ⟪η x w, v w⟫ ∂M

def pilotMean {Ω W H : Type*} [MeasurableSpace W] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {M : Measure W} (m : W → H) (η : Ω → W → H) (B : W → H →L[ℝ] H) (z : Ω × Ω) : ℝ :=
  ∫ w, ⟪m w + η z.1 w, B w (m w + η z.2 w)⟫ ∂M

section InnerAndTest
variable {Ω W H : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {μ : Measure Ω} {M : Measure W} [IsProbabilityMeasure μ] [IsFiniteMeasure M]

theorem inner_integrable {f g : W → H} (hf : MemLp f 2 M) (hg : MemLp g 2 M) :
    Integrable (fun w => ⟪f w, g w⟫) M := by
  refine (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with w hfw hgw
  rw [hfw, hgw]

private theorem inner_integral_sq_le {f g : W → H} (hf : MemLp f 2 M) (hg : MemLp g 2 M) :
    (∫ w, ⟪f w, g w⟫ ∂M) ^ 2 ≤ (∫ w, ‖f w‖ ^ 2 ∂M) * (∫ w, ‖g w‖ ^ 2 ∂M) := by
  have hnorm {u : W → H} (hu : MemLp u 2 M) : ‖hu.toLp u‖ ^ 2 = ∫ w, ‖u w‖ ^ 2 ∂M := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hu.coeFn_toLp] with w hw; rw [hw, real_inner_self_eq_norm_sq]
  have hinn : ⟪hf.toLp f, hg.toLp g⟫ = ∫ w, ⟪f w, g w⟫ ∂M := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with w hfw hgw; rw [hfw, hgw]
  rw [← hinn, ← hnorm hf, ← hnorm hg, ← mul_pow]
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2

private theorem test_memLp_two {η : Ω → W → H}
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    {v : W → H} (hv : MemLp v 2 M) :
    MemLp (test (M := M) η v) 2 μ := by
  have hm0 : AEStronglyMeasurable (fun z : Ω × W => ⟪η z.1 z.2, v z.2⟫) (μ.prod M) :=
    hη.aestronglyMeasurable.inner hv.aestronglyMeasurable.comp_snd
  have hm : AEStronglyMeasurable (test (M := M) η v) μ := hm0.integral_prod_right'
  refine (memLp_two_iff_integrable_sq hm).mpr ?_
  refine (hη.norm.integrable_sq.integral_prod_left.mul_const (∫ w, ‖v w‖ ^ 2 ∂M)).mono' (hm.pow 2) ?_
  filter_upwards [NearlyMinimax.memLp_sections_left hη] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact inner_integral_sq_le hx hv

private theorem test_mean_zero [CompleteSpace H] {η : Ω → W → H}
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    (hcenter : ∀ᵐ w ∂M, (∫ x, η x w ∂μ) = 0)
    {v : W → H} (hv : MemLp v 2 M) :
    (∫ x, test (M := M) η v x ∂μ) = 0 := by
  have hi : Integrable (fun z : Ω × W => ⟪η z.1 z.2, v z.2⟫) (μ.prod M) :=
    inner_integrable hη (hv.comp_measurePreserving measurePreserving_snd)
  change (∫ x, ∫ w, ⟪η x w, v w⟫ ∂M ∂μ) = 0
  rw [← integral_prod _ hi, integral_prod_symm _ hi]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hcenter, hη.aestronglyMeasurable.prodMk_right, hη.norm.integrable_sq.prod_left_ae] with w hw hm hisq
  have hηw : MemLp (fun x => η x w) 2 μ := (memLp_two_iff_integrable_sq_norm hm).mpr hisq
  calc (∫ x, ⟪η x w, v w⟫ ∂μ) = ∫ x, ⟪v w, η x w⟫ ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun _ => real_inner_comm _ _)
    _ = ⟪v w, ∫ x, η x w ∂μ⟫ := integral_inner (hηw.integrable (by norm_num)) _
    _ = 0 := by rw [hw]; simp

end InnerAndTest

section OperatorAndSectionBounds
variable {Ω W H : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {μ : Measure Ω} {M : Measure W} [IsProbabilityMeasure μ] [IsFiniteMeasure M]

theorem operatorField_memLp {B : W → H →L[ℝ] H}
    (hmB : Measurable (fun z : W × H => B z.1 z.2)) {C : ℝ} (hbound : ∀ w, ‖B w‖ ≤ C)
    {f : W → H} (hmf : Measurable f) (hf : MemLp f 2 M) :
    MemLp (fun w => B w (f w)) 2 M :=
  hf.of_le_mul (c := C) (hmB.comp (measurable_id.prodMk hmf)).aestronglyMeasurable <|
    Filter.Eventually.of_forall fun w => ((B w).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hbound w) (norm_nonneg _))

theorem memLp_joint_of_uniform_section_energy {η : Ω → W → H}
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : ∀ᵐ w ∂M, MemLp (fun x => η x w) 2 μ)
    {R : ℝ} (_hR : 0 ≤ R) (hE : ∀ᵐ w ∂M, (∫ x, ‖η x w‖ ^ 2 ∂μ) ≤ R) :
    MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M) := by
  have hm : AEStronglyMeasurable (fun z : Ω × W => ‖η z.1 z.2‖ ^ 2) (μ.prod M) :=
    hmη.aestronglyMeasurable.norm.pow 2
  refine (memLp_two_iff_integrable_sq_norm hmη.aestronglyMeasurable).mpr ((integrable_prod_iff' hm).mpr ⟨?_, ?_⟩)
  · exact hη.mono fun _ hw => hw.norm.integrable_sq
  · refine (integrable_const R).mono' hm.norm.prod_swap.integral_prod_right' ?_
    filter_upwards [hE] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simpa only [Function.comp_def, Prod.swap_prod_mk, norm_pow, Real.norm_eq_abs, sq_abs] using hw

theorem joint_energy_le_of_uniform_sections {η : Ω → W → H}
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : ∀ᵐ w ∂M, MemLp (fun x => η x w) 2 μ)
    {R : ℝ} (hR : 0 ≤ R) (hE : ∀ᵐ w ∂M, (∫ x, ‖η x w‖ ^ 2 ∂μ) ≤ R) :
    (∫ z : Ω × W, ‖η z.1 z.2‖ ^ 2 ∂μ.prod M) ≤ R * M.real Set.univ := by
  have hi := (memLp_joint_of_uniform_section_energy hmη hη hR hE).norm.integrable_sq
  rw [integral_prod_symm _ hi]
  exact (integral_mono_ae hi.integral_prod_right (integrable_const R) hE).trans_eq (by simp [integral_const, mul_comm])

theorem half_pilotMean_facts [CompleteSpace H] (m : W → H) (hmm : Measurable m) (hm : MemLp m 2 M)
    {η : Ω → W → H} (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    (hcenter : ∀ᵐ w ∂M, (∫ x, η x w ∂μ) = 0)
    {B : W → H →L[ℝ] H} (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {cB lam : ℝ} (hcB : 0 ≤ cB) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ cB)
    (hsym : ∀ w x y, ⟪x, B w y⟫ = ⟪B w x, y⟫)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M)
    (G : Ω × Ω → ℝ) (he : G =ᵐ[μ.prod μ] fun x => (1 / 2) * pilotMean (M := M) m η B x) :
    (∫ x, G x ∂μ.prod μ) = (1 / 2) * (∫ w, ⟪m w, B w (m w)⟫ ∂M) ∧
      MemLp G 2 (μ.prod μ) ∧
      (∫ x, (G x - ∫ z, G z ∂μ.prod μ) ^ 2 ∂μ.prod μ) ≤
        (3 / 4) * lam * cB ^ 2 * (2 * (∫ w, ‖m w‖ ^ 2 ∂M) + ∫ z : Ω × W, ‖η z.1 z.2‖ ^ 2 ∂μ.prod M) := by
  let v := fun w => B w (m w)
  have hv : MemLp v 2 M := operatorField_memLp hmB hbound hmm hm
  have hv_en : (∫ w, ‖v w‖ ^ 2 ∂M) ≤ cB ^ 2 * ∫ w, ‖m w‖ ^ 2 ∂M := by
    rw [← integral_const_mul]
    refine integral_mono hv.norm.integrable_sq (hm.norm.integrable_sq.const_mul _) fun w => ?_
    calc ‖B w (m w)‖ ^ 2 ≤ (cB * ‖m w‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (((B w).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hbound w) (norm_nonneg _))) 2
      _ = cB ^ 2 * ‖m w‖ ^ 2 := by ring
  -- Bilinear fluctuation `bil z = ∫ w, ⟪η z.1 w, B w (η z.2 w)⟫ ∂M`
  let bil (z : Ω × Ω) : ℝ := ∫ w, ⟪η z.1 w, B w (η z.2 w)⟫ ∂M
  have hm_bil : Measurable bil :=
    ((hmη.comp (measurable_fst.fst.prodMk measurable_snd)).inner
      (hmB.comp (measurable_snd.prodMk (hmη.comp (measurable_fst.snd.prodMk measurable_snd))))).stronglyMeasurable.integral_prod_right'.measurable
  have hbil_sec {y : Ω} (hy : MemLp (η y) 2 M) :
      (∫ x, bil (x, y) ^ 2 ∂μ) ≤ lam * cB ^ 2 * ∫ w, ‖η y w‖ ^ 2 ∂M := by
    have hmy : Measurable (η y) := hmη.comp (measurable_const.prodMk measurable_id)
    have hBy := operatorField_memLp hmB hbound hmy hy
    have hBy_en : (∫ w, ‖B w (η y w)‖ ^ 2 ∂M) ≤ cB ^ 2 * ∫ w, ‖η y w‖ ^ 2 ∂M := by
      rw [← integral_const_mul]
      refine integral_mono hBy.norm.integrable_sq (hy.norm.integrable_sq.const_mul _) fun w => ?_
      calc ‖B w (η y w)‖ ^ 2 ≤ (cB * ‖η y w‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (((B w).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hbound w) (norm_nonneg _))) 2
        _ = cB ^ 2 * ‖η y w‖ ^ 2 := by ring
    simpa only [test, bil, mul_assoc] using (htest _ hBy).trans (mul_le_mul_of_nonneg_left hBy_en hlam)
  have hbil_sq_int : Integrable (fun z => bil z ^ 2) (μ.prod μ) := by
    have hmZ : AEStronglyMeasurable (fun z : Ω × Ω => bil z ^ 2) (μ.prod μ) :=
      hm_bil.aestronglyMeasurable.pow 2
    refine (integrable_prod_iff' hmZ).mpr ⟨?_, ?_⟩
    · filter_upwards [NearlyMinimax.memLp_sections_left hη] with y hy
      have hmy : Measurable (η y) := hmη.comp (measurable_const.prodMk measurable_id)
      exact (test_memLp_two hη (operatorField_memLp hmB hbound hmy hy)).integrable_sq
    · refine (hη.norm.integrable_sq.integral_prod_left.const_mul (lam * cB ^ 2)).mono' hmZ.norm.prod_swap.integral_prod_right' ?_
      filter_upwards [NearlyMinimax.memLp_sections_left hη] with y hy
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      simp only [norm_pow, Real.norm_eq_abs, sq_abs]
      exact hbil_sec hy
  have hbil_L2 : MemLp bil 2 (μ.prod μ) := (memLp_two_iff_integrable_sq hm_bil.aestronglyMeasurable).mpr hbil_sq_int
  have hbil_en : (∫ z, bil z ^ 2 ∂μ.prod μ) ≤ lam * cB ^ 2 * ∫ z : Ω × W, ‖η z.1 z.2‖ ^ 2 ∂μ.prod M := by
    rw [integral_prod_symm _ hbil_sq_int]
    refine (integral_mono_ae hbil_sq_int.integral_prod_right
      (hη.norm.integrable_sq.integral_prod_left.const_mul (lam * cB ^ 2)) ?_).trans_eq
      (by rw [integral_const_mul, integral_prod _ hη.norm.integrable_sq])
    filter_upwards [NearlyMinimax.memLp_sections_left hη] with y hy
    exact hbil_sec hy
  have hbil_mean0 : (∫ z, bil z ∂μ.prod μ) = 0 := by
    rw [integral_prod_symm _ (hbil_L2.integrable (by norm_num))]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [NearlyMinimax.memLp_sections_left hη] with y hy
    have hmy : Measurable (η y) := hmη.comp (measurable_const.prodMk measurable_id)
    exact test_mean_zero hη hcenter (operatorField_memLp hmB hbound hmy hy)
  -- Fluctuation decomposition `pilotMean = fluc + ∫ ⟪m, B m⟫` a.e.
  let fluc (z : Ω × Ω) : ℝ := test (M := M) η v z.1 + test (M := M) η v z.2 + bil z
  let det : ℝ := ∫ w, ⟪m w, B w (m w)⟫ ∂M
  have ht_L2 : MemLp (test (M := M) η v) 2 μ := test_memLp_two hη hv
  have hfluc_L2 : MemLp fluc 2 (μ.prod μ) :=
    ((ht_L2.comp_measurePreserving measurePreserving_fst).add
      (ht_L2.comp_measurePreserving measurePreserving_snd)).add hbil_L2
  have hdecomp : pilotMean (M := M) m η B =ᵐ[μ.prod μ] fun z => fluc z + det := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae (NearlyMinimax.memLp_sections_left hη),
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae (NearlyMinimax.memLp_sections_left hη)] with z hx hy
    have hmy : Measurable (η z.2) := hmη.comp (measurable_const.prodMk measurable_id)
    have hBy := operatorField_memLp hmB hbound hmy hy
    have h0 := inner_integrable hm hv
    have h1 := inner_integrable hx hv
    have h2 := inner_integrable hy hv
    have h3 := inner_integrable hx hBy
    have hpt : (fun w => ⟪m w + η z.1 w, B w (m w + η z.2 w)⟫) =
        fun w => ⟪m w, B w (m w)⟫ + ⟪η z.1 w, v w⟫ + ⟪η z.2 w, v w⟫ + ⟪η z.1 w, B w (η z.2 w)⟫ := funext fun w => by
      dsimp [v]; rw [map_add, inner_add_left, inner_add_right, inner_add_right, hsym w (m w) (η z.2 w),
        real_inner_comm (B w (m w)) (η z.2 w)]; ring
    have ha := integral_add ((h0.add h1).add h2) h3
    have hb := integral_add (h0.add h1) h2
    have hc := integral_add h0 h1
    simp only [Pi.add_apply] at ha hb hc
    simp only [pilotMean, fluc, det, test, bil]
    rw [hpt, ha, hb, hc]; ring
  have hfluc_mean0 : (∫ z, fluc z ∂μ.prod μ) = 0 := by
    have h1 := (ht_L2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).comp_fst μ
    have h2 := (ht_L2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).comp_snd μ
    have h3 := hbil_L2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have ha := integral_add (h1.add h2) h3
    have hb := integral_add h1 h2
    simp only [Pi.add_apply] at ha hb
    change (∫ z : Ω × Ω, test (M := M) η v z.1 + test (M := M) η v z.2 + bil z ∂μ.prod μ) = 0
    rw [ha, hb, integral_fun_fst, integral_fun_snd, test_mean_zero hη hcenter hv, hbil_mean0]; simp
  have hG_ae : G =ᵐ[μ.prod μ] fun z => (1 / 2) * fluc z + (1 / 2) * det := by
    filter_upwards [he, hdecomp] with z hz hd
    rw [hz, hd]; ring
  have hG_mean : (∫ x, G x ∂μ.prod μ) = (1 / 2) * det := by
    rw [integral_congr_ae hG_ae,
      integral_add ((hfluc_L2.integrable (by norm_num)).const_mul (1 / 2)) (integrable_const _),
      integral_const_mul, hfluc_mean0]; simp
  have hG_L2 : MemLp G 2 (μ.prod μ) := ((hfluc_L2.const_mul (1 / 2)).add (memLp_const _)).ae_eq hG_ae.symm
  refine ⟨hG_mean, hG_L2, ?_⟩
  have hsq_ae : (fun x => (G x - ∫ z, G z ∂μ.prod μ) ^ 2) =ᵐ[μ.prod μ] fun x => (1 / 4) * fluc x ^ 2 := by
    filter_upwards [hG_ae] with x hx; rw [hx, hG_mean]; ring
  rw [integral_congr_ae hsq_ae, integral_const_mul]
  -- Bound `∫ fluc^2 ≤ 3 * lam * cB^2 * (2 * ∫ ‖m‖^2 + ∫ ‖η‖^2)`
  have h1 := ht_L2.integrable_sq.comp_fst μ
  have h2 := ht_L2.integrable_sq.comp_snd μ
  have hfluc_en : (∫ z, fluc z ^ 2 ∂μ.prod μ) ≤
      3 * lam * cB ^ 2 * (2 * (∫ w, ‖m w‖ ^ 2 ∂M) + ∫ z : Ω × W, ‖η z.1 z.2‖ ^ 2 ∂μ.prod M) := by
    refine (integral_mono (g := fun z => 3 * (test (M := M) η v z.1 ^ 2 + test (M := M) η v z.2 ^ 2 + bil z ^ 2))
      hfluc_L2.integrable_sq (((h1.add h2).add hbil_sq_int).const_mul 3) fun z => ?_).trans ?_
    · dsimp [fluc]; nlinarith [sq_nonneg (test (M := M) η v z.1 - test (M := M) η v z.2),
        sq_nonneg (test (M := M) η v z.1 - bil z), sq_nonneg (test (M := M) η v z.2 - bil z)]
    · have ha := integral_add (h1.add h2) hbil_sq_int
      have hb := integral_add h1 h2
      simp only [Pi.add_apply] at ha hb
      rw [integral_const_mul, ha, hb,
        integral_fun_fst (μ := μ) (ν := μ) (fun x => test (M := M) η v x ^ 2),
        integral_fun_snd (μ := μ) (ν := μ) (fun x => test (M := M) η v x ^ 2)]
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
      have ht_bd := (htest v hv).trans (mul_le_mul_of_nonneg_left hv_en hlam)
      nlinarith [ht_bd, hbil_en]
  nlinarith [hfluc_en]

end OperatorAndSectionBounds

section MaskedKernel
variable {Ω W H : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {μ : Measure Ω} {ν : Measure W} [IsProbabilityMeasure μ] [SFinite ν]

def maskedPilotKernel (c : Ω → W → H) (A : W → H →L[ℝ] H) (q : W → ℝ) (z : (Ω × Ω) × W) : ℝ :=
  q z.2 * ⟪c z.1.1 z.2, A z.2 (c z.1.2 z.2)⟫

theorem maskedPilotKernel_measurable {c : Ω → W → H} (hmc : Measurable (fun z : Ω × W => c z.1 z.2))
    {A : W → H →L[ℝ] H} (hmA : Measurable (fun z : W × H => A z.1 z.2))
    {q : W → ℝ} (hmq : Measurable q) : Measurable (maskedPilotKernel c A q) :=
  (hmq.comp measurable_snd).mul ((hmc.comp (measurable_fst.fst.prodMk measurable_snd)).inner
    (hmA.comp (measurable_snd.prodMk (hmc.comp (measurable_fst.snd.prodMk measurable_snd)))))

theorem maskedPilotKernel_facts {c : Ω → W → H} (hmc : Measurable (fun z : Ω × W => c z.1 z.2))
    {A : W → H →L[ℝ] H} (hmA : Measurable (fun z : W × H => A z.1 z.2))
    {q : W → ℝ} (hmq : Measurable q) (hq : ∀ w, q w ^ 2 = q w)
    (hA : Integrable (fun w => q w * ‖A w‖ ^ 2) ν)
    (hc : ∀ᵐ w ∂ν, q w ≠ 0 → MemLp (fun x => c x w) 2 μ)
    {L : ℝ} (hL : 0 ≤ L) (hE : ∀ᵐ w ∂ν, q w ≠ 0 → (∫ x, ‖c x w‖ ^ 2 ∂μ) ≤ L) :
    MemLp (maskedPilotKernel c A q) 2 ((μ.prod μ).prod ν) ∧
      (∫ z, maskedPilotKernel c A q z ^ 2 ∂(μ.prod μ).prod ν) ≤ L ^ 2 * ∫ w, q w * ‖A w‖ ^ 2 ∂ν := by
  let c' (x : Ω) (w : W) : H := if q w = 0 then 0 else c x w
  have hmc' : Measurable (fun z : Ω × W => c' z.1 z.2) :=
    Measurable.ite ((hmq.comp measurable_snd) (measurableSet_singleton 0)) measurable_const hmc
  have heq_k : maskedPilotKernel c' A q = maskedPilotKernel c A q := funext fun z => by
    by_cases hz : q z.2 = 0 <;> simp [maskedPilotKernel, c', hz]
  have hc' : ∀ᵐ w ∂ν, MemLp (fun x => c' x w) 2 μ := by
    filter_upwards [hc] with w hw
    by_cases hz : q w = 0
    · simpa [c', hz] using (memLp_const (μ := μ) (p := 2) (0 : H))
    · simpa [c', hz] using hw hz
  have hE' : ∀ᵐ w ∂ν, (∫ x, ‖c' x w‖ ^ 2 ∂μ) ≤ L := by
    filter_upwards [hE] with w hw
    by_cases hz : q w = 0 <;> simp [c', hz, hL, hw]
  have hq_nn (w : W) : 0 ≤ q w := (hq w).symm ▸ sq_nonneg (q w)
  have hop_sq (T : H →L[ℝ] H) (u v : H) : ⟪u, T v⟫ ^ 2 ≤ ‖T‖ ^ 2 * (‖u‖ ^ 2 * ‖v‖ ^ 2) := by
    have h := (abs_real_inner_le_norm u (T v)).trans (mul_le_mul_of_nonneg_left (T.le_opNorm v) (norm_nonneg u))
    exact (show ⟪u, T v⟫ ^ 2 ≤ (‖u‖ * (‖T‖ * ‖v‖)) ^ 2 by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2).trans_eq (by ring)
  have hsec_int {w : W} (hw : MemLp (fun x => c' x w) 2 μ) :
      Integrable (fun z : Ω × Ω => maskedPilotKernel c' A q (z, w) ^ 2) (μ.prod μ) ∧
      (∫ x, ‖c' x w‖ ^ 2 ∂μ ≤ L →
        (∫ z : Ω × Ω, maskedPilotKernel c' A q (z, w) ^ 2 ∂μ.prod μ) ≤ L ^ 2 * (q w * ‖A w‖ ^ 2)) := by
    have hm_in : AEStronglyMeasurable (fun z : Ω × Ω => ⟪c' z.1 w, A w (c' z.2 w)⟫ ^ 2) (μ.prod μ) :=
      (hw.aestronglyMeasurable.comp_fst.inner
        ((A w).continuous.comp_aestronglyMeasurable hw.aestronglyMeasurable.comp_snd)).pow 2
    have hdom := (hw.norm.integrable_sq.mul_prod hw.norm.integrable_sq).const_mul (‖A w‖ ^ 2)
    have hin_int : Integrable (fun z : Ω × Ω => ⟪c' z.1 w, A w (c' z.2 w)⟫ ^ 2) (μ.prod μ) :=
      hdom.mono' hm_in <| Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hop_sq (A w) _ _
    have hsq_eq : (fun z : Ω × Ω => maskedPilotKernel c' A q (z, w) ^ 2) =
        fun z => q w * ⟪c' z.1 w, A w (c' z.2 w)⟫ ^ 2 := funext fun z => by
      simp only [maskedPilotKernel, mul_pow, hq]
    rw [hsq_eq]
    refine ⟨hin_int.const_mul (q w), fun hEw => ?_⟩
    rw [integral_const_mul]
    have hprod_le : (∫ z : Ω × Ω, ⟪c' z.1 w, A w (c' z.2 w)⟫ ^ 2 ∂μ.prod μ) ≤ ‖A w‖ ^ 2 * L ^ 2 := by
      refine (integral_mono hin_int hdom fun z => hop_sq (A w) _ _).trans ?_
      rw [integral_const_mul, integral_prod_mul (fun x : Ω => ‖c' x w‖ ^ 2) (fun x : Ω => ‖c' x w‖ ^ 2)]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [sq] using pow_le_pow_left₀ (integral_nonneg fun _ => sq_nonneg _) hEw 2) (sq_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left hprod_le (hq_nn w)]
  have hm_sq : AEStronglyMeasurable (fun z => maskedPilotKernel c' A q z ^ 2) ((μ.prod μ).prod ν) :=
    (maskedPilotKernel_measurable hmc' hmA hmq).aestronglyMeasurable.pow 2
  have hsq_int : Integrable (fun z => maskedPilotKernel c' A q z ^ 2) ((μ.prod μ).prod ν) := by
    refine (integrable_prod_iff' hm_sq).mpr ⟨hc'.mono fun _ hw => (hsec_int hw).1, ?_⟩
    refine (hA.const_mul (L ^ 2)).mono' hm_sq.norm.prod_swap.integral_prod_right' ?_
    filter_upwards [hc', hE'] with w hcw hEw
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simpa only [Function.comp_def, Prod.swap_prod_mk, norm_pow, Real.norm_eq_abs, sq_abs] using (hsec_int hcw).2 hEw
  rw [← heq_k]
  refine ⟨(memLp_two_iff_integrable_sq (maskedPilotKernel_measurable hmc' hmA hmq).aestronglyMeasurable).mpr hsq_int, ?_⟩
  rw [integral_prod_symm _ hsq_int, ← integral_const_mul]
  refine integral_mono_ae hsq_int.integral_prod_right (hA.const_mul _) ?_
  filter_upwards [hc', hE'] with w hcw hEw
  exact (hsec_int hcw).2 hEw

end MaskedKernel
end PilotFields

-- 4. Response operator conditional mean & fourth-moment energy

def responseOperatorEnergyBound {d : ℕ} (C : ModelConstants d) : ℝ :=
  12 * responseFourthBound C + 6 + 8 * C.varianceUpper ^ 2

theorem responseOperatorEnergyBound_pos {d : ℕ} (C : ModelConstants d) :
    0 < responseOperatorEnergyBound C := by
  have := responseFourthBound_pos C; unfold responseOperatorEnergyBound; positivity

def pairCovariates {d : ℕ} (z : Observation d × Observation d) : Covariate d × Covariate d :=
  (z.1.1, z.2.1)

private theorem observationPairScoreOperator_measurable_apply {d : ℕ} (V : ℝ) :
    Measurable (fun z : (Observation d × Observation d) × PairVector =>
      pairScoreOperator V z.1.1.2 z.1.2.2 z.2) :=
  (((pairScoreOperator_continuous V).comp (continuous_fst.fst.snd.prodMk continuous_fst.snd.snd)).clm_apply
    continuous_snd).measurable

private theorem regular_response_operator_energy {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    Integrable (fun z : Observation d × Observation d =>
      sameLabelKernel (regularObservationLabel k hk) z * ‖pairScoreOperator θ.variance z.1.2 z.2.2‖ ^ 2)
      ((observationLaw θ).prod (observationLaw θ)) ∧
    (∫ z : Observation d × Observation d,
      sameLabelKernel (regularObservationLabel k hk) z * ‖pairScoreOperator θ.variance z.1.2 z.2.2‖ ^ 2
        ∂(observationLaw θ).prod (observationLaw θ)) ≤
      responseOperatorEnergyBound C * (C.densityUpper / (k : ℝ) ^ d) := by
  classical
  let μ := observationLaw θ
  let _ := observationLaw_isProbability C θ hθ
  let lbl := regularObservationLabel (d := d) k hk
  have hlbl : Measurable lbl := regularObservationLabel_measurable k hk
  have hr4 : Integrable (fun x : Observation d => x.2 ^ 4) μ := observationLaw_response_fourth_integrable C θ hθ
  let G := labelLocalizedKernel lbl (fun x : Observation d => x.2 ^ 4)
  have hG : Integrable G (μ.prod μ) := labelLocalizedKernel_integrable μ lbl hlbl _ hr4
  have hGs : Integrable (fun z : Observation d × Observation d => G z.swap) (μ.prod μ) := integrable_swap_iff.mpr hG
  have hq := (sameLabelKernel_memLp μ lbl hlbl).integrable (by norm_num)
  let dom (z : Observation d × Observation d) :=
    6 * G z + 6 * G z.swap + (6 + 8 * θ.variance ^ 2) * sameLabelKernel lbl z
  have hdom : Integrable dom (μ.prod μ) := ((hG.const_mul 6).add (hGs.const_mul 6)).add (hq.const_mul _)
  have hm : Measurable (fun z : Observation d × Observation d =>
      sameLabelKernel lbl z * ‖pairScoreOperator θ.variance z.1.2 z.2.2‖ ^ 2) :=
    (sameLabelKernel_measurable lbl hlbl).mul
      (((pairScoreOperator_continuous θ.variance).measurable.comp
        (measurable_fst.snd.prodMk measurable_snd.snd)).norm.pow_const 2)
  have hpt (z : Observation d × Observation d) :
      sameLabelKernel lbl z * ‖pairScoreOperator θ.variance z.1.2 z.2.2‖ ^ 2 ≤ dom z := by
    by_cases he : lbl z.1 = lbl z.2
    · have hb := pairScoreOperator_norm_sq_le θ.variance z.1.2 z.2.2
      simp only [dom, sameLabelKernel, he, ↓reduceIte, labelLocalizedKernel, G,
        Prod.fst_swap, Prod.snd_swap, eq_comm, one_mul, mul_one]
      nlinarith [hb]
    · simp [dom, sameLabelKernel, labelLocalizedKernel, G, he, Ne.symm he]
  have hint : Integrable (fun z : Observation d × Observation d =>
      sameLabelKernel lbl z * ‖pairScoreOperator θ.variance z.1.2 z.2.2‖ ^ 2) (μ.prod μ) := by
    refine hdom.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by unfold sameLabelKernel; split_ifs <;> norm_num) (sq_nonneg _))]
    exact hpt z
  refine ⟨hint, ?_⟩
  have hupper := labelLocalizedKernel_integral_le μ lbl hlbl _ hr4 (responseFourthBound C) fun i => by
    rw [regularObservationLabel_mass C θ hθ k hk i, regularObservationLabel_fiber k hk i]
    exact observationLaw_localized_fourth_integral_le C θ hθ _
      ((measurableSet_singleton i).preimage (regular_grid_cell_measurable k hk))
  have hb := integral_mono hint hdom hpt
  have ha := integral_add ((hG.const_mul 6).add (hGs.const_mul 6)) (hq.const_mul (6 + 8 * θ.variance ^ 2))
  have ha' := integral_add (hG.const_mul 6) (hGs.const_mul 6)
  simp only [Pi.add_apply, Pi.mul_apply] at ha ha'
  dsimp only [dom] at hb
  rw [ha, ha', integral_const_mul, integral_const_mul, integral_const_mul,
    integral_prod_swap G, sameLabelKernel_integral μ lbl hlbl] at hb
  dsimp only [μ, lbl] at hb hupper
  simp_rw [regularObservationLabel_mass C θ hθ k hk] at hb hupper
  change _ ≤ _ * regularGridCollisionMass θ k hk at hupper
  change _ ≤ _ + _ * regularGridCollisionMass θ k hk at hb
  have hV0 : 0 ≤ θ.variance := C.varianceLower_pos.le.trans hθ.2.2.2.2.2.1
  have hvsq : θ.variance ^ 2 ≤ C.varianceUpper ^ 2 := pow_le_pow_left₀ hV0 hθ.2.2.2.2.2.2.1 2
  have hmass_nn : 0 ≤ regularGridCollisionMass θ k hk := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : (∫ z, sameLabelKernel lbl z * ‖pairScoreOperator θ.variance z.1.2 z.2.2‖ ^ 2 ∂μ.prod μ) ≤
      responseOperatorEnergyBound C * regularGridCollisionMass θ k hk := by
    unfold responseOperatorEnergyBound
    nlinarith [hb, hupper, mul_le_mul_of_nonneg_right hvsq hmass_nn]
  exact h1.trans (mul_le_mul_of_nonneg_left (regularGridCollisionMass_upper C θ hθ k hk) (responseOperatorEnergyBound_pos C).le)

private theorem observationPair_integral_conditioning {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (g : Observation d × Observation d → ℝ)
    (hg : Integrable g ((observationLaw θ).prod (observationLaw θ))) :
    (∫ z, g z ∂(observationLaw θ).prod (observationLaw θ)) =
      ∫ x : Covariate d × Covariate d,
        ∫ u : ℝ × ℝ, g ((x.1, θ.regression x.1 + u.1), (x.2, θ.regression x.2 + u.2))
          ∂(θ.errors x.1).prod (θ.errors x.2)
        ∂(designLaw θ).prod (designLaw θ) := by
  let _ := observationLaw_isProbability C θ hθ
  let _ := designLaw_isProbability C θ hθ
  have ho := measurePreserving_finTwoArrow (observationLaw θ)
  have hd := measurePreserving_finTwoArrow (designLaw θ)
  have hs := sampleLaw_integral_conditioning C θ hθ _ (ho.integrable_comp_of_integrable hg)
  have he (x : Fin 2 → Covariate d) :
      (∫ u, g ((x 0, θ.regression (x 0) + u 0), (x 1, θ.regression (x 1) + u 1)) ∂conditionalErrorLaw θ x) =
      ∫ u : ℝ × ℝ, g ((x 0, θ.regression (x 0) + u.1), (x 1, θ.regression (x 1) + u.2))
        ∂(θ.errors (x 0)).prod (θ.errors (x 1)) :=
    (measurePreserving_piFinTwo (fun i : Fin 2 => θ.errors (x i))).integral_comp'
      fun u : ℝ × ℝ => g ((x 0, θ.regression (x 0) + u.1), (x 1, θ.regression (x 1) + u.2))
  calc (∫ z, g z ∂(observationLaw θ).prod (observationLaw θ))
    _ = ∫ z : Fin 2 → Observation d, g (z 0, z 1) ∂sampleLaw θ 2 := (ho.integral_comp' g).symm
    _ = ∫ x : Fin 2 → Covariate d,
          ∫ u, g ((x 0, θ.regression (x 0) + u 0), (x 1, θ.regression (x 1) + u 1))
            ∂conditionalErrorLaw θ x ∂designVectorLaw θ 2 := hs
    _ = ∫ x : Fin 2 → Covariate d,
          ∫ u : ℝ × ℝ, g ((x 0, θ.regression (x 0) + u.1), (x 1, θ.regression (x 1) + u.2))
            ∂(θ.errors (x 0)).prod (θ.errors (x 1)) ∂designVectorLaw θ 2 := by simp_rw [he]
    _ = _ := hd.integral_comp' fun x : Covariate d × Covariate d =>
          ∫ u : ℝ × ℝ, g ((x.1, θ.regression x.1 + u.1), (x.2, θ.regression x.2 + u.2))
            ∂(θ.errors x.1).prod (θ.errors x.2)

private theorem conditional_pairScoreOperator_integral (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp (fun u : ℝ => u) 2 μ) (hν : MemLp (fun u : ℝ => u) 2 ν)
    (hmμ : (∫ u : ℝ, u ∂μ) = 0) (hmν : (∫ u : ℝ, u ∂ν) = 0)
    {V : ℝ} (h2μ : (∫ u : ℝ, u ^ 2 ∂μ) = V) (h2ν : (∫ u : ℝ, u ^ 2 ∂ν) = V)
    (f f' : ℝ) (a b : PairVector) :
    (∫ z : ℝ × ℝ, ⟪a, pairScoreOperator V (f + z.1) (f' + z.2) b⟫ ∂μ.prod ν) =
      ⟪a, InnerProductSpace.rankOne ℝ (pairResponseVector f f') (pairResponseVector f f') b⟫ := by
  let Y (u : ℝ) := f + u
  let Y' (u : ℝ) := f' + u
  have hY : MemLp Y 2 μ := (memLp_const f).add hμ
  have hY' : MemLp Y' 2 ν := (memLp_const f').add hν
  have hm : (∫ u, Y u ∂μ) = f := by rw [integral_add (integrable_const _) (hμ.integrable (by norm_num)), hmμ]; simp
  have hm' : (∫ u, Y' u ∂ν) = f' := by rw [integral_add (integrable_const _) (hν.integrable (by norm_num)), hmν]; simp
  have h2 := response_second_moment_of_centered_error hμ hmμ h2μ f
  have h2' := response_second_moment_of_centered_error hν hmν h2ν f'
  have hi := hY.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hi' := hY'.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h0 := (hY'.integrable_sq.comp_snd μ).const_mul (a 0 * b 0)
  have h1 := (hY.integrable_sq.comp_fst ν).const_mul (a 1 * b 1)
  have h2i := (hi.mul_prod hi').const_mul (a 0 * b 1 + a 1 * b 0)
  have h3 := (hi'.comp_snd μ).const_mul (a 0 * b 2 + a 2 * b 0)
  have h4 := (hi.comp_fst ν).const_mul (a 1 * b 2 + a 2 * b 1)
  have h5 : Integrable (fun _ : ℝ × ℝ => a 2 * b 2) (μ.prod ν) := integrable_const _
  have h6 : Integrable (fun _ : ℝ × ℝ => V * (a 0 * b 0 + a 1 * b 1)) (μ.prod ν) := integrable_const _
  have ha0 := integral_add h0 h1
  have ha1 := integral_add (h0.add h1) h2i
  have ha2 := integral_add ((h0.add h1).add h2i) h3
  have ha3 := integral_add (((h0.add h1).add h2i).add h3) h4
  have ha4 := integral_add ((((h0.add h1).add h2i).add h3).add h4) h5
  have ha5 := integral_sub (((((h0.add h1).add h2i).add h3).add h4).add h5) h6
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply] at ha0 ha1 ha2 ha3 ha4 ha5
  change (∫ z : ℝ × ℝ, ⟪a, pairScoreOperator V (Y z.1) (Y' z.2) b⟫ ∂μ.prod ν) = _
  simp_rw [pairScoreOperator_inner_polynomial]
  rw [ha5, ha4, ha3, ha2, ha1, ha0]
  have hs0 : (∫ z : ℝ × ℝ, Y' z.2 ^ 2 ∂μ.prod ν) = f' ^ 2 + V := by
    calc (∫ z : ℝ × ℝ, Y' z.2 ^ 2 ∂μ.prod ν)
      _ = ∫ x, Y' x ^ 2 ∂ν := by
          simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using
            integral_fun_snd (μ := μ) (ν := ν) fun x => Y' x ^ 2
      _ = f' ^ 2 + V := h2'
  have hs1 : (∫ z : ℝ × ℝ, Y z.1 ^ 2 ∂μ.prod ν) = f ^ 2 + V := by
    calc (∫ z : ℝ × ℝ, Y z.1 ^ 2 ∂μ.prod ν)
      _ = ∫ x, Y x ^ 2 ∂μ := by
          simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using
            integral_fun_fst (μ := μ) (ν := ν) fun x => Y x ^ 2
      _ = f ^ 2 + V := h2
  simp only [integral_const_mul, integral_fun_snd, integral_fun_fst, integral_prod_mul,
    hm, hm', hs0, hs1, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, integral_const,
    InnerProductSpace.inner_right_rankOne_apply, pairResponseVector_inner]
  rw [real_inner_comm b (pairResponseVector f f'), pairResponseVector_inner]; ring

-- 5. `PairPilotAssumptions`, `TwoScalarPilotVector`, & `PairPilotFromScalars`

def pairPilotCoefficient {Ω : Type*} {d : ℕ} (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector) (x : Ω)
    (w : Covariate d × Covariate d) : PairVector := bar w + η x w

theorem regularPairDesignMeasure_ae_of_supported {d : ℕ}
    (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k)
    {P : Covariate d × Covariate d → Prop}
    (hp : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 → P w) :
    ∀ᵐ w ∂regularPairDesignMeasure θ k hk, P w := by
  change ∀ᵐ w ∂ENNReal.ofReal ((k : ℝ) ^ d) •
    ((designLaw θ).prod (designLaw θ)).restrict
      {z | regularGridCell k hk z.1 = regularGridCell k hk z.2}, P w
  apply Measure.ae_smul_measure
  apply (ae_restrict_iff' (measurableSet_eq_fun
    ((regular_grid_cell_measurable k hk).comp measurable_fst)
    ((regular_grid_cell_measurable k hk).comp measurable_snd))).mpr
  filter_upwards [hp] with w hw hs
  have hs' : regularGridCell k hk w.1 = regularGridCell k hk w.2 := hs
  exact hw (by simp [sameLabelKernel, hs'])

structure PairPilotAssumptions {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k) (μ : Measure Ω)
    (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector) (Cp W lam : ℝ) : Prop where
  constantNonnegative : 0 ≤ Cp
  budgetNonnegative : 0 ≤ W
  barMeasurable : Measurable bar
  noiseMeasurable : Measurable (fun z : Ω × (Covariate d × Covariate d) => η z.1 z.2)
  barBound : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
    sameLabelKernel (regularGridCell k hk) w ≠ 0 → ‖bar w‖ ≤ Cp
  noiseSection : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
    sameLabelKernel (regularGridCell k hk) w ≠ 0 → MemLp (fun x => η x w) 2 μ
  noiseEnergy : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
    sameLabelKernel (regularGridCell k hk) w ≠ 0 → (∫ x, ‖η x w‖ ^ 2 ∂μ) ≤ Cp * W
  noiseCentered : ∀ᵐ w ∂regularPairDesignMeasure θ k hk, (∫ x, η x w ∂μ) = 0
  lamNonnegative : 0 ≤ lam
  linearTest : ∀ v : (Covariate d × Covariate d) → PairVector,
    MemLp v 2 (regularPairDesignMeasure θ k hk) →
    (∫ x, PilotFields.test (M := regularPairDesignMeasure θ k hk) η v x ^ 2 ∂μ) ≤
      lam * ∫ w, ‖v w‖ ^ 2 ∂regularPairDesignMeasure θ k hk

theorem PairPilotAssumptions.mono_lam {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {θ : RegressionParameter d} {k : ℕ} {hk : 0 < k} {μ : Measure Ω}
    {bar : Covariate d × Covariate d → PairVector}
    {η : Ω → Covariate d × Covariate d → PairVector} {Cp W lam lam' : ℝ}
    (hp : PairPilotAssumptions θ k hk μ bar η Cp W lam) (hl : lam ≤ lam') :
    PairPilotAssumptions θ k hk μ bar η Cp W lam' :=
  { hp with
    lamNonnegative := hp.lamNonnegative.trans hl
    linearTest := fun v hv => (hp.linearTest v hv).trans
      (mul_le_mul_of_nonneg_right hl (integral_nonneg fun w => sq_nonneg ‖v w‖)) }

def twoScalarPilotVector (a b : ℝ) : PairVector :=
  (a - b) • pairCoordinateVector 1 - a • pairCoordinateVector 2

theorem twoScalarPilotVector_coordinates (a b : ℝ) :
    twoScalarPilotVector a b = WithLp.toLp 2 ![0, a - b, -a] := by
  ext i; fin_cases i <;> simp [twoScalarPilotVector, pairCoordinateVector]

theorem pairPilotAssumptions_of_two_scalars
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] {d : ℕ}
    (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k)
    (bar : Covariate d × Covariate d → PairVector)
    (a b : Ω → Covariate d × Covariate d → ℝ)
    {Cp W point test Λ : ℝ} (hCp : 0 ≤ Cp) (hW : 0 ≤ W)
    (htest : 0 ≤ test) (hΛ : 0 < Λ) (hpoint : 5 * point ≤ Cp)
    (hmbar : Measurable bar)
    (hma : Measurable (fun z : Ω × (Covariate d × Covariate d) => a z.1 z.2))
    (hmb : Measurable (fun z : Ω × (Covariate d × Covariate d) => b z.1 z.2))
    (hbar : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 → ‖bar w‖ ≤ Cp)
    (hsections : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 →
        MemLp (fun x => a x w) 2 μ ∧ MemLp (fun x => b x w) 2 μ)
    (henergy : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 →
        (∫ x, a x w ^ 2 ∂μ) ≤ point * W ∧ (∫ x, b x w ^ 2 ∂μ) ≤ point * W)
    (hcenter : ∀ᵐ w ∂regularPairDesignMeasure θ k hk,
      (∫ x, a x w ∂μ) = 0 ∧ (∫ x, b x w ∂μ) = 0)
    (hinta : ∀ v : (Covariate d × Covariate d) → ℝ,
      MemLp v 2 (regularPairDesignMeasure θ k hk) → ∀ x,
        Integrable (fun w => v w * a x w) (regularPairDesignMeasure θ k hk))
    (hintb : ∀ v : (Covariate d × Covariate d) → ℝ,
      MemLp v 2 (regularPairDesignMeasure θ k hk) → ∀ x,
        Integrable (fun w => v w * b x w) (regularPairDesignMeasure θ k hk))
    (hLa : ∀ v : (Covariate d × Covariate d) → ℝ,
      MemLp v 2 (regularPairDesignMeasure θ k hk) →
        MemLp (fun x => ∫ w, v w * a x w ∂regularPairDesignMeasure θ k hk) 2 μ)
    (hLb : ∀ v : (Covariate d × Covariate d) → ℝ,
      MemLp v 2 (regularPairDesignMeasure θ k hk) →
        MemLp (fun x => ∫ w, v w * b x w ∂regularPairDesignMeasure θ k hk) 2 μ)
    (hEa : ∀ v : (Covariate d × Covariate d) → ℝ,
      MemLp v 2 (regularPairDesignMeasure θ k hk) →
        (∫ x, (∫ w, v w * a x w ∂regularPairDesignMeasure θ k hk) ^ 2 ∂μ) ≤
          (test * W / Λ) * ∫ w, v w ^ 2 ∂regularPairDesignMeasure θ k hk)
    (hEb : ∀ v : (Covariate d × Covariate d) → ℝ,
      MemLp v 2 (regularPairDesignMeasure θ k hk) →
        (∫ x, (∫ w, v w * b x w ∂regularPairDesignMeasure θ k hk) ^ 2 ∂μ) ≤
          (test * W / Λ) * ∫ w, v w ^ 2 ∂regularPairDesignMeasure θ k hk) :
    PairPilotAssumptions θ k hk μ bar (fun x w => twoScalarPilotVector (a x w) (b x w))
      Cp W (6 * (test * W / Λ)) := by
  have hnorm_le (x y : ℝ) : ‖twoScalarPilotVector x y‖ ^ 2 ≤ 3 * x ^ 2 + 2 * y ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, twoScalarPilotVector_coordinates]
    simp only [Fin.sum_univ_succ, Fin.isValue, WithLp.ofLp_toLp, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Finset.univ_eq_empty, Finset.sum_empty]
    nlinarith [sq_nonneg (x + y)]
  have hvec_L2 {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
      MemLp (fun x => twoScalarPilotVector (f x) (g x)) 2 μ := by
    have hs : AEStronglyMeasurable (fun x => twoScalarPilotVector (f x) (g x)) μ :=
      ((hf.aestronglyMeasurable.sub hg.aestronglyMeasurable).smul_const _).sub (hf.aestronglyMeasurable.smul_const _)
    refine (memLp_two_iff_integrable_sq_norm hs).mpr
      (((hf.integrable_sq.const_mul 3).add (hg.integrable_sq.const_mul 2)).mono' (hs.norm.pow 2) ?_)
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hnorm_le _ _
  refine ⟨hCp, hW, hmbar, ((hma.sub hmb).smul measurable_const).sub (hma.smul measurable_const), hbar,
    hsections.mono (fun _ hw hs => hvec_L2 (hw hs).1 (hw hs).2), ?_, ?_, by positivity, ?_⟩
  · filter_upwards [hsections, henergy] with w hw he hs
    obtain ⟨ha2, hb2⟩ := hw hs
    have h := integral_mono (hvec_L2 ha2 hb2).norm.integrable_sq
      ((ha2.integrable_sq.const_mul 3).add (hb2.integrable_sq.const_mul 2)) fun x => hnorm_le (a x w) (b x w)
    change (∫ x, ‖twoScalarPilotVector (a x w) (b x w)‖ ^ 2 ∂μ) ≤ ∫ x, 3 * a x w ^ 2 + 2 * b x w ^ 2 ∂μ at h
    rw [integral_add (f := fun x => 3 * a x w ^ 2) (g := fun x => 2 * b x w ^ 2)
      (ha2.integrable_sq.const_mul 3) (hb2.integrable_sq.const_mul 2), integral_const_mul, integral_const_mul] at h
    have hm := mul_le_mul_of_nonneg_right hpoint hW
    nlinarith [(he hs).1, (he hs).2, h, hm]
  · filter_upwards [regularPairDesignMeasure_ae_of_supported θ k hk hsections, hcenter] with w hw hc
    have hai := hw.1.integrable (by norm_num)
    have hbi := hw.2.integrable (by norm_num)
    unfold twoScalarPilotVector
    rw [integral_sub (f := fun x => (a x w - b x w) • pairCoordinateVector 1)
      (g := fun x => a x w • pairCoordinateVector 2) ((hai.sub hbi).smul_const _) (hai.smul_const _),
      integral_smul_const, integral_smul_const, integral_sub hai hbi, hc.1, hc.2]; simp
  · intro v hv
    let M := regularPairDesignMeasure θ k hk
    have hcoord (i : Fin 3) : MemLp (fun w => v w i) 2 M :=
      hv.mono ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp_aestronglyMeasurable hv.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun w => PiLp.norm_apply_le (v w) i)
    let vA (w : Covariate d × Covariate d) := v w 1 - v w 2
    let vB (w : Covariate d × Covariate d) := v w 1
    have hvA : MemLp vA 2 M := (hcoord 1).sub (hcoord 2)
    have hvB : MemLp vB 2 M := hcoord 1
    let A (x : Ω) := ∫ w, vA w * a x w ∂M
    let B (x : Ω) := ∫ w, vB w * b x w ∂M
    have hA : MemLp A 2 μ := hLa vA hvA
    have hB : MemLp B 2 μ := hLb vB hvB
    have heq (x : Ω) : PilotFields.test (M := M) (fun x w => twoScalarPilotVector (a x w) (b x w)) v x = A x - B x := by
      unfold PilotFields.test
      have h_in (w) : ⟪twoScalarPilotVector (a x w) (b x w), v w⟫ = vA w * a x w - vB w * b x w := by
        rw [twoScalarPilotVector_coordinates]; simp [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_succ, vA, vB]; ring
      simp_rw [h_in]
      exact integral_sub (hinta vA hvA x) (hintb vB hvB x)
    simp_rw [heq]
    have hsq := integral_mono (hA.sub hB).integrable_sq
      ((hA.integrable_sq.const_mul 2).add (hB.integrable_sq.const_mul 2))
      fun x => show (A x - B x) ^ 2 ≤ 2 * A x ^ 2 + 2 * B x ^ 2 by nlinarith [sq_nonneg (A x + B x)]
    change (∫ x, (A x - B x) ^ 2 ∂μ) ≤ ∫ x, 2 * A x ^ 2 + 2 * B x ^ 2 ∂μ at hsq
    rw [integral_add (f := fun x => 2 * A x ^ 2) (g := fun x => 2 * B x ^ 2)
      (hA.integrable_sq.const_mul 2) (hB.integrable_sq.const_mul 2), integral_const_mul, integral_const_mul] at hsq
    have hwt : (∫ w, vA w ^ 2 ∂M) + (∫ w, vB w ^ 2 ∂M) ≤ 3 * ∫ w, ‖v w‖ ^ 2 ∂M := by
      rw [← integral_add hvA.integrable_sq hvB.integrable_sq, ← integral_const_mul]
      refine integral_mono (hvA.integrable_sq.add hvB.integrable_sq) (hv.norm.integrable_sq.const_mul 3) fun w => ?_
      rw [EuclideanSpace.real_norm_sq_eq]; simp only [Fin.sum_univ_succ, Fin.isValue, Fin.succ_zero_eq_one,
        Fin.succ_one_eq_two, Finset.univ_eq_empty, Finset.sum_empty, Real.norm_eq_abs, sq_abs]
      dsimp [vA, vB]; nlinarith [sq_nonneg (v w 1 + v w 2), sq_nonneg (v w 0), sq_nonneg (v w 2)]
    have hc0 : 0 ≤ test * W / Λ := div_nonneg (mul_nonneg htest hW) hΛ.le
    dsimp only [A, B] at hsq
    nlinarith [hsq, hEa vA hvA, hEb vB hvB, mul_le_mul_of_nonneg_left hwt hc0]

theorem scalarPilot_covariance_sample_budget {Cp W test Λ n : ℝ}
    (hn : 0 < n) (hW : 0 ≤ W) (_htest : 0 ≤ test) (hΛ : n / 12 ≤ Λ)
    (hCp : 72 * test ≤ Cp ^ 2) :
    6 * (test * W / Λ) ≤ Cp ^ 2 * W / n := by
  have hΛ0 : 0 < Λ := (div_pos hn (by norm_num)).trans_le hΛ
  rw [← mul_div_assoc, div_le_div_iff₀ hΛ0 hn]
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCp hW) hn.le
  have hden := mul_le_mul_of_nonneg_left hΛ (mul_nonneg (sq_nonneg Cp) hW)
  nlinarith

-- 6. Rate algebra & `coefficientPairEstimator_rms_bound`

def pairFluctuationScale {d : ℕ} (n k : ℕ) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹ + Real.sqrt ((k : ℝ) ^ d) / (n : ℝ)

theorem pairFluctuationScale_nonneg {d : ℕ} (n k : ℕ) :
    0 ≤ pairFluctuationScale (d := d) n k := by unfold pairFluctuationScale; positivity

def pairRateSquaredConstant {d : ℕ} (C : ModelConstants d) (Cp c a : ℝ) : ℝ :=
  (2 / a ^ 2) *
    ((4 * responseOperatorEnergyBound C * C.densityUpper + 8 * C.varianceUpper ^ 2 * C.densityUpper) *
      (4 * (C.densityUpper / c + 1 / c ^ 2) * (1 + Cp) ^ 4) +
    (3 * (2 * C.holderBound ^ 2 + 1) ^ 2 + 6 * C.varianceUpper ^ 2) *
      (2 * C.densityUpper * (1 + Cp) ^ 4) + C.densityUpper ^ 2 / 2)

theorem pairRateSquaredConstant_pos {d : ℕ} (C : ModelConstants d)
    {Cp c a : ℝ} (hCp : 0 ≤ Cp) (hc : 0 < c) (ha : 0 < a) :
    0 < pairRateSquaredConstant C Cp c a := by
  have : 0 < C.densityUpper := by linarith [C.one_lt_densityUpper]
  have := responseOperatorEnergyBound_pos C
  unfold pairRateSquaredConstant; positivity

private theorem pairRiskBudget_rate_le {d n m k : ℕ} (C : ModelConstants d)
    (hn : 0 < n) (hm : 2 ≤ m) (hk : 0 < k) (hsize : (1 / 4 : ℝ) * n ≤ m)
    {Cp W B_var b : ℝ} (hCp : 0 ≤ Cp) (hW : 0 ≤ W) (hB : 0 ≤ B_var)
    (hB_le : B_var ≤ C.densityUpper * (2 * Cp ^ 2 + Cp * W))
    {I_S I_D : ℝ}
    (hstep1 : I_S + C.varianceUpper ^ 2 * I_D ≤
      (4 * responseOperatorEnergyBound C * C.densityUpper + 8 * C.varianceUpper ^ 2 * C.densityUpper) *
        ((C.densityUpper / (m : ℝ) + (k : ℝ) ^ d / (2 * (m : ℝ) * (m - 1 : ℕ))) * (2 * Cp ^ 2 + 2 * Cp * W) ^ 2) +
      (3 * (2 * C.holderBound ^ 2 + 1) ^ 2 + 6 * C.varianceUpper ^ 2) * ((Cp ^ 2 * W / (n : ℝ)) * B_var) +
      (C.densityUpper ^ 2 / 2) * b ^ 4) :
    (2 / (1 / 4 : ℝ) ^ 2) * (I_S + C.varianceUpper ^ 2 * I_D) ≤
      pairRateSquaredConstant C Cp (1 / 4) (1 / 4) *
        (b ^ 2 + pairFluctuationScale (d := d) n k * (1 + W)) ^ 2 := by
  let P := 1 + Cp
  let t := pairFluctuationScale (d := d) n k
  let R := t * (1 + W)
  let E_c := C.densityUpper / (1 / 4 : ℝ) + 1 / (1 / 4 : ℝ) ^ 2
  let c_eval := C.densityUpper / (m : ℝ) + (k : ℝ) ^ d / (2 * (m : ℝ) * (m - 1 : ℕ))
  let L_coef := 2 * Cp ^ 2 + 2 * Cp * W
  let lam := Cp ^ 2 * W / (n : ℝ)
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hkp : 0 < (k : ℝ) ^ d := pow_pos (by exact_mod_cast hk) d
  have hpplus : 0 ≤ C.densityUpper := by linarith [C.one_lt_densityUpper]
  have ht_nn : 0 ≤ t := pairFluctuationScale_nonneg n k
  have hR_nn : 0 ≤ R := mul_nonneg ht_nn (by linarith)
  have hL_coef : 0 ≤ L_coef := by dsimp [L_coef]; positivity
  have ht_sq_lo : 1 / (n : ℝ) + (k : ℝ) ^ d / (n : ℝ) ^ 2 ≤ t ^ 2 := by
    have ha : ((Real.sqrt (n : ℝ))⁻¹) ^ 2 = 1 / (n : ℝ) := by rw [inv_pow, Real.sq_sqrt hn0.le, one_div]
    have hb : (Real.sqrt ((k : ℝ) ^ d) / (n : ℝ)) ^ 2 = (k : ℝ) ^ d / (n : ℝ) ^ 2 := by rw [div_pow, Real.sq_sqrt hkp.le]
    have hab : 0 ≤ (Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt ((k : ℝ) ^ d) / (n : ℝ)) := by positivity
    dsimp [t, pairFluctuationScale]; nlinarith
  have hc_eval_le : c_eval ≤ E_c * t ^ 2 := by
    have hm1 : (m : ℝ) ≤ 2 * ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (show m ≤ 2 * (m - 1) by omega)
    have hmsq : ((1 / 4 : ℝ) * n) ^ 2 ≤ (m : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hsize 2
    have hden : (1 / 4 : ℝ) ^ 2 * (n : ℝ) ^ 2 ≤ 2 * (m : ℝ) * (m - 1 : ℕ) := by
      have := mul_le_mul_of_nonneg_left hm1 hm0.le; nlinarith
    have h1 : C.densityUpper / (m : ℝ) ≤ (C.densityUpper / (1 / 4 : ℝ)) * (1 / (n : ℝ)) :=
      (div_le_div_of_nonneg_left hpplus (by positivity) hsize).trans_eq (by ring)
    have h2 : (k : ℝ) ^ d / (2 * (m : ℝ) * (m - 1 : ℕ)) ≤ (1 / (1 / 4 : ℝ) ^ 2) * ((k : ℝ) ^ d / (n : ℝ) ^ 2) :=
      (div_le_div_of_nonneg_left hkp.le (by positivity) hden).trans_eq (by ring)
    have h3 : (C.densityUpper / (1 / 4 : ℝ)) * (1 / (n : ℝ)) + (1 / (1 / 4 : ℝ) ^ 2) * ((k : ℝ) ^ d / (n : ℝ) ^ 2) ≤
        E_c * (1 / (n : ℝ) + (k : ℝ) ^ d / (n : ℝ) ^ 2) := by
      have h_a : 0 ≤ (1 / (1 / 4 : ℝ) ^ 2) * (1 / (n : ℝ)) := by positivity
      have h_b : 0 ≤ (C.densityUpper / (1 / 4 : ℝ)) * ((k : ℝ) ^ d / (n : ℝ) ^ 2) := by positivity
      dsimp [E_c]; linarith
    exact ((add_le_add h1 h2).trans h3).trans (mul_le_mul_of_nonneg_left ht_sq_lo (by dsimp [E_c]; positivity))
  have hCP : Cp ≤ P ^ 2 := by dsimp [P]; nlinarith [hCp, sq_nonneg Cp]
  have hC2P : Cp ^ 2 ≤ P ^ 2 := by dsimp [P]; nlinarith [hCp]
  have hCW := mul_le_mul_of_nonneg_right hCP hW
  have hL_coef_sq : L_coef ^ 2 ≤ 4 * P ^ 4 * (1 + W) ^ 2 := by
    have hFb : L_coef ≤ 2 * P ^ 2 * (1 + W) := by dsimp [L_coef]; nlinarith [hC2P, hCW]
    exact (pow_le_pow_left₀ hL_coef hFb 2).trans_eq (by ring)
  have hEF : c_eval * L_coef ^ 2 ≤ 4 * E_c * P ^ 4 * R ^ 2 :=
    (mul_le_mul hc_eval_le hL_coef_sq (sq_nonneg _) (by dsimp [E_c]; positivity)).trans_eq (by dsimp [R]; ring)
  have hBb : B_var ≤ 2 * C.densityUpper * P ^ 2 * (1 + W) := by
    refine hB_le.trans ?_
    have h1 : 2 * Cp ^ 2 + Cp * W ≤ 2 * P ^ 2 * (1 + W) := by nlinarith [hC2P, hCW, mul_nonneg (sq_nonneg P) hW]
    exact (mul_le_mul_of_nonneg_left h1 hpplus).trans_eq (by ring)
  have hLamB : lam * B_var ≤ 2 * C.densityUpper * P ^ 4 * R ^ 2 := by
    have hLamSmall : lam ≤ P ^ 2 * W / (n : ℝ) := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC2P hW) hn0.le
    have hmB := mul_le_mul hLamSmall hBb hB (div_nonneg (mul_nonneg (sq_nonneg P) hW) hn0.le)
    have hW2 : W * (1 + W) ≤ (1 + W) ^ 2 := by nlinarith [hW]
    have ht1 : 1 / (n : ℝ) ≤ t ^ 2 := by linarith [ht_sq_lo, show (0 : ℝ) ≤ (k : ℝ) ^ d / (n : ℝ) ^ 2 by positivity]
    calc lam * B_var
      _ ≤ (P ^ 2 * W / (n : ℝ)) * (2 * C.densityUpper * P ^ 2 * (1 + W)) := hmB
      _ = (2 * C.densityUpper * P ^ 4) * (W * (1 + W)) * (1 / (n : ℝ)) := by ring
      _ ≤ (2 * C.densityUpper * P ^ 4) * (1 + W) ^ 2 * t ^ 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hW2 (by positivity)) ht1 (by positivity) (by positivity)
      _ = 2 * C.densityUpper * P ^ 4 * R ^ 2 := by dsimp [R]; ring
  have hA0 : 0 ≤ 4 * responseOperatorEnergyBound C * C.densityUpper + 8 * C.varianceUpper ^ 2 * C.densityUpper := by
    have := responseOperatorEnergyBound_pos C; positivity
  have hL0 : 0 ≤ 3 * (2 * C.holderBound ^ 2 + 1) ^ 2 + 6 * C.varianceUpper ^ 2 := by positivity
  have hsR : R ^ 2 ≤ (b ^ 2 + R) ^ 2 := pow_le_pow_left₀ hR_nn (le_add_of_nonneg_left (sq_nonneg b)) 2
  have hsb : b ^ 4 ≤ (b ^ 2 + R) ^ 2 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg b) (le_add_of_nonneg_right hR_nn) 2
  have hCR : 0 ≤ (4 * responseOperatorEnergyBound C * C.densityUpper + 8 * C.varianceUpper ^ 2 * C.densityUpper) *
      (4 * E_c * P ^ 4) + (3 * (2 * C.holderBound ^ 2 + 1) ^ 2 + 6 * C.varianceUpper ^ 2) *
        (2 * C.densityUpper * P ^ 4) := by dsimp [E_c, P]; positivity
  unfold pairRateSquaredConstant
  rw [mul_assoc (2 / (1 / 4 : ℝ) ^ 2)]
  refine mul_le_mul_of_nonneg_left (hstep1.trans ?_) (by norm_num)
  have hER := mul_le_mul_of_nonneg_left hEF hA0
  have hLR := mul_le_mul_of_nonneg_left hLamB hL0
  have hCsR := mul_le_mul_of_nonneg_left hsR hCR
  have hCsb := mul_le_mul_of_nonneg_left hsb (by positivity : 0 ≤ C.densityUpper ^ 2 / 2)
  dsimp only [E_c, P, R, t] at hER hLR hCsR hCsb ⊢
  linarith only [hER, hLR, hCsR, hCsb]

def rawModelPairNoise {Ω : Type*} {d : ℕ} (k : ℕ) (hk : 0 < k)
    (c : Ω → Covariate d × Covariate d → PairVector) (p : Ω × Ω) (z : Observation d × Observation d) : ℝ :=
  sameLabelKernel (regularObservationLabel k hk) z *
    ⟪c p.1 (pairCovariates z), pairNoiseOperator (c p.2 (pairCovariates z))⟫

def coefficientPairNumeratorKernel {Ω : Type*} {d : ℕ} (k : ℕ) (hk : 0 < k)
    (c : Ω → Covariate d × Covariate d → PairVector) (p : Ω × Ω) (z : Observation d × Observation d) : ℝ :=
  sameLabelKernel (regularObservationLabel k hk) z *
    ⟪c p.1 (pairCovariates z), InnerProductSpace.rankOne ℝ
      (pairResponseVector z.1.2 z.2.2) (pairResponseVector z.1.2 z.2.2) (c p.2 (pairCovariates z))⟫

def coefficientPairStatistic {d : ℕ} (C : ModelConstants d) (m k : ℕ) (hk : 0 < k)
    (c : (Fin m → Observation d) → Covariate d × Covariate d → PairVector)
    (z : (((Fin m → Observation d) × (Fin m → Observation d)) × (Fin m → Observation d))) : ℝ :=
  stabilizedRatio C.varianceLower C.varianceUpper (1 / 4)
    (PairUStatistic.fieldPairAverage m ((k : ℝ) ^ d) (coefficientPairNumeratorKernel k hk c) (fun i x => x i))
    (PairUStatistic.fieldPairAverage m ((k : ℝ) ^ d) (rawModelPairNoise k hk c) (fun i x => x i)) z

theorem coefficientPairStatistic_measurable {d : ℕ} (C : ModelConstants d) (m k : ℕ)
    (hk : 0 < k) {c : (Fin m → Observation d) → Covariate d × Covariate d → PairVector}
    (hmc : Measurable (fun z : (Fin m → Observation d) × (Covariate d × Covariate d) => c z.1 z.2)) :
    Measurable (coefficientPairStatistic C m k hk c) := by
  have hcov : Measurable (pairCovariates (d := d)) := measurable_fst.fst.prodMk measurable_snd.fst
  have hc_obs : Measurable (fun z : (Fin m → Observation d) × (Observation d × Observation d) =>
      c z.1 (pairCovariates z.2)) := hmc.comp (measurable_fst.prodMk (hcov.comp measurable_snd))
  have hq := sameLabelKernel_measurable (regularObservationLabel (d := d) k hk)
    (regularObservationLabel_measurable (d := d) k hk)
  have hmN0 := PilotFields.maskedPilotKernel_measurable (c := fun x z => c x (pairCovariates z))
    (A := fun z : Observation d × Observation d => pairScoreOperator 0 z.1.2 z.2.2)
    (q := sameLabelKernel (regularObservationLabel (d := d) k hk))
    hc_obs (observationPairScoreOperator_measurable_apply (d := d) 0) hq
  change Measurable (fun z : ((Fin m → Observation d) × (Fin m → Observation d)) × (Observation d × Observation d) =>
    sameLabelKernel (regularObservationLabel k hk) z.2 *
      ⟪c z.1.1 (pairCovariates z.2), pairScoreOperator 0 z.2.1.2 z.2.2.2 (c z.1.2 (pairCovariates z.2))⟫) at hmN0
  have hmN : Measurable (fun z : ((Fin m → Observation d) × (Fin m → Observation d)) × (Observation d × Observation d) =>
      coefficientPairNumeratorKernel k hk c z.1 z.2) := by
    simpa only [coefficientPairNumeratorKernel, pairScoreOperator,
      _root_.sub_apply, _root_.smul_apply, zero_smul, sub_zero] using hmN0
  have hmD : Measurable (fun z : ((Fin m → Observation d) × (Fin m → Observation d)) × (Observation d × Observation d) =>
      rawModelPairNoise k hk c z.1 z.2) :=
    PilotFields.maskedPilotKernel_measurable (c := fun x z => c x (pairCovariates z))
      (A := fun _ : Observation d × Observation d => pairNoiseOperator)
      (q := sameLabelKernel (regularObservationLabel (d := d) k hk))
      hc_obs (pairNoiseOperator.continuous.measurable.comp measurable_snd) hq
  exact stabilizedRatio_measurable C.varianceLower C.varianceUpper (1 / 4)
    (PairUStatistic.fieldPairAverage_measurable m ((k : ℝ) ^ d) hmN _ fun i => measurable_pi_apply i)
    (PairUStatistic.fieldPairAverage_measurable m ((k : ℝ) ^ d) hmD _ fun i => measurable_pi_apply i)

def coefficientPairEstimator {d n : ℕ} (C : ModelConstants d) (k : ℕ) (hk : 0 < k)
    (c : (Fin (threeBlockSize n) → Observation d) → Covariate d × Covariate d → PairVector)
    (hmc : Measurable (fun z : (Fin (threeBlockSize n) → Observation d) ×
      (Covariate d × Covariate d) => c z.1 z.2)) : Estimator d n :=
  ⟨fun z => coefficientPairStatistic C (threeBlockSize n) k hk c (threeBlockSplit d n z),
    (coefficientPairStatistic_measurable C _ k hk hmc).comp (threeBlockSplit_measurable d n)⟩

theorem coefficientPairEstimator_rms_bound {d n : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (hn : 6 ≤ n)
    (k : ℕ) (hk : 0 < k)
    (c : (Fin (threeBlockSize n) → Observation d) → Covariate d × Covariate d → PairVector)
    (hmc : Measurable (fun z : (Fin (threeBlockSize n) → Observation d) ×
      (Covariate d × Covariate d) => c z.1 z.2))
    (bar : Covariate d × Covariate d → PairVector)
    (η : (Fin (threeBlockSize n) → Observation d) → Covariate d × Covariate d → PairVector)
    (Cp W b : ℝ) (heq : c = pairPilotCoefficient bar η)
    (hp : PairPilotAssumptions θ k hk (sampleLaw θ (threeBlockSize n)) bar η
      Cp W (Cp ^ 2 * W / (n : ℝ)))
    (hfirst : ∀ᵐ w ∂regularPairDesignMeasure θ k hk, bar w 0 = 1)
    (hresidual : ∀ᵐ w ∂regularPairDesignMeasure θ k hk,
      |⟪bar w, pairResponseVector (θ.regression w.1) (θ.regression w.2)⟫| ≤ b) :
    meanSquaredRisk (coefficientPairEstimator C k hk c hmc) θ ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (pairRateSquaredConstant C Cp (1 / 4) (1 / 4)) *
        (b ^ 2 + pairFluctuationScale (d := d) n k * (1 + W))) := by
  let m := threeBlockSize n
  let μ := sampleLaw θ m
  let obs := observationLaw θ
  let M_des := regularPairDesignMeasure θ k hk
  let _ := observationLaw_isProbability C θ hθ
  let _ := sampleLaw_isProbability C θ hθ m
  let _ := regularPairDesignMeasure_isFinite C θ hθ k hk
  let _ := designLaw_isProbability C θ hθ
  let lam := Cp ^ 2 * W / (n : ℝ)
  let L_coef := 2 * Cp ^ 2 + 2 * Cp * W
  have hL_coef : 0 ≤ L_coef := by
    dsimp [L_coef]
    nlinarith [hp.constantNonnegative, hp.budgetNonnegative, mul_nonneg hp.constantNonnegative hp.budgetNonnegative]
  let c_pil := pairPilotCoefficient bar η
  have hmc_pil : Measurable (fun z : (Fin m → Observation d) × (Covariate d × Covariate d) => c_pil z.1 z.2) :=
    (hp.barMeasurable.comp measurable_snd).add hp.noiseMeasurable
  have hcov_meas : Measurable (pairCovariates (d := d)) := measurable_fst.fst.prodMk measurable_snd.fst
  have hc_obs : Measurable (fun z : (Fin m → Observation d) × (Observation d × Observation d) =>
      c_pil z.1 (pairCovariates z.2)) := hmc_pil.comp (measurable_fst.prodMk (hcov_meas.comp measurable_snd))
  have hmp_cov : MeasurePreserving pairCovariates (obs.prod obs) ((designLaw θ).prod (designLaw θ)) :=
    (observationLaw_fst_measurePreserving C θ hθ).prod (observationLaw_fst_measurePreserving C θ hθ)
  -- Section L2 and energy bounds for `c_pil = bar + η`
  have hc_sec : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 → MemLp (fun x => c_pil x w) 2 μ :=
    hp.noiseSection.mono fun w hw hs => (memLp_const (bar w)).add (hw hs)
  have hc_en : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 → (∫ x, ‖c_pil x w‖ ^ 2 ∂μ) ≤ L_coef := by
    filter_upwards [hp.noiseSection, hp.barBound, hp.noiseEnergy] with w hs hb he hq
    have hηw := hs hq
    have hT := ((memLp_const (bar w)).add hηw).norm.integrable_sq
    have hmono := integral_mono (g := fun x => 2 * ‖bar w‖ ^ 2 + 2 * ‖η x w‖ ^ 2) hT
      ((integrable_const (2 * ‖bar w‖ ^ 2)).add (hηw.norm.integrable_sq.const_mul 2))
      fun x => by
        have h1 := pow_le_pow_left₀ (norm_nonneg (bar w + η x w)) (norm_add_le (bar w) (η x w)) 2
        change ‖bar w + η x w‖ ^ 2 ≤ 2 * ‖bar w‖ ^ 2 + 2 * ‖η x w‖ ^ 2
        nlinarith [sq_nonneg (‖bar w‖ - ‖η x w‖)]
    rw [integral_add (f := fun _ => 2 * ‖bar w‖ ^ 2) (g := fun x => 2 * ‖η x w‖ ^ 2)
      (integrable_const _) (hηw.norm.integrable_sq.const_mul 2),
      integral_const, integral_const_mul] at hmono
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hmono
    have hbsq := pow_le_pow_left₀ (norm_nonneg _) (hb hq) 2
    dsimp [c_pil, pairPilotCoefficient, L_coef] at hmono ⊢; linarith [hmono, he hq, hbsq]
  -- Score & noise kernels
  let K_score (p : (Fin m → Observation d) × (Fin m → Observation d)) (z : Observation d × Observation d) : ℝ :=
    sameLabelKernel (regularObservationLabel k hk) z *
      ⟪c_pil p.1 (pairCovariates z), pairScoreOperator θ.variance z.1.2 z.2.2 (c_pil p.2 (pairCovariates z))⟫
  let K_noise := rawModelPairNoise k hk c_pil
  have hq_meas := sameLabelKernel_measurable (regularObservationLabel (d := d) k hk)
    (regularObservationLabel_measurable (d := d) k hk)
  have hq_idem (z : Observation d × Observation d) :
      sameLabelKernel (regularObservationLabel k hk) z ^ 2 = sameLabelKernel (regularObservationLabel k hk) z := by
    unfold sameLabelKernel; split_ifs <;> norm_num
  -- Masked kernel L2 & energy facts for K_score and K_noise
  obtain ⟨hresp_int, hresp_le⟩ := regular_response_operator_energy C θ hθ k hk
  obtain ⟨hK_score_L2, hK_score_en0⟩ := PilotFields.maskedPilotKernel_facts
    (μ := μ) (ν := obs.prod obs) hc_obs (observationPairScoreOperator_measurable_apply (d := d) θ.variance)
    hq_meas hq_idem hresp_int (hmp_cov.quasiMeasurePreserving.ae hc_sec) hL_coef
    (hmp_cov.quasiMeasurePreserving.ae hc_en)
  have hK_score_en : (∫ z, K_score z.1 z.2 ^ 2 ∂(μ.prod μ).prod (obs.prod obs)) ≤
      L_coef ^ 2 * (responseOperatorEnergyBound C * (C.densityUpper / (k : ℝ) ^ d)) :=
    hK_score_en0.trans (mul_le_mul_of_nonneg_left hresp_le (sq_nonneg _))
  have hnoise_op_int : Integrable (fun z : Observation d × Observation d =>
      sameLabelKernel (regularObservationLabel k hk) z * ‖pairNoiseOperator‖ ^ 2) (obs.prod obs) :=
    ((sameLabelKernel_memLp obs _ (regularObservationLabel_measurable k hk)).integrable (by norm_num)).mul_const _
  have hnoise_op_le : (∫ z : Observation d × Observation d,
      sameLabelKernel (regularObservationLabel k hk) z * ‖pairNoiseOperator‖ ^ 2 ∂obs.prod obs) ≤
      4 * (C.densityUpper / (k : ℝ) ^ d) := by
    dsimp only [obs]
    rw [integral_mul_const, sameLabelKernel_integral (observationLaw θ) _ (regularObservationLabel_measurable k hk)]
    simp_rw [regularObservationLabel_mass C θ hθ k hk]
    change regularGridCollisionMass θ k hk * ‖pairNoiseOperator‖ ^ 2 ≤ _
    have hq_nn : 0 ≤ regularGridCollisionMass θ k hk := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hN : ‖pairNoiseOperator‖ ^ 2 ≤ 4 := by
      have h := pow_le_pow_left₀ (norm_nonneg _) pairNoiseOperator_norm_le 2; norm_num at h; exact h
    exact (mul_le_mul_of_nonneg_left hN hq_nn).trans (by linarith [regularGridCollisionMass_upper C θ hθ k hk])
  obtain ⟨hK_noise_L2, hK_noise_en0⟩ := PilotFields.maskedPilotKernel_facts
    (μ := μ) (ν := obs.prod obs) hc_obs (pairNoiseOperator.continuous.measurable.comp measurable_snd)
    hq_meas hq_idem hnoise_op_int (hmp_cov.quasiMeasurePreserving.ae hc_sec) hL_coef
    (hmp_cov.quasiMeasurePreserving.ae hc_en)
  have hK_noise_en : (∫ z, K_noise z.1 z.2 ^ 2 ∂(μ.prod μ).prod (obs.prod obs)) ≤
      L_coef ^ 2 * (4 * (C.densityUpper / (k : ℝ) ^ d)) :=
    hK_noise_en0.trans (mul_le_mul_of_nonneg_left hnoise_op_le (sq_nonneg _))
  -- Pilot mean analysis via `PilotFields.half_pilotMean_facts`
  have hbar_M : ∀ᵐ w ∂M_des, ‖bar w‖ ≤ Cp := regularPairDesignMeasure_ae_of_supported θ k hk hp.barBound
  have hbar_L2 : MemLp bar 2 M_des := MemLp.of_bound hp.barMeasurable.aestronglyMeasurable Cp hbar_M
  have hη_sec_M := regularPairDesignMeasure_ae_of_supported θ k hk hp.noiseSection
  have hη_en_M := regularPairDesignMeasure_ae_of_supported θ k hk hp.noiseEnergy
  have hη_L2 : MemLp (fun z : (Fin m → Observation d) × (Covariate d × Covariate d) => η z.1 z.2) 2 (μ.prod M_des) :=
    PilotFields.memLp_joint_of_uniform_section_energy hp.noiseMeasurable hη_sec_M
      (mul_nonneg hp.constantNonnegative hp.budgetNonnegative) hη_en_M
  let B_var : ℝ := 2 * (∫ w, ‖bar w‖ ^ 2 ∂M_des) + ∫ z, ‖η z.1 z.2‖ ^ 2 ∂μ.prod M_des
  have hB_var_nn : 0 ≤ B_var := by dsimp [B_var]; positivity
  have hB_var_le : B_var ≤ C.densityUpper * (2 * Cp ^ 2 + Cp * W) := by
    have hbarE : (∫ w, ‖bar w‖ ^ 2 ∂M_des) ≤ Cp ^ 2 * M_des.real univ := by
      simpa only [integral_const, smul_eq_mul, mul_comm] using
        integral_mono_ae hbar_L2.norm.integrable_sq (integrable_const (Cp ^ 2))
          (hbar_M.mono fun _ hw => pow_le_pow_left₀ (norm_nonneg _) hw 2)
    have hnoiseE := PilotFields.joint_energy_le_of_uniform_sections hp.noiseMeasurable hη_sec_M
      (mul_nonneg hp.constantNonnegative hp.budgetNonnegative) hη_en_M
    have hmass := (regularPairDesignMeasure_mass_bounds C θ hθ k hk).2
    dsimp [B_var]
    nlinarith [mul_le_mul_of_nonneg_left hmass (sq_nonneg Cp),
      mul_le_mul_of_nonneg_left hmass (mul_nonneg hp.constantNonnegative hp.budgetNonnegative)]
  -- Conditional means `M_score` and `M_noise`
  let M_score := PairUStatistic.fieldPairMean (μ := obs) ((k : ℝ) ^ d) K_score
  let M_noise := PairUStatistic.fieldPairMean (μ := obs) ((k : ℝ) ^ d) K_noise
  have hM_score_ae : M_score =ᵐ[μ.prod μ] fun p => (1 / 2) *
      PilotFields.pilotMean (M := M_des) bar η (boundedPairRegressionOperator C θ) p := by
    filter_upwards [(hK_score_L2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).prod_right_ae] with p hp_int
    change Integrable (K_score p) ((observationLaw θ).prod (observationLaw θ)) at hp_int
    dsimp only [M_score, PairUStatistic.fieldPairMean, obs]
    rw [observationPair_integral_conditioning C θ hθ _ hp_int]
    have hcond_eq : (∫ w : Covariate d × Covariate d,
        (∫ u : ℝ × ℝ, K_score p ((w.1, θ.regression w.1 + u.1), (w.2, θ.regression w.2 + u.2))
          ∂(θ.errors w.1).prod (θ.errors w.2)) ∂(designLaw θ).prod (designLaw θ)) =
        ∫ w : Covariate d × Covariate d, sameLabelKernel (regularGridCell k hk) w *
          ⟪c_pil p.1 w, InnerProductSpace.rankOne ℝ (pairResponseVector (θ.regression w.1) (θ.regression w.2))
            (pairResponseVector (θ.regression w.1) (θ.regression w.2)) (c_pil p.2 w)⟫
          ∂(designLaw θ).prod (designLaw θ) := by
      refine integral_congr_ae ?_
      filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := designLaw θ) (ν := designLaw θ)).ae hθ.2.2.2.2.2.2.2,
        (Measure.quasiMeasurePreserving_snd (μ := designLaw θ) (ν := designLaw θ)).ae hθ.2.2.2.2.2.2.2] with w hw1 hw2
      have hμ1 : MemLp (fun u : ℝ => u) 2 (θ.errors w.1) := (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr hw1.2.1
      have hμ2 : MemLp (fun u : ℝ => u) 2 (θ.errors w.2) := (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr hw2.2.1
      change (∫ u : ℝ × ℝ, sameLabelKernel (regularGridCell k hk) w *
        ⟪c_pil p.1 w, pairScoreOperator θ.variance (θ.regression w.1 + u.1) (θ.regression w.2 + u.2) (c_pil p.2 w)⟫
        ∂(θ.errors w.1).prod (θ.errors w.2)) = _
      rw [integral_const_mul, conditional_pairScoreOperator_integral (θ.errors w.1) (θ.errors w.2)
        hμ1 hμ2 hw1.2.2.2.1 hw2.2.2.2.1 hw1.2.2.2.2.1 hw2.2.2.2.2.1]
    rw [hcond_eq]
    have hM := regularPairDesignMeasure_integral C θ hθ k hk fun w =>
      ⟪c_pil p.1 w, InnerProductSpace.rankOne ℝ (pairResponseVector (θ.regression w.1) (θ.regression w.2))
        (pairResponseVector (θ.regression w.1) (θ.regression w.2)) (c_pil p.2 w)⟫
    rw [smul_eq_mul] at hM
    calc ((k : ℝ) ^ d / 2) * ∫ w, sameLabelKernel (regularGridCell k hk) w * _ ∂(designLaw θ).prod (designLaw θ)
      _ = (1 / 2) * ((k : ℝ) ^ d * ∫ w, sameLabelKernel (regularGridCell k hk) w * _ ∂(designLaw θ).prod (designLaw θ)) := by ring
      _ = (1 / 2) * ∫ w, _ ∂M_des := by rw [hM]; rfl
      _ = _ := by
          congr 1; refine integral_congr_ae ?_
          filter_upwards [boundedPairRegressionOperator_eq_ae C θ hθ k hk] with w hw
          simp only [PilotFields.pilotMean, c_pil, pairPilotCoefficient, hw]
  have hM_noise_ae : M_noise =ᵐ[μ.prod μ] fun p => (1 / 2) *
      PilotFields.pilotMean (M := M_des) bar η (fun _ => pairNoiseOperator) p := by
    filter_upwards [(hK_noise_L2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).prod_right_ae] with p hp_int
    change Integrable (K_noise p) ((observationLaw θ).prod (observationLaw θ)) at hp_int
    dsimp only [M_noise, PairUStatistic.fieldPairMean, obs]
    rw [observationPair_integral_conditioning C θ hθ _ hp_int]
    have hcond_eq : (∫ w : Covariate d × Covariate d,
        (∫ u : ℝ × ℝ, K_noise p ((w.1, θ.regression w.1 + u.1), (w.2, θ.regression w.2 + u.2))
          ∂(θ.errors w.1).prod (θ.errors w.2)) ∂(designLaw θ).prod (designLaw θ)) =
        ∫ w : Covariate d × Covariate d, sameLabelKernel (regularGridCell k hk) w *
          ⟪c_pil p.1 w, pairNoiseOperator (c_pil p.2 w)⟫ ∂(designLaw θ).prod (designLaw θ) :=
      integral_congr_ae (Filter.Eventually.of_forall fun w => by
        change (∫ _u : ℝ × ℝ, sameLabelKernel (regularGridCell k hk) w *
          ⟪c_pil p.1 w, pairNoiseOperator (c_pil p.2 w)⟫ ∂(θ.errors w.1).prod (θ.errors w.2)) = _
        simp)
    rw [hcond_eq]
    have hM := regularPairDesignMeasure_integral C θ hθ k hk fun w => ⟪c_pil p.1 w, pairNoiseOperator (c_pil p.2 w)⟫
    simp only [smul_eq_mul, c_pil, pairPilotCoefficient] at hM
    simp only [PilotFields.pilotMean, c_pil, pairPilotCoefficient, M_des]
    rw [hM]; ring
  obtain ⟨hM_score_mean, hM_score_L2, hM_score_var⟩ := PilotFields.half_pilotMean_facts
    bar hp.barMeasurable hbar_L2 hp.noiseMeasurable hη_L2 hp.noiseCentered
    (boundedPairRegressionOperator_measurable_apply C θ hθ) (by positivity) hp.lamNonnegative
    (boundedPairRegressionOperator_norm_le C θ) (boundedPairRegressionOperator_symmetric C θ)
    hp.linearTest M_score hM_score_ae
  have hnoise_sym (a_v b_v : PairVector) : ⟪a_v, pairNoiseOperator b_v⟫ = ⟪pairNoiseOperator a_v, b_v⟫ := by
    rw [← real_inner_comm (pairNoiseOperator a_v) b_v, pairNoiseOperator_inner, pairNoiseOperator_inner]; ring
  obtain ⟨hM_noise_mean, hM_noise_L2, hM_noise_var0⟩ := PilotFields.half_pilotMean_facts
    bar hp.barMeasurable hbar_L2 hp.noiseMeasurable hη_L2 hp.noiseCentered
    (pairNoiseOperator.continuous.measurable.comp measurable_snd) (by norm_num : (0 : ℝ) ≤ 2) hp.lamNonnegative
    (fun _ => pairNoiseOperator_norm_le) (fun _ => hnoise_sym) hp.linearTest M_noise hM_noise_ae
  have hM_noise_var : (∫ p, (M_noise p - ∫ z, M_noise z ∂μ.prod μ) ^ 2 ∂μ.prod μ) ≤ 3 * lam * B_var :=
    hM_noise_var0.trans_eq (by dsimp [B_var]; ring)
  -- Denominator lower bound `1 / 2 ≤ ∫ M_noise` and score bias `|∫ M_score| ≤ (p+ / 2) * b^2`
  have hfloor : 2 * (1 / 4 : ℝ) ≤ ∫ p, M_noise p ∂μ.prod μ := by
    rw [hM_noise_mean]
    have hOp := PilotFields.operatorField_memLp (pairNoiseOperator.continuous.measurable.comp measurable_snd)
      (fun _ => pairNoiseOperator_norm_le) hp.barMeasurable hbar_L2
    have hLow : M_des.real univ ≤ ∫ w, ⟪bar w, pairNoiseOperator (bar w)⟫ ∂M_des := by
      simpa only [integral_const, smul_eq_mul, mul_one] using
        integral_mono_ae (integrable_const (1 : ℝ)) (PilotFields.inner_integrable hbar_L2 hOp)
          (hfirst.mono fun w hw => by dsimp only; rw [pairNoiseOperator_inner, hw]; nlinarith [sq_nonneg (bar w 1)])
    linarith [(regularPairDesignMeasure_mass_bounds C θ hθ k hk).1, hLow]
  have hbias_sq : (∫ p, M_score p ∂μ.prod μ) ^ 2 ≤ ((C.densityUpper / 2) * b ^ 2) ^ 2 := by
    have hnn : 0 ≤ ∫ p, M_score p ∂μ.prod μ := by
      rw [hM_score_mean]
      refine mul_nonneg (by norm_num) (integral_nonneg fun w => ?_)
      change 0 ≤ ⟪bar w, InnerProductSpace.rankOne ℝ
        (pairResponseVector (boundedRegression C θ w.1) (boundedRegression C θ w.2))
        (pairResponseVector (boundedRegression C θ w.1) (boundedRegression C θ w.2)) (bar w)⟫
      rw [InnerProductSpace.inner_right_rankOne_apply, real_inner_comm (bar w)]
      exact mul_self_nonneg _
    have hup : (∫ p, M_score p ∂μ.prod μ) ≤ (C.densityUpper / 2) * b ^ 2 := by
      rw [hM_score_mean]
      have hOp := PilotFields.operatorField_memLp (boundedPairRegressionOperator_measurable_apply C θ hθ)
        (boundedPairRegressionOperator_norm_le C θ) hp.barMeasurable hbar_L2
      have hpt : (fun w => ⟪bar w, boundedPairRegressionOperator C θ w (bar w)⟫) ≤ᵐ[M_des] fun _ => b ^ 2 := by
        filter_upwards [boundedPairRegressionOperator_eq_ae C θ hθ k hk, hresidual] with w hw hr
        change ⟪bar w, boundedPairRegressionOperator C θ w (bar w)⟫ ≤ b ^ 2
        rw [hw, InnerProductSpace.inner_right_rankOne_apply, real_inner_comm (bar w)]
        have hSq := pow_le_pow_left₀ (abs_nonneg _) hr 2
        rw [sq_abs] at hSq
        simpa only [pow_two] using hSq
      have hI := integral_mono_ae (PilotFields.inner_integrable hbar_L2 hOp) (integrable_const (b ^ 2)) hpt
      simp only [integral_const, smul_eq_mul] at hI
      calc (1 / 2) * ∫ w, ⟪bar w, boundedPairRegressionOperator C θ w (bar w)⟫ ∂M_des
        _ ≤ (1 / 2) * (M_des.real univ * b ^ 2) := mul_le_mul_of_nonneg_left hI (by norm_num)
        _ ≤ (1 / 2) * (C.densityUpper * b ^ 2) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (regularPairDesignMeasure_mass_bounds C θ hθ k hk).2 (sq_nonneg b)) (by norm_num)
        _ = (C.densityUpper / 2) * b ^ 2 := by ring
    exact pow_le_pow_left₀ hnn hup 2
  -- Two-stage centered evaluation variance for `S` and `D`
  let X (i : Fin m) (x : Fin m → Observation d) := x i
  have hind : iIndepFun X μ := iIndepFun_pi (μ := fun _ : Fin m => obs) (X := fun _ => id) fun _ => aemeasurable_id
  have hX (i : Fin m) : MeasurePreserving (X i) μ obs := measurePreserving_eval (fun _ : Fin m => obs) i
  have hm2 : 2 ≤ m := threeBlockSize_two_le hn
  have hkp : 0 < (k : ℝ) ^ d := pow_pos (by exact_mod_cast hk) d
  have hpplus : 0 ≤ C.densityUpper := by linarith [C.one_lt_densityUpper]
  let c_eval := C.densityUpper / (m : ℝ) + (k : ℝ) ^ d / (2 * (m : ℝ) * (m - 1 : ℕ))
  have hc_eval_nn : 0 ≤ c_eval := by dsimp [c_eval]; positivity
  let S := PairUStatistic.fieldPairAverage m ((k : ℝ) ^ d) K_score X
  let D := PairUStatistic.fieldPairAverage m ((k : ℝ) ^ d) K_noise X
  let N := PairUStatistic.fieldPairAverage m ((k : ℝ) ^ d) (coefficientPairNumeratorKernel k hk c_pil) X
  have hmK_score := PilotFields.maskedPilotKernel_measurable
    (c := fun x z => c_pil x (pairCovariates z))
    (A := fun z : Observation d × Observation d => pairScoreOperator θ.variance z.1.2 z.2.2)
    (q := sameLabelKernel (regularObservationLabel (d := d) k hk))
    hc_obs (observationPairScoreOperator_measurable_apply (d := d) θ.variance) hq_meas
  have hmK_noise := PilotFields.maskedPilotKernel_measurable
    (c := fun x z => c_pil x (pairCovariates z))
    (A := fun _ : Observation d × Observation d => pairNoiseOperator)
    (q := sameLabelKernel (regularObservationLabel (d := d) k hk))
    hc_obs (pairNoiseOperator.continuous.measurable.comp measurable_snd) hq_meas
  have hSv0 := PairUStatistic.fieldPairAverage_centered_sq_le
    (π := μ.prod μ) (ν := μ) (μ := obs) (G := K_score)
    (cap := C.densityUpper / (k : ℝ) ^ d) (bound := C.densityUpper) hm2 X hind hX
    (regularObservationLabel (d := d) k hk) (regularObservationLabel_measurable (d := d) k hk)
    hmK_score hK_score_L2
    (fun p x y hxy => by simp [K_score, regularObservationLabel, sameLabelKernel] at hxy ⊢; exact hxy.elim)
    hkp (div_nonneg hpplus hkp.le)
    (fun i => by rw [regularObservationLabel_mass C θ hθ k hk i]; exact regularGridProbability_cap C θ hθ k hk i)
    (by rw [mul_div_cancel₀ _ hkp.ne']) hM_score_L2 hM_score_var
  have hSv : (∫ z, (S z - ∫ p, M_score p ∂μ.prod μ) ^ 2 ∂(μ.prod μ).prod μ) ≤
      2 * c_eval * (L_coef ^ 2 * responseOperatorEnergyBound C * C.densityUpper) +
      (3 / 2) * lam * (2 * C.holderBound ^ 2 + 1) ^ 2 * B_var := by
    refine hSv0.trans ?_
    have hE : (k : ℝ) ^ d * (∫ z, K_score z.1 z.2 ^ 2 ∂(μ.prod μ).prod (obs.prod obs)) ≤
        L_coef ^ 2 * responseOperatorEnergyBound C * C.densityUpper :=
      (mul_le_mul_of_nonneg_left hK_score_en hkp.le).trans_eq (by field_simp [hkp.ne'])
    change 2 * c_eval * _ + 2 * ((3 / 4) * lam * (2 * C.holderBound ^ 2 + 1) ^ 2 * B_var) ≤ _
    have hm_e := mul_le_mul_of_nonneg_left hE (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc_eval_nn)
    linarith [hm_e]
  have hDv0 := PairUStatistic.fieldPairAverage_centered_sq_le
    (π := μ.prod μ) (ν := μ) (μ := obs) (G := K_noise)
    (cap := C.densityUpper / (k : ℝ) ^ d) (bound := C.densityUpper) hm2 X hind hX
    (regularObservationLabel (d := d) k hk) (regularObservationLabel_measurable (d := d) k hk)
    hmK_noise hK_noise_L2
    (fun p x y hxy => by simp [K_noise, rawModelPairNoise, regularObservationLabel, sameLabelKernel] at hxy ⊢; exact hxy.elim)
    hkp (div_nonneg hpplus hkp.le)
    (fun i => by rw [regularObservationLabel_mass C θ hθ k hk i]; exact regularGridProbability_cap C θ hθ k hk i)
    (by rw [mul_div_cancel₀ _ hkp.ne']) hM_noise_L2 hM_noise_var
  have hDv : (∫ z, (D z - ∫ p, M_noise p ∂μ.prod μ) ^ 2 ∂(μ.prod μ).prod μ) ≤
      8 * c_eval * (L_coef ^ 2 * C.densityUpper) + 6 * lam * B_var := by
    refine hDv0.trans ?_
    have hE : (k : ℝ) ^ d * (∫ z, K_noise z.1 z.2 ^ 2 ∂(μ.prod μ).prod (obs.prod obs)) ≤
        4 * L_coef ^ 2 * C.densityUpper :=
      (mul_le_mul_of_nonneg_left hK_noise_en hkp.le).trans_eq (by field_simp [hkp.ne'])
    change 2 * c_eval * _ + 2 * (3 * lam * B_var) ≤ _
    have hm_e := mul_le_mul_of_nonneg_left hE (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc_eval_nn)
    linarith [hm_e]
  -- Stabilized ratio MSE bound
  have hN_eq : N = fun z => S z + θ.variance * D z := funext fun z => by
    have hkern : coefficientPairNumeratorKernel k hk c_pil = fun p w => K_score p w + θ.variance * K_noise p w := by
      funext p w
      simp only [coefficientPairNumeratorKernel, K_score, K_noise, rawModelPairNoise, pairCovariates,
        pairScoreOperator, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        inner_sub_right, inner_smul_right]
      ring
    dsimp only [N, S, D]; rw [hkern]; exact PairUStatistic.fieldPairAverage_add_smul ..
  have hmS : Measurable S := PairUStatistic.fieldPairAverage_measurable _ _ hmK_score X fun i => (hX i).measurable
  have hmD : Measurable D := PairUStatistic.fieldPairAverage_measurable _ _ hmK_noise X fun i => (hX i).measurable
  have hmN : Measurable N := hN_eq ▸ hmS.add (hmD.const_mul _)
  have hS_L2 : MemLp S 2 ((μ.prod μ).prod μ) := PairUStatistic.fieldPairAverage_memLp _ hK_score_L2 X hind hX
  have hD_L2 : MemLp D 2 ((μ.prod μ).prod μ) := PairUStatistic.fieldPairAverage_memLp _ hK_noise_L2 X hind hX
  have hdif : (fun z => N z - θ.variance * D z) = S := funext fun z => by rw [hN_eq]; ring
  have hr_mse := stabilized_ratio_lintegral_mse_le ((μ.prod μ).prod μ) hmN hmD
    (hdif ▸ hS_L2) hD_L2 (by norm_num : (0 : ℝ) < 1 / 4)
    hθ.2.2.2.2.2.1 hθ.2.2.2.2.2.2.1 (C.varianceLower_pos.le.trans hθ.2.2.2.2.2.1) hfloor
  simp_rw [fun z => congrFun hdif z] at hr_mse
  -- Uncenter `S` using `(S z)^2 ≤ 2 * (S z - c)^2 + 2 * c^2`
  have hS_sq : (∫ z, S z ^ 2 ∂(μ.prod μ).prod μ) ≤
      2 * (∫ z, (S z - ∫ p, M_score p ∂μ.prod μ) ^ 2 ∂(μ.prod μ).prod μ) +
      2 * ((C.densityUpper / 2) * b ^ 2) ^ 2 := by
    let c0 := ∫ p, M_score p ∂μ.prod μ
    have hc_L2 : MemLp (fun z => S z - c0) 2 ((μ.prod μ).prod μ) := hS_L2.sub (memLp_const c0)
    have hmono := integral_mono (g := fun z => 2 * (S z - c0) ^ 2 + 2 * c0 ^ 2) hS_L2.integrable_sq
      ((hc_L2.integrable_sq.const_mul 2).add (integrable_const (2 * c0 ^ 2)))
      fun z => by dsimp only; nlinarith [sq_nonneg (S z - 2 * c0)]
    rw [integral_add (f := fun z => 2 * (S z - c0) ^ 2) (g := fun _ => 2 * c0 ^ 2)
      (hc_L2.integrable_sq.const_mul 2) (integrable_const _), integral_const_mul, integral_const] at hmono
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hmono
    dsimp [c0] at hmono; linarith [hmono, hbias_sq]
  have hmse_real := pairRiskBudget_rate_le (n := n) (m := m) (k := k) C (by omega) hm2 hk
    (threeBlockSize_fraction hn) hp.constantNonnegative hp.budgetNonnegative hB_var_nn hB_var_le
    (b := b) (by
      have hd_mul := mul_le_mul_of_nonneg_left hDv (sq_nonneg C.varianceUpper)
      have hb4 : 2 * ((C.densityUpper / 2) * b ^ 2) ^ 2 = (C.densityUpper ^ 2 / 2) * b ^ 4 := by ring
      have hsum := add_le_add (hS_sq.trans (add_le_add (mul_le_mul_of_nonneg_left hSv (by norm_num)) (le_of_eq hb4))) hd_mul
      dsimp only [c_eval, L_coef, lam] at hsum
      exact hsum.trans_eq (by ring))
  -- Connect to `meanSquaredRisk (coefficientPairEstimator C k hk c hmc) θ`
  have hrisk_eq : meanSquaredRisk (coefficientPairEstimator C k hk c hmc) θ =
      ∫⁻ z, ENNReal.ofReal ((stabilizedRatio C.varianceLower C.varianceUpper (1 / 4) N D z - θ.variance) ^ 2)
        ∂(μ.prod μ).prod μ := by
    unfold meanSquaredRisk coefficientPairEstimator
    have hmp := (threeBlockSplit_measurePreserving (n := n) C θ hθ).lintegral_comp
      ((((coefficientPairStatistic_measurable C m k hk hmc).sub_const θ.variance).pow_const 2).ennreal_ofReal)
    rw [hmp]
    simp_rw [coefficientPairStatistic, heq]
    rfl
  rw [hrisk_eq]
  have hmse := hr_mse.trans (ENNReal.ofReal_mono hmse_real)
  have hC0 := (pairRateSquaredConstant_pos C hp.constantNonnegative
    (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (0 : ℝ) < 1 / 4)).le
  have hR0 : 0 ≤ b ^ 2 + pairFluctuationScale (d := d) n k * (1 + W) :=
    add_nonneg (sq_nonneg b) (mul_nonneg (pairFluctuationScale_nonneg n k) (by linarith [hp.budgetNonnegative]))
  have hrms := ENNReal.rpow_le_rpow hmse (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rwa [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hC0 (sq_nonneg _)) (by norm_num),
    ← Real.sqrt_eq_rpow, Real.sqrt_mul hC0, Real.sqrt_sq hR0] at hrms

end NearlyMinimax
