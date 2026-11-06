module
public import NearlyMinimax.HighHistoryLikelihoodScore
public import NearlyMinimax.MixtureRisk
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable {E : Type*} {d n : ℕ}
section
section
section
variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
theorem map_snd_prod_withDensity_ofReal (ν : Measure Ω) [IsProbabilityMeasure ν]
    (μ : Measure Z) [SFinite μ] (f ) (hf : Measurable f)
    (C ) (hC : 0 ≤ C) (hbound : ∀ z, 0 ≤ f z ∧ f z ≤ C) :
    ((ν.prod μ).withDensity (fun z => ENNReal.ofReal (f z))).map Prod.snd =
      μ.withDensity (fun z => ENNReal.ofReal (∫ ω, f (ω,z) ∂ν)) := by
  have h_map_snd_prod_withDensity (f) (hf : Measurable f) : ((ν.prod μ).withDensity f).map Prod.snd =
      μ.withDensity (fun z => ∫⁻ ω, f (ω,z) ∂ν) := by
    apply Measure.ext_of_lintegral
    intro G hG
    have hGm : Measurable (fun z : Ω × Z => G z.2) := hG.comp measurable_snd
    rw [lintegral_map hG measurable_snd,
      lintegral_withDensity_eq_lintegral_mul _ hf hGm,
      lintegral_prod_symm' _ (hf.mul hGm),
      lintegral_withDensity_eq_lintegral_mul _ (hf.lintegral_prod_left') hG]
    apply lintegral_congr
    intro z
    exact lintegral_mul_const (G z) (hf.comp (measurable_id.prodMk measurable_const))
  rw [(h_map_snd_prod_withDensity _ hf.ennreal_ofReal)]
  congr 1
  funext z
  have hi : Integrable (fun ω => f (ω,z)) ν := by
    apply Integrable.of_bound (hf.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable C
    exact Eventually.of_forall fun ω => by
      change ‖f (ω,z)‖ ≤ C
      rw [Real.norm_eq_abs, abs_of_nonneg (hbound _).1]
      exact (hbound _).2
  exact (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun ω => (hbound _).1)).symm
theorem integral_likelihood_pos (ν : Measure Ω) [IsProbabilityMeasure ν]
    (f : Ω → ℝ) (hf : Measurable f) (C : ℝ) (hpos : ∀ ω, 0 < f ω)
    (hbound : ∀ ω, f ω ≤ C) : 0 < ∫ ω, f ω ∂ν := by
  have hi : Integrable f ν := by
    apply Integrable.of_bound hf.aestronglyMeasurable C
    exact Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hpos ω).le]
      exact hbound ω
  rw [integral_pos_iff_support_of_nonneg (fun ω => (hpos ω).le) hi]
  have hs : Function.support f = univ := by
    ext ω
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (hpos ω).ne'
  simp [hs]
end
variable {Ω : Type*} [MeasurableSpace Ω]
def highMarginalRawLikelihood  (ν : Measure Ω) (n ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) : ℝ :=
  ∫ ω, highRawSampleLikelihood n a V (p ω) (F ω) z ∂ν
theorem highMarginalRawLikelihood_measurable  (ν ) [SFinite ν]
    (n : ℕ) (a V : ℝ) (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable (highMarginalRawLikelihood ν n a V p F) :=
  (highRawSampleLikelihood_joint_measurable n a V p F hp hF).stronglyMeasurable.integral_prod_left'.measurable
theorem highMarginalRawLikelihood_pos  (ν ) [IsProbabilityMeasure ν]
    (n a V P) (hP : 0 ≤ P) (ha : a ≠ 0)
    (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hpp : ∀ ω x, 0 < p ω x) (hpb : ∀ ω x, |p ω x| ≤ P)
    (hq : ∀ ω x y, 0 < ternaryMass a (F ω x) V y)
    (z ) :
    0 < highMarginalRawLikelihood ν n a V p F z := by
  apply integral_likelihood_pos ν _
    (highRawSampleLikelihood_joint_measurable n a V p F hp hF).of_uncurry_right (P^n)
  · exact fun ω => highRawSampleLikelihood_pos n a V p F hpp hq ω z
  · exact fun ω => (le_abs_self _).trans
      (highRawSampleLikelihood_abs_le n a V P hP _ _ (hpb ω) ha
        (fun x y => (hq ω x y).le) z)
theorem highMassTilt_index_marginal_density  (ν ) [IsProbabilityMeasure ν]
    (n : ℕ) (a V : ℝ) (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (aRaw bRaw : ℝ) (haRaw : 0 < aRaw) (ha : a ≠ 0)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y) :
    (highSampleIndexKernel n a V p F hp hF) ∘ₘ
        (massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n) =
      (highSampleReference d n).withDensity (fun z => ENNReal.ofReal
        (highMarginalRawLikelihood ν n a V p F z /
          massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n)) := by
  let m : Ω → ℝ := fun ω => highRawDensityMass (p ω)
  have hm  := highRawDensityMass_joint_measurable p hp
  have hb (ω : Ω) : aRaw ≤ m ω ∧ m ω ≤ bRaw :=
    highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw
      (Eventually.of_forall (hraw ω))
  have hG := massPowerNormalizer_pos ν m hm n aRaw bRaw haRaw hb
  let _ := massPowerTilt_isProbability ν m hm n aRaw bRaw haRaw hb
  have hpabs (ω : Ω) (x : Covariate d) : |p ω x| ≤ |bRaw| := by
    rw [abs_of_nonneg (haRaw.le.trans (hraw ω x).1)]
    exact (hraw ω x).2.trans (le_abs_self _)
  let L : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) → ℝ := fun z =>
    highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 / massPowerNormalizer ν m n
  have hLb (z) : 0 ≤ L z ∧ L z ≤ |bRaw|^n / massPowerNormalizer ν m n := by
    have hl0 : 0 ≤ highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 :=
      Finset.prod_nonneg (fun i _ => mul_nonneg (haRaw.le.trans (hraw z.1 _).1) (hq z.1 _ _))
    have hlb := highRawSampleLikelihood_abs_le n a V |bRaw| (abs_nonneg _) _ _ (hpabs z.1) ha (hq z.1) z.2
    exact ⟨div_nonneg hl0 hG.le, div_le_div_of_nonneg_right ((le_abs_self _).trans hlb) hG.le⟩
  rw [← Measure.snd_compProd, Measure.snd,
    massPowerTilt_highSample_compProd ν n a V p F hp hF aRaw bRaw haRaw hraw, map_snd_prod_withDensity_ofReal ν (highSampleReference d n) L ((highRawSampleLikelihood_joint_measurable n a V p F hp hF).div_const _)
    (|bRaw|^n / massPowerNormalizer ν m n) (by positivity) hLb]
  congr 1
  funext z
  simp only [L, integral_div, highMarginalRawLikelihood, m]
end
section
variable {Ω : Type*} [MeasurableSpace Ω]
theorem weighted_score_energy_contraction (ν : Measure Ω) (L D : Ω → ℝ)
    (hL : ∀ ω, 0 < L ω) (hiL : Integrable L ν) (hiD : Integrable D ν)
    (hiE : Integrable (fun ω => D ω ^ 2 / L ω) ν)
    (hmean : 0 < ∫ ω, L ω ∂ν) :
    (∫ ω, D ω ∂ν)^2 / (∫ ω, L ω ∂ν) ≤ ∫ ω, D ω ^ 2 / L ω ∂ν := by
  let r : ℝ := (∫ ω, D ω ∂ν) / (∫ ω, L ω ∂ν)
  have he (ω : Ω) : (D ω - r * L ω)^2 / L ω =
      D ω^2 / L ω - 2*r*D ω + r^2*L ω := by
    field_simp [(hL ω).ne']
    ring
  have hn : 0 ≤ ∫ ω, (D ω - r * L ω)^2 / L ω ∂ν :=
    integral_nonneg (fun ω => div_nonneg (sq_nonneg _) (hL ω).le)
  have hv : (∫ ω, (D ω - r * L ω)^2 / L ω ∂ν) =
      (∫ ω, D ω^2 / L ω ∂ν) - 2*r*(∫ ω, D ω ∂ν) + r^2*(∫ ω, L ω ∂ν) := by
    simp_rw [he]
    have hv1 := integral_add (hiE.sub (hiD.const_mul (2*r))) (hiL.const_mul (r^2))
    rw [integral_sub' hiE (hiD.const_mul (2*r)), integral_const_mul, integral_const_mul] at hv1
    simpa only [Pi.sub_apply] using hv1
  rw [hv] at hn
  have hr : -2*r*(∫ ω, D ω ∂ν) + r^2*(∫ ω, L ω ∂ν) =
      -(∫ ω, D ω ∂ν)^2 / (∫ ω, L ω ∂ν) := by
    dsimp only [r]
    field_simp [hmean.ne']
    ring
  rw [neg_div] at hr
  nlinarith [hn, hr]
end
def decodeTernaryResponse (a y : ℝ) : Fin 3 :=
  if y = -a then 0 else if y = 0 then 1 else 2
def decodeDesignResponse  (a : ℝ) (z : Fin n → Observation d) :
    (Fin n → Covariate d) × (Fin n → Fin 3) :=
  (fun i => (z i).1, fun i => decodeTernaryResponse a (z i).2)
theorem decodeDesignResponse_measurable  (a ) :
    Measurable (decodeDesignResponse (d := d) (n := n) a) := by
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro i
    exact measurable_fst.comp (measurable_pi_apply i)
  · apply measurable_pi_lambda
    intro i
    have h_decodeTernaryResponse_measurable : Measurable (decodeTernaryResponse a) := by
      apply Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const
      exact Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const measurable_const
    exact h_decodeTernaryResponse_measurable.comp (measurable_snd.comp (measurable_pi_apply i))
theorem decodeDesignResponse_encode  (a : ℝ) (ha : 0 < a)
    (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    decodeDesignResponse a (encodeDesignResponse a z) = z := by
  apply Prod.ext
  · rfl
  · funext i
    have h_decodeTernaryResponse_value (y) : decodeTernaryResponse a (ternaryValue a y) = y := by
      have hna  := neg_ne_zero.mpr ha.ne'
      have han : a ≠ -a := by linarith
      fin_cases y <;> simp [decodeTernaryResponse, ternaryValue, ha.ne', han]
    exact h_decodeTernaryResponse_value (z.2 i)
variable {J : Type*} [Fintype J] [LinearOrder J]
def highMarginalLikelihoodDerivative  [MeasurableSpace E] 
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) (π : Measure E) (activation : E → ℝ)
    (n : ℕ) (a V η : ℝ) (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (z : (Fin n → Covariate d) × (Fin n → Fin 3)) : ℝ :=
  ∫ ω, highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F ω z ∂ν
def highMarginalIndexScore  [MeasurableSpace E] 
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) (π : Measure E) (activation : E → ℝ)
    (n : ℕ) (a V η : ℝ) (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (z : (Fin n → Covariate d) × (Fin n → Fin 3)) : ℝ :=
  highMarginalLikelihoodDerivative dependent hsymm ν π activation n a V η p F z /
    highMarginalRawLikelihood ν n a V p F z
def highMarginalRealScore  [MeasurableSpace E] 
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) (π : Measure E) (activation : E → ℝ)
    (n : ℕ) (a V η : ℝ) (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (z : Fin n → Observation d) : ℝ :=
  highMarginalIndexScore dependent hsymm ν π activation n a V η p F (decodeDesignResponse a z)
theorem highMarginalIndexScore_measurable  [MeasurableSpace E]
    [StandardBorelSpace E] 
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) [SFinite ν] (π : Measure E) [SFinite π]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a V η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable (highMarginalIndexScore dependent hsymm ν π activation n a V η p F) := by
  exact (highHistoryLikelihoodDerivative_measurable dependent hsymm π activation ham n a V η p F hp hF).stronglyMeasurable.integral_prod_left'.measurable.div
    (highMarginalRawLikelihood_measurable ν n a V p F hp hF)
theorem highMarginalRealScore_measurable  [MeasurableSpace E]
    [StandardBorelSpace E] 
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) [SFinite ν] (π : Measure E) [SFinite π]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a V η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable (highMarginalRealScore dependent hsymm ν π activation n a V η p F) :=
  (highMarginalIndexScore_measurable dependent hsymm ν π activation ham n a V η p F hp hF).comp
    (decodeDesignResponse_measurable a)
theorem highMarginalRealScore_integral  [MeasurableSpace E]
    [StandardBorelSpace E] 
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) [IsProbabilityMeasure ν]
    (π : Measure E) [IsProbabilityMeasure π] (activation : E → ℝ) (ham : Measurable activation)
    (Ba ) (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    (n ) (a V η aRaw bRaw B : ℝ) (ha : 0 < a) (haRaw : 0 < aRaw) (hB : 0 ≤ B)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 < ternaryMass a (F ω x) V y)
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B) :
    (∫ z, H z * highMarginalRealScore dependent hsymm ν π activation n a V η p F z
      ∂(highRealSampleKernel n a V p F hp hF) ∘ₘ
        (massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n)) =
      (massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
        ∫ z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)),
          H (encodeDesignResponse a z.2) *
            highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2
          ∂ν.prod (highSampleReference d n) := by
  have hm : Measurable (fun z => H z *
      highMarginalRealScore dependent hsymm ν π activation n a V η p F z) :=
    hH.mul (highMarginalRealScore_measurable dependent hsymm ν π activation ham n a V η p F hp hF)
  rw [highRealSampleKernel, ← Measure.map_comp _ _ (encodeDesignResponse_measurable a),
    integral_map_of_stronglyMeasurable (encodeDesignResponse_measurable a) hm.stronglyMeasurable]
  have h_highMarginalIndexScore_integral : (∫ z, H (encodeDesignResponse a z) *
      highMarginalIndexScore dependent hsymm ν π activation n a V η p F z
      ∂(highSampleIndexKernel n a V p F hp hF) ∘ₘ
        (massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n)) =
      (massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
        ∫ z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)),
          H (encodeDesignResponse a z.2) *
            highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2
          ∂ν.prod (highSampleReference d n) := by
    let m := fun ω => highRawDensityMass (p ω)
    have hm : Measurable m := highRawDensityMass_joint_measurable p hp
    have hb (ω) : aRaw ≤ m ω ∧ m ω ≤ bRaw :=
      highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw
        (Eventually.of_forall (hraw ω))
    have hG := massPowerNormalizer_pos ν m hm n aRaw bRaw haRaw hb
    have hpb (ω : HistoryMarked dependent E) (x : Covariate d) : |p ω x| ≤ |bRaw| := by
      rw [abs_of_nonneg (haRaw.le.trans (hraw ω x).1)]
      exact (hraw ω x).2.trans (le_abs_self _)
    have hL (z) := highMarginalRawLikelihood_pos ν n a V |bRaw| (abs_nonneg _) ha.ne' p F hp hF
      (fun ω x => haRaw.trans_le (hraw ω x).1) hpb hq z
    have hdens : Measurable (fun z => ENNReal.ofReal
        (highMarginalRawLikelihood ν n a V p F z / massPowerNormalizer ν m n)) :=
      ((highMarginalRawLikelihood_measurable ν n a V p F hp hF).div_const _).ennreal_ofReal
    rw [highMassTilt_index_marginal_density ν n a V p F hp hF aRaw bRaw haRaw ha.ne' hraw
      (fun ω x y => (hq ω x y).le),
      integral_withDensity_eq_integral_toReal_smul hdens (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp_rw [ENNReal.toReal_ofReal (div_nonneg (hL _).le hG.le), smul_eq_mul]
    have hi : Integrable (fun z =>
        H (encodeDesignResponse a z.2) *
          highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2)
        (ν.prod (highSampleReference d n)) := by
      apply Integrable.of_bound
        (((hH.comp (encodeDesignResponse_measurable a)).comp measurable_snd).mul
          (highHistoryLikelihoodDerivative_measurable dependent hsymm π activation ham n a V η p F hp hF)).aestronglyMeasurable
        (B * ((Fintype.card J ) * (Ba * |bRaw|^n) + η^2 * (|bRaw|^n * (n/a^2))))
      exact Eventually.of_forall fun z => by
        change ‖H (encodeDesignResponse a z.2) *
          highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2‖ ≤ _
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hHb _) (highHistoryLikelihoodDerivative_abs_le π dependent hsymm activation Ba hBa
          habound n a V η |bRaw| (abs_nonneg _) ha p F hpb (fun ω x y => (hq ω x y).le) z.1 z.2)
          (abs_nonneg _) hB
    calc
      _ = (massPowerNormalizer ν m n)⁻¹ *
          ∫ z, H (encodeDesignResponse a z) *
            highMarginalLikelihoodDerivative dependent hsymm ν π activation n a V η p F z
            ∂highSampleReference d n := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by
          dsimp only [highMarginalIndexScore]
          field_simp [(hL z).ne', hG.ne']
      _ = _ := by
        congr 1
        rw [MeasureTheory.integral_prod_symm _ hi]
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by
          dsimp only [highMarginalLikelihoodDerivative]
          rw [integral_const_mul]
  convert (h_highMarginalIndexScore_integral) using 1
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only [highMarginalRealScore]
    rw [decodeDesignResponse_encode a ha]
end
section
section
variable {Ω : Type*} [MeasurableSpace Ω]
theorem highTiltedObservableMean_eq_dataMean  (ν ) [IsProbabilityMeasure ν]
    (n a V aRaw bRaw B) (ha : a ≠ 0) (haRaw : 0 < aRaw) (hB : 0 ≤ B)
    (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
    (H ) (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B) :
    highTiltedObservableMean ν n a V p F hp hF H =
      ∫ z, H z ∂(highRealSampleKernel n a V p F hp hF) ∘ₘ
        (massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n) := by
  have hb (ω) : aRaw ≤ highRawDensityMass (p ω) ∧ highRawDensityMass (p ω) ≤ bRaw :=
    highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw
      (Eventually.of_forall (hraw ω))
  let _ := massPowerTilt_isProbability ν _ (highRawDensityMass_joint_measurable p hp) n aRaw bRaw haRaw hb
  let _ := highRealSampleKernel_markov n a V p F hp hF aRaw bRaw haRaw hraw ha hq
  exact (probability_kernel_integral _ _ H (by apply Integrable.of_bound hH.aestronglyMeasurable B; exact Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hHb z)).symm
end
variable {J : Type*} [Fintype J] [LinearOrder J]
theorem historyMarkedPrior_dataMean_score_hasDerivAt (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (T Ba : ℝ) (hBa : 0 ≤ Ba)
     [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (activation : E → ℝ) (hactivation : Measurable activation)
    (hcenter : ∫ e, activation e ∂π = 0) (habound : ∀ e, |activation e| ≤ Ba)
    (hsmall : T * Ba / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
     (n : ℕ) (a v η aRaw bRaw : ℝ) (ha : 0 < a) (haRaw : 0 < aRaw)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ u ∈ Icc 0 T, ∀ ω x y, 0 < ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    (hmass : ∀ u ∈ Icc 0 T,
      (historyMarkedPrior dependent Δ u π activation).map (fun ω => highRawDensityMass (p ω)) =
      (historyMarkedPrior dependent Δ 0 π activation).map (fun ω => highRawDensityMass (p ω)))
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H)
    (B : ℝ) (hB : 0 ≤ B) (hHb : ∀ z, |H z| ≤ B)
    (t : ℝ) (ht : 0 < t) (htT : t < T) :
    HasDerivAt (fun u => ∫ z, H z ∂(highRealSampleKernel n a (v - η^2*u) p F hp hF) ∘ₘ
      (massPowerTilt (historyMarkedPrior dependent Δ u π activation)
        (fun ω => highRawDensityMass (p ω)) n))
      (∫ z, H z * highMarginalRealScore dependent hsymm
        (historyMarkedPrior dependent Δ t π activation) π activation n a (v - η^2*t) η p F z
        ∂(highRealSampleKernel n a (v - η^2*t) p F hp hF) ∘ₘ
          (massPowerTilt (historyMarkedPrior dependent Δ t π activation)
            (fun ω => highRawDensityMass (p ω)) n)) t := by
  have hq0 (u : ℝ) (hu : u ∈ Icc 0 T) (ω : HistoryMarked dependent E) (x : Covariate d) (y : Fin 3) :=
    (hq u hu ω x y).le
  have hprob u (hu : u ∈ Icc 0 T) :
      IsProbabilityMeasure (historyMarkedPrior dependent Δ u π activation) := by
    have hs  :=
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2 hBa)
        (historyReferenceRho_pos Δ).le).trans hsmall
    exact historyMarkedPrior_probability dependent hrefl hsymm Δ hΔ hlabels u Ba hu.1 hBa π
      activation (by apply Integrable.of_bound hactivation.aestronglyMeasurable Ba; exact Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using habound e) hcenter habound hs
  let _ := hprob t ⟨ht.le, htT.le⟩
  have h_historyMarkedPrior_tiltedObservable_hasDerivAt : HasDerivAt (fun u => highTiltedObservableMean (historyMarkedPrior dependent Δ u π activation)
      n a (v - η ^ 2 * u) p F hp hF H)
      ((massPowerNormalizer (historyMarkedPrior dependent Δ 0 π activation)
        (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
        ((-η ^ 2 * ∫ ω, highRawObservableVarianceDerivative n a (v - η ^ 2 * t) (p ω) (F ω) H
          ∂historyMarkedPrior dependent Δ t π activation) +
          historyMarkedPriorGenerator dependent hsymm Δ t π activation
            (fun ω => highRawObservable n a (v - η ^ 2 * t) (p ω) (F ω) H))) t := by
    have hpb (ω : HistoryMarked dependent E) (x : Covariate d) : |p ω x| ≤ |bRaw| := by
      rw [abs_of_nonneg (haRaw.le.trans (hraw ω x).1)]
      exact (hraw ω x).2.trans (le_abs_self _)
    have hd := historyMarkedPrior_rawObservable_hasDerivAt dependent hrefl hsymm Δ hΔ hlabels
      T Ba t ht htT hBa π activation hactivation habound hsmall n a v η |bRaw| B ha
      (abs_nonneg _) hB p F hp hF hpb (fun u hu => hq0 u ⟨hu.1.le, hu.2.le⟩) H hH hHb
    have hc := hd.const_mul ((massPowerNormalizer (historyMarkedPrior dependent Δ 0 π activation)
      (fun ω => highRawDensityMass (p ω)) n)⁻¹)
    apply hc.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht htT] with u hu
    exact historyMarkedPrior_tiltedObservable_eq_raw dependent hrefl hsymm Δ hΔ hlabels T Ba hBa
      π activation hactivation hcenter habound hsmall n a v η aRaw bRaw ha haRaw p F hp hF hraw hq0 hmass
      H hH B hB hHb u ⟨hu.1.le, hu.2.le⟩
  have hpb (ω : HistoryMarked dependent E) (x : Covariate d) : |p ω x| ≤ |bRaw| := by
    rw [abs_of_nonneg (haRaw.le.trans (hraw ω x).1)]
    exact (hraw ω x).2.trans (le_abs_self _)
  have he := highMarginalRealScore_integral dependent hsymm
    (historyMarkedPrior dependent Δ t π activation) π activation hactivation Ba hBa habound
    n a (v - η^2*t) η aRaw bRaw B ha haRaw hB p F hp hF hraw
    (hq t ⟨ht.le,htT.le⟩) H hH hHb
  have hi := highHistoryLikelihoodDerivative_observable π dependent hsymm
    (historyMarkedPrior dependent Δ t π activation) activation hactivation Ba hBa habound
    n a (v - η^2*t) η |bRaw| B (abs_nonneg _) hB ha p F hp hF hpb
    (hq0 t ⟨ht.le,htT.le⟩) H hH hHb
  rw [hi, massPowerNormalizer_eq_of_massLaw _ _ _ (highRawDensityMass_joint_measurable p hp)
    n (hmass t ⟨ht.le,htT.le⟩)] at he
  rw [he]
  apply (h_historyMarkedPrior_tiltedObservable_hasDerivAt).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht htT] with u hu
  let _ := hprob u ⟨hu.1.le,hu.2.le⟩
  exact (highTiltedObservableMean_eq_dataMean (historyMarkedPrior dependent Δ u π activation)
    n a (v - η^2*u) aRaw bRaw B ha.ne' haRaw hB p F hp hF hraw
    (hq0 u ⟨hu.1.le,hu.2.le⟩) H hH hHb).symm
theorem historyMarkedPrior_dataMean_absolutelyContinuous (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (T Ba : ℝ) (hBa : 0 ≤ Ba)
     [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (activation : E → ℝ) (hactivation : Measurable activation)
    (hcenter : ∫ e, activation e ∂π = 0) (habound : ∀ e, |activation e| ≤ Ba)
    (hsmall : T * Ba / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
     (n a v η aRaw bRaw) (ha : 0 < a) (haRaw : 0 < aRaw)
    (p F hp hF)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ u ∈ Icc 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    (hmass : ∀ u ∈ Icc 0 T,
      (historyMarkedPrior dependent Δ u π activation).map (fun ω => highRawDensityMass (p ω)) =
      (historyMarkedPrior dependent Δ 0 π activation).map (fun ω => highRawDensityMass (p ω)))
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H)
    (B : ℝ) (hB : 0 ≤ B) (hHb : ∀ z, |H z| ≤ B)
    (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval
      (fun u => ∫ z, H z ∂(highRealSampleKernel n a (v - η^2*u) p F hp hF) ∘ₘ
        (massPowerTilt (historyMarkedPrior dependent Δ u π activation)
          (fun ω => highRawDensityMass (p ω)) n)) 0 T := by
  have h_historyMarkedPrior_tiltedObservable_exists_lipschitz : ∃ K : NNReal, LipschitzOnWith K
      (fun u => highTiltedObservableMean (historyMarkedPrior dependent Δ u π activation)
        n a (v - η ^ 2 * u) p F hp hF H) (Icc 0 T) := by
    have hpb (ω : HistoryMarked dependent E) (x : Covariate d) : |p ω x| ≤ |bRaw| := by
      rw [abs_of_nonneg (haRaw.le.trans (hraw ω x).1)]
      exact (hraw ω x).2.trans (le_abs_self _)
    have h_historyMarkedPrior_rawObservable_exists_lipschitz (P : ℝ) (hP : 0 ≤ P) (hpb : ∀ ω x, |p ω x| ≤ P) : ∃ K : NNReal, LipschitzOnWith K
        (fun u => ∫ ω, highRawObservable n a (v - η ^ 2 * u) (p ω) (F ω) H
          ∂historyMarkedPrior dependent Δ u π activation) (Icc 0 T) := by
      let G : ℝ → HistoryMarked dependent E → ℝ := fun u ω => highRawObservable n a (v - η ^ 2 * u) (p ω) (F ω) H
      have hGM (u : ℝ) : Measurable (G u) := highRawObservable_measurable n a (v - η ^ 2 * u) p F hp hF H hH
      let M := B * P ^ n * (highSampleReference d n).real Set.univ
      have hM : 0 ≤ M := by dsimp [M]; positivity
      have hGb (u : ℝ) (hu : u ∈ Icc 0 T) (ω : HistoryMarked dependent E) : |G u ω| ≤ M :=
        highRawObservable_abs_le n a (v - η ^ 2 * u) P B hP hB (p ω) (F ω) (hpb ω) ha.ne' (hq u hu ω) H hHb
      let K : NNReal := ⟨B * (η ^ 2 * (P ^ n * ((n : ℝ) / a ^ 2))) * (highSampleReference d n).real Set.univ, by positivity⟩
      have hGlip (ω : HistoryMarked dependent E) : LipschitzOnWith K (fun u => G u ω) (Icc 0 T) :=
        highRawObservable_lipschitzOn n a v η T P B ha hP hB p F hp hF hpb hq H hH hHb ω
      have h_historyMarkedPrior_variable_observable_lipschitz : LipschitzOnWith
          ⟨↑K * (3 / 2 : ℝ) ^ Fintype.card J +
            M * ((historyReferenceRho Δ)⁻¹ * (Fintype.card J : ℝ) * Ba * (3 / 2 : ℝ) ^ Fintype.card J),
            by have hρ := historyReferenceRho_pos Δ; positivity⟩
          (fun u => ∫ h, G u h ∂historyMarkedPrior dependent Δ u π activation) (Icc 0 T) := by
        let μ := historyMarkedReference dependent Δ π
        let _ : IsProbabilityMeasure μ := historyMarkedReference_probability dependent hrefl hsymm Δ hΔ hlabels π
        let ρ := historyReferenceRho Δ
        let C : ℝ := (3 / 2 : ℝ) ^ Fintype.card J
        let D : ℝ := ρ⁻¹ * (Fintype.card J : ℝ) * Ba * C
        have hρ  := historyReferenceRho_pos Δ
        have : 0 ≤ C := by positivity
        have : 0 ≤ D := by dsimp [D]; positivity
        have hs (u : ℝ) (hu : u ∈ Icc 0 T) : u * Ba / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2) :=
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2 hBa) hρ.le).trans hsmall
        have hφ (u : ℝ) (hu : u ∈ Icc 0 T) (h : HistoryMarked dependent E) :
            ‖historyMarkedDensity dependent ρ u activation h‖ ≤ C := by
          have hb := historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels ρ u Ba hρ hu.1 hBa activation habound (hs u hu) h
          rw [Real.norm_eq_abs, abs_of_nonneg ((by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1)]
          exact hb.2
        let H : ℝ → HistoryMarked dependent E → ℝ := fun u h => G u h * historyMarkedDensity dependent ρ u activation h
        have hi (u : ℝ) (hu : u ∈ Icc 0 T) : Integrable (H u) μ := by
          apply Integrable.of_bound ((hGM u).mul (historyMarkedDensity_measurable dependent ρ u activation hactivation)).aestronglyMeasurable (M * C)
          exact Eventually.of_forall fun h => by
            rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs]
            exact mul_le_mul (hGb u hu h) (hφ u hu h) (norm_nonneg _) hM
        apply LipschitzOnWith.of_dist_le_mul
        intro u hu v hv
        rw [historyMarkedPrior_integral_eq_expectation dependent hrefl hsymm Δ hlabels u Ba hu.1 hBa π activation hactivation habound (hs u hu),
          historyMarkedPrior_integral_eq_expectation dependent hrefl hsymm Δ hlabels v Ba hv.1 hBa π activation hactivation habound (hs v hv)]
        change dist (∫ h, H u h ∂μ) (∫ h, H v h ∂μ) ≤ (↑K * C + M * D) * dist u v
        rw [dist_eq_norm, ← integral_sub (hi u hu) (hi v hv)]
        have hb : ∀ᵐ h ∂μ, ‖H u h - H v h‖ ≤ (↑K * C + M * D) * dist u v := by
          apply Eventually.of_forall
          intro h
          have hGdiff := (hGlip h).dist_le_mul u hu v hv
          rw [dist_eq_norm] at hGdiff
          have hφdiff := (historyMarkedDensity_lipschitzOn dependent hrefl hsymm Δ hlabels ρ T Ba hρ hBa activation habound hsmall h).dist_le_mul u hu v hv
          rw [dist_eq_norm] at hφdiff
          have he : H u h - H v h = (G u h - G v h) * historyMarkedDensity dependent ρ u activation h +
            G v h * (historyMarkedDensity dependent ρ u activation h - historyMarkedDensity dependent ρ v activation h) := by dsimp [H]; ring
          rw [he]
          calc
            _ ≤ ‖(G u h - G v h) * historyMarkedDensity dependent ρ u activation h‖ +
                ‖G v h * (historyMarkedDensity dependent ρ u activation h - historyMarkedDensity dependent ρ v activation h)‖ := norm_add_le _ _
            _ ≤ ↑K * dist u v * C + M * (D * dist u v) := by
              rw [norm_mul, norm_mul]
              exact add_le_add (mul_le_mul hGdiff (hφ u hu h) (norm_nonneg _) (by positivity))
                (mul_le_mul (by simpa only [Real.norm_eq_abs] using hGb v hv h) hφdiff (norm_nonneg _) hM)
            _ = _ := by ring
        simpa using norm_integral_le_of_norm_le_const hb
      exact ⟨_, h_historyMarkedPrior_variable_observable_lipschitz⟩
    obtain ⟨K, hK⟩ := (h_historyMarkedPrior_rawObservable_exists_lipschitz |bRaw| (abs_nonneg _) hpb)
    let c : ℝ := (massPowerNormalizer (historyMarkedPrior dependent Δ 0 π activation)
      (fun ω => highRawDensityMass (p ω)) n)⁻¹
    refine ⟨⟨|c| * K, mul_nonneg (abs_nonneg _) K.coe_nonneg⟩, ?_⟩
    apply LipschitzOnWith.of_dist_le_mul
    intro u hu w hw
    rw [historyMarkedPrior_tiltedObservable_eq_raw dependent hrefl hsymm Δ hΔ hlabels T Ba hBa
      π activation hactivation hcenter habound hsmall n a v η aRaw bRaw ha haRaw p F hp hF hraw hq hmass
      H hH B hB hHb u hu,
      historyMarkedPrior_tiltedObservable_eq_raw dependent hrefl hsymm Δ hΔ hlabels T Ba hBa
      π activation hactivation hcenter habound hsmall n a v η aRaw bRaw ha haRaw p F hp hF hraw hq hmass
      H hH B hB hHb w hw]
    change dist (c * _) (c * _) ≤ |c| * ↑K * dist u w
    rw [Real.dist_eq, ← mul_sub, abs_mul]
    have hh := hK.dist_le_mul u hu w hw
    rw [Real.dist_eq] at hh
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (abs_nonneg c)
  obtain ⟨K, hK⟩ := h_historyMarkedPrior_tiltedObservable_exists_lipschitz
  have he (u : ℝ) (hu : u ∈ Icc 0 T) :
      highTiltedObservableMean (historyMarkedPrior dependent Δ u π activation)
        n a (v - η^2*u) p F hp hF H =
      ∫ z, H z ∂(highRealSampleKernel n a (v - η^2*u) p F hp hF) ∘ₘ
        (massPowerTilt (historyMarkedPrior dependent Δ u π activation)
          (fun ω => highRawDensityMass (p ω)) n) := by
    have hs  :=
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2 hBa)
        (historyReferenceRho_pos Δ).le).trans hsmall
    let _ := historyMarkedPrior_probability dependent hrefl hsymm Δ hΔ hlabels u Ba hu.1 hBa π
      activation (by apply Integrable.of_bound hactivation.aestronglyMeasurable Ba; exact Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using habound e) hcenter habound hs
    exact highTiltedObservableMean_eq_dataMean (historyMarkedPrior dependent Δ u π activation)
      n a (v - η^2*u) aRaw bRaw B ha.ne' haRaw hB p F hp hF hraw (hq u hu) H hH hHb
  have hKd : LipschitzOnWith K
      (fun u => ∫ z, H z ∂(highRealSampleKernel n a (v - η^2*u) p F hp hF) ∘ₘ
        (massPowerTilt (historyMarkedPrior dependent Δ u π activation)
          (fun ω => highRawDensityMass (p ω)) n)) (Icc 0 T) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u hu w hw
    rw [← he u hu, ← he w hw]
    exact hK.dist_le_mul u hu w hw
  rw [← uIcc_of_le hT] at hKd
  exact hKd.absolutelyContinuousOnInterval
theorem historyMarkedPrior_dataMean_score_hasDerivAt_ae (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (T Ba : ℝ) (hBa : 0 ≤ Ba)
     [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (activation : E → ℝ) (hactivation : Measurable activation)
    (hcenter : ∫ e, activation e ∂π = 0) (habound : ∀ e, |activation e| ≤ Ba)
    (hsmall : T * Ba / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
     (n : ℕ) (a v η aRaw bRaw : ℝ) (ha : 0 < a) (haRaw : 0 < aRaw)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ u ∈ Icc 0 T, ∀ ω x y, 0 < ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    (hmass : ∀ u ∈ Icc 0 T,
      (historyMarkedPrior dependent Δ u π activation).map (fun ω => highRawDensityMass (p ω)) =
      (historyMarkedPrior dependent Δ 0 π activation).map (fun ω => highRawDensityMass (p ω)))
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H)
    (B : ℝ) (hB : 0 ≤ B) (hHb : ∀ z, |H z| ≤ B)
    : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Icc 0 T →
      HasDerivAt (fun u => ∫ z, H z ∂(highRealSampleKernel n a (v - η^2*u) p F hp hF) ∘ₘ
        (massPowerTilt (historyMarkedPrior dependent Δ u π activation)
          (fun ω => highRawDensityMass (p ω)) n))
        (∫ z, H z * highMarginalRealScore dependent hsymm
          (historyMarkedPrior dependent Δ t π activation) π activation n a (v - η^2*t) η p F z
          ∂(highRealSampleKernel n a (v - η^2*t) p F hp hF) ∘ₘ
            (massPowerTilt (historyMarkedPrior dependent Δ t π activation)
              (fun ω => highRawDensityMass (p ω)) n)) t := by
  have h0 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ ↑0 := by simp [ae_iff]
  have hT : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ T := by simp [ae_iff]
  filter_upwards [h0, hT] with t ht0 htT
  intro ht
  exact historyMarkedPrior_dataMean_score_hasDerivAt dependent hrefl hsymm Δ hΔ hlabels
    T Ba hBa π activation hactivation hcenter habound hsmall n a v η aRaw bRaw ha haRaw p F hp hF
    hraw hq hmass H hH B hB hHb t (lt_of_le_of_ne ht.1 (Ne.symm ht0)) (lt_of_le_of_ne ht.2 htT)
end
section
section
variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
def posteriorMeanScore (ν : Measure Ω) (L D : Ω × Z → ℝ) (z : Z) : ℝ :=
  (∫ ω, D (ω,z) ∂ν) / (∫ ω, L (ω,z) ∂ν)
theorem posteriorMeanScore_memLp_energy (ν : Measure Ω) [IsProbabilityMeasure ν]
    (μ : Measure Z) [SFinite μ] (L D )
    (hLm : Measurable L) (hDm : Measurable D) (hLp : ∀ z, 0 < L z)
    (LC DC G ) (hG : 0 < G) (hLb : ∀ z, L z ≤ LC) (hDb : ∀ z, |D z| ≤ DC)
    (hE : Integrable (fun z => D z^2 / L z) (ν.prod μ)) :
    let ρ := μ.withDensity (fun z => ENNReal.ofReal ((∫ ω, L (ω,z) ∂ν) / G))
    MemLp (posteriorMeanScore ν L D) 2 ρ ∧
      (∫ z, (posteriorMeanScore ν L D z)^2 ∂ρ) ≤
        G⁻¹ * ∫ z, D z^2 / L z ∂ν.prod μ := by
  let M : Z → ℝ := fun z => ∫ ω, L (ω,z) ∂ν
  let A : Z → ℝ := fun z => ∫ ω, D (ω,z) ∂ν
  let E : Z → ℝ := fun z => ∫ ω, D (ω,z)^2 / L (ω,z) ∂ν
  let R : Z → ℝ := posteriorMeanScore ν L D
  have hM : Measurable M := hLm.stronglyMeasurable.integral_prod_left'.measurable
  have h_posteriorMeanScore_measurable : Measurable (posteriorMeanScore ν L D) := hDm.stronglyMeasurable.integral_prod_left'.measurable.div
    hLm.stronglyMeasurable.integral_prod_left'.measurable
  have hR : Measurable R := h_posteriorMeanScore_measurable
  have hden (z) : 0 < M z := integral_likelihood_pos ν _
    (hLm.comp (measurable_id.prodMk measurable_const)) LC
    (fun ω => hLp (ω,z)) (fun ω => hLb (ω,z))
  have hiL (z) : Integrable (fun ω => L (ω,z)) ν := by
    apply Integrable.of_bound (hLm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable LC
    exact Eventually.of_forall fun ω => by
      change ‖L (ω,z)‖ ≤ LC
      rw [Real.norm_eq_abs, abs_of_nonneg (hLp _).le]
      exact hLb _
  have hiD (z) : Integrable (fun ω => D (ω,z)) ν := by
    apply Integrable.of_bound (hDm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable DC
    exact Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs, Function.comp_apply, id_eq] using hDb (ω,z)
  have hEnergy : ∀ᵐ z ∂μ, (M z / G) * R z^2 ≤ G⁻¹ * E z := by
    filter_upwards [hE.prod_left_ae] with z hEz
    have hc := weighted_score_energy_contraction ν (fun ω => L (ω,z)) (fun ω => D (ω,z))
      (fun ω => hLp (ω,z)) (hiL z) (hiD z) hEz (hden z)
    have halg : (M z / G) * R z^2 = G⁻¹ * (A z^2 / M z) := by
      dsimp only [R, posteriorMeanScore, A, M]
      field_simp [(hden z).ne',hG.ne']
    rw [halg]
    exact mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr hG.le)
  have hiE : Integrable (fun z => G⁻¹ * E z) μ := hE.integral_prod_right.const_mul _
  have hweighted : Integrable (fun z => (M z/G) * R z^2) μ := by
    apply hiE.mono' ((hM.div_const _).mul (hR.pow_const 2)).aestronglyMeasurable
    filter_upwards [hEnergy] with z hz
    change ‖(M z/G) * R z^2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (div_nonneg (hden z).le hG.le) (sq_nonneg _))]
    exact hz
  have hdens : Measurable (fun z => ENNReal.ofReal (M z/G)) := (hM.div_const G).ennreal_ofReal
  refine ⟨(memLp_two_iff_integrable_sq hR.aestronglyMeasurable).2 (by apply (integrable_withDensity_iff_integrable_smul' hdens (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).2; simpa only [ENNReal.toReal_ofReal (div_nonneg (hden _).le hG.le), smul_eq_mul] using hweighted), ?_⟩
  change (∫ z, R z^2 ∂(μ.withDensity (fun z => ENNReal.ofReal (M z / G)))) ≤ _
  rw [integral_withDensity_eq_integral_toReal_smul hdens (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (hden _).le hG.le), smul_eq_mul]
  calc
    _ ≤ ∫ z, G⁻¹ * E z ∂μ := integral_mono_ae hweighted hiE hEnergy
    _ = _ := by rw [integral_const_mul, ← MeasureTheory.integral_prod_symm _ hE]
end
variable {J : Type*} [Fintype J] [LinearOrder J]
theorem highMarginalRealScore_memLp_energy  [MeasurableSpace E]
    [StandardBorelSpace E] 
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) [IsProbabilityMeasure ν]
    (π : Measure E) [IsProbabilityMeasure π] (activation : E → ℝ) (ham : Measurable activation)
    (Ba ) (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    (n a V η aRaw bRaw) (ha : 0 < a) (haRaw : 0 < aRaw)
    (p F )
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 < ternaryMass a (F ω x) V y)
    (hE : Integrable (fun z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      (highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2)^2 /
        highRawSampleLikelihood n a V (p z.1) (F z.1) z.2) (ν.prod (highSampleReference d n))) :
    let P := (highRealSampleKernel n a V p F hp hF) ∘ₘ
      (massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n)
    MemLp (highMarginalRealScore dependent hsymm ν π activation n a V η p F) 2 P ∧
      (∫ z, (highMarginalRealScore dependent hsymm ν π activation n a V η p F z)^2 ∂P) ≤
        (massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
          ∫ z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)),
            (highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2)^2 /
              highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 ∂ν.prod (highSampleReference d n) := by
  let μ := highSampleReference d n
  let L : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)) → ℝ := fun z =>
    highRawSampleLikelihood n a V (p z.1) (F z.1) z.2
  let D : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)) → ℝ := fun z =>
    highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2
  let m := fun ω => highRawDensityMass (p ω)
  let G := massPowerNormalizer ν m n
  have hb (ω) : aRaw ≤ m ω ∧ m ω ≤ bRaw :=
    highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw
      (Eventually.of_forall (hraw ω))
  have hpb (ω : HistoryMarked dependent E) (x : Covariate d) : |p ω x| ≤ |bRaw| := by
    rw [abs_of_nonneg (haRaw.le.trans (hraw ω x).1)]
    exact (hraw ω x).2.trans (le_abs_self _)
  have hLp (z) : 0 < L z := highRawSampleLikelihood_pos n a V p F
    (fun ω x => haRaw.trans_le (hraw ω x).1) hq z.1 z.2
  have hLb (z) : L z ≤ |bRaw|^n := (le_abs_self _).trans
    (highRawSampleLikelihood_abs_le n a V |bRaw| (abs_nonneg _) _ _ (hpb z.1) ha.ne'
      (fun x y => (hq z.1 x y).le) z.2)
  have hDb (z) : |D z| ≤ Fintype.card J  * (Ba * |bRaw|^n) +
      η^2 * (|bRaw|^n * (n/a^2)) :=
    highHistoryLikelihoodDerivative_abs_le π dependent hsymm activation Ba hBa habound
      n a V η |bRaw| (abs_nonneg _) ha p F hpb (fun ω x y => (hq ω x y).le) z.1 z.2
  have he := posteriorMeanScore_memLp_energy ν μ L D
    (highRawSampleLikelihood_joint_measurable n a V p F hp hF)
    (highHistoryLikelihoodDerivative_measurable dependent hsymm π activation ham n a V η p F hp hF)
    hLp (|bRaw|^n) _ G (massPowerNormalizer_pos ν m (highRawDensityMass_joint_measurable p hp) n aRaw bRaw haRaw hb) hLb hDb hE
  have hden := highMassTilt_index_marginal_density ν n a V p F hp hF aRaw bRaw haRaw ha.ne'
    hraw (fun ω x y => (hq ω x y).le)
  let Pi := (highSampleIndexKernel n a V p F hp hF) ∘ₘ massPowerTilt ν m n
  have hpost : posteriorMeanScore ν L D = highMarginalIndexScore dependent hsymm ν π activation n a V η p F := rfl
  change MemLp (posteriorMeanScore ν L D) 2
      (μ.withDensity (fun z => ENNReal.ofReal ((∫ ω, L (ω,z) ∂ν) / G))) ∧ _ at he
  rw [hpost] at he
  change Pi = μ.withDensity (fun z => ENNReal.ofReal ((∫ ω, L (ω,z) ∂ν) / G)) at hden
  rw [← hden] at he
  have hmap : (highRealSampleKernel n a V p F hp hF) ∘ₘ massPowerTilt ν m n =
      Pi.map (encodeDesignResponse a) := by
    exact (Measure.map_comp _ _ (encodeDesignResponse_measurable a)).symm
  have hR := highMarginalRealScore_measurable dependent hsymm ν π activation ham n a V η p F hp hF
  have hcomp : (fun z => highMarginalRealScore dependent hsymm ν π activation n a V η p F
      (encodeDesignResponse a z)) = highMarginalIndexScore dependent hsymm ν π activation n a V η p F := by
    funext z
    exact congrArg (highMarginalIndexScore dependent hsymm ν π activation n a V η p F)
      (decodeDesignResponse_encode a ha z)
  dsimp only
  rw [hmap]
  constructor
  · apply (memLp_map_measure_iff hR.aestronglyMeasurable (encodeDesignResponse_measurable a).aemeasurable).2
    simpa only [Function.comp_def, hcomp] using he.1
  · rw [integral_map_of_stronglyMeasurable (encodeDesignResponse_measurable a) (hR.pow_const 2).stronglyMeasurable]
    have hpoint (z) : highMarginalRealScore dependent hsymm ν π activation n a V η p F
        (encodeDesignResponse a z) = highMarginalIndexScore dependent hsymm ν π activation n a V η p F z :=
      congrFun hcomp z
    simp_rw [hpoint]
    exact he.2
end
section
variable {J : Type*} [Fintype J] [LinearOrder J]
theorem historyMarkedPrior_dataScore_centered_ae (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (T Ba : ℝ) (hBa : 0 ≤ Ba)
     [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (activation : E → ℝ) (hactivation : Measurable activation)
    (hcenter : ∫ e, activation e ∂π = 0) (habound : ∀ e, |activation e| ≤ Ba)
    (hsmall : T * Ba / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
     (n : ℕ) (a v η aRaw bRaw : ℝ) (ha : 0 < a) (haRaw : 0 < aRaw)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ u ∈ Icc 0 T, ∀ ω x y, 0 < ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    (hmass : ∀ u ∈ Icc 0 T,
      (historyMarkedPrior dependent Δ u π activation).map (fun ω => highRawDensityMass (p ω)) =
      (historyMarkedPrior dependent Δ 0 π activation).map (fun ω => highRawDensityMass (p ω)))
    : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Icc 0 T →
      (∫ z, highMarginalRealScore dependent hsymm
        (historyMarkedPrior dependent Δ t π activation) π activation n a (v - η^2*t) η p F z
        ∂(highRealSampleKernel n a (v - η^2*t) p F hp hF) ∘ₘ
          (massPowerTilt (historyMarkedPrior dependent Δ t π activation)
            (fun ω => highRawDensityMass (p ω)) n)) = 0 := by
  have h0 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ ↑0 := by simp [ae_iff]
  have hT : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ T := by simp [ae_iff]
  filter_upwards [h0, hT] with t ht0 htT
  intro ht
  have h_historyMarkedPrior_dataScore_centered (ht : 0 < t) (htT : t < T) : (∫ z, highMarginalRealScore dependent hsymm
      (historyMarkedPrior dependent Δ t π activation) π activation n a (v - η^2*t) η p F z
      ∂(highRealSampleKernel n a (v - η^2*t) p F hp hF) ∘ₘ
        (massPowerTilt (historyMarkedPrior dependent Δ t π activation)
          (fun ω => highRawDensityMass (p ω)) n)) = 0 := by
    have hd := historyMarkedPrior_dataMean_score_hasDerivAt dependent hrefl hsymm Δ hΔ hlabels
      T Ba hBa π activation hactivation hcenter habound hsmall n a v η aRaw bRaw ha haRaw p F hp hF
      hraw hq hmass (fun _ => 1) measurable_const 1 (by norm_num) (fun _ => by norm_num) t ht htT
    have he : (fun u => ∫ z, (1 : ℝ) ∂(highRealSampleKernel n a (v - η^2*u) p F hp hF) ∘ₘ
        (massPowerTilt (historyMarkedPrior dependent Δ u π activation)
          (fun ω => highRawDensityMass (p ω)) n)) =ᶠ[𝓝 t] (fun _ => 1) := by
      filter_upwards [Ioo_mem_nhds ht htT] with u hu
      have hs  :=
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2.le hBa)
          (historyReferenceRho_pos Δ).le).trans hsmall
      let _ := historyMarkedPrior_probability dependent hrefl hsymm Δ hΔ hlabels u Ba hu.1.le hBa π
        activation (by apply Integrable.of_bound hactivation.aestronglyMeasurable Ba; exact Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using habound e) hcenter habound hs
      have hm := highRawDensityMass_joint_measurable p hp
      have hb (ω) : aRaw ≤ highRawDensityMass (p ω) ∧ highRawDensityMass (p ω) ≤ bRaw :=
        highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw
          (Eventually.of_forall (hraw ω))
      let _ := massPowerTilt_isProbability (historyMarkedPrior dependent Δ u π activation)
        _ hm n aRaw bRaw haRaw hb
      let _ := highRealSampleKernel_markov n a (v - η^2*u) p F hp hF aRaw bRaw haRaw hraw ha.ne'
        (fun ω x y => (hq u ⟨hu.1.le,hu.2.le⟩ ω x y).le)
      simp
    simpa only [one_mul] using hd.unique ((hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq he)
  exact h_historyMarkedPrior_dataScore_centered (lt_of_le_of_ne ht.1 (Ne.symm ht0)) (lt_of_le_of_ne ht.2 htT)
end
section
variable {J : Type*} [Fintype J] [LinearOrder J]
theorem highRawSampleLikelihood_time_measurable  [MeasurableSpace Ω] 
    (n a v η p F)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable (fun z : ℝ × (Ω × ((Fin n → Covariate d) × (Fin n → Fin 3))) =>
      highRawSampleLikelihood n a (v-η^2*z.1) (p z.2.1) (F z.2.1) z.2.2) := by
  apply measurable_uncurry_of_continuous_of_measurable
    (u := fun (t : ℝ) (z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3))) =>
      highRawSampleLikelihood n a (v-η^2*t) (p z.1) (F z.1) z.2)
  · intro z
    exact continuous_iff_continuousAt.mpr (fun t =>
      (highRawSampleLikelihood_hasDerivAt_path n a v η t (p z.1) (F z.1) z.2).continuousAt)
  · exact fun t => highRawSampleLikelihood_joint_measurable n a (v-η^2*t) p F hp hF
theorem ternaryMass_continuous_variance (a f y) :
    Continuous (fun V => ternaryMass a f V y) := by
  fin_cases y <;> simp only [ternaryMass]
  all_goals fun_prop
theorem highRawSampleVarianceDerivative_time_measurable  [MeasurableSpace Ω] 
    (n a v η p F)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable (fun z : ℝ × (Ω × ((Fin n → Covariate d) × (Fin n → Fin 3))) =>
      highRawSampleVarianceDerivative n a (v-η^2*z.1) (p z.2.1) (F z.2.1) z.2.2) := by
  apply measurable_uncurry_of_continuous_of_measurable
    (u := fun (t : ℝ) (z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3))) =>
      highRawSampleVarianceDerivative n a (v-η^2*t) (p z.1) (F z.1) z.2)
  · intro z
    apply Continuous.mul continuous_const
    apply continuous_finset_sum
    intro i _
    apply Continuous.mul _ continuous_const
    apply continuous_finset_prod
    intro j _
    exact (ternaryMass_continuous_variance a _ _).comp (by fun_prop)
  · exact fun t => highRawSampleVarianceDerivative_joint_measurable n a (v-η^2*t) p F hp hF
theorem highAppendLikelihoodAction_time_measurable  [MeasurableSpace E]
    [StandardBorelSpace E] 
    (dependent hsymm π) [SFinite π] (activation ) (ham : Measurable activation)
    (n a v η p F)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) (j : J) :
    Measurable (fun z : ℝ × (HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3))) =>
      highAppendLikelihoodAction dependent hsymm π activation n a (v-η^2*z.1) p F j z.2.1 z.2.2) := by
  have hc : Measurable (fun z :
      (ℝ × (HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)))) × E =>
      (z.1.1,(historyMarkedAppend dependent hsymm j (z.1.2.1,z.2),z.1.2.2))) :=
    (measurable_fst.comp measurable_fst).prodMk
      (((historyMarkedAppend_measurable dependent hsymm j).comp
        ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_fst)))
  have hj  :=
    (ham.comp measurable_snd).mul
      ((highRawSampleLikelihood_time_measurable n a v η p F hp hF).comp hc)
  exact hj.stronglyMeasurable.integral_prod_right'.measurable
theorem highHistoryLikelihoodDerivative_time_measurable  [MeasurableSpace E]
    [StandardBorelSpace E] 
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (π : Measure E) [SFinite π] (activation : E → ℝ) (ham : Measurable activation)
    (n : ℕ) (a v η : ℝ) (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable (fun z : ℝ × (HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3))) =>
      highHistoryLikelihoodDerivative dependent hsymm π activation n a (v-η^2*z.1) η p F z.2.1 z.2.2) := by
  exact (Finset.measurable_sum _ (fun j _ =>
    highAppendLikelihoodAction_time_measurable dependent hsymm π activation ham n a v η p F hp hF j)).sub
      ((highRawSampleVarianceDerivative_time_measurable n a v η p F hp hF).const_mul (η^2))
end
variable {J : Type*} [Fintype J] [LinearOrder J]
theorem historyMarkedPrior_integral_joint_measurable 
    [MeasurableSpace E] [MeasurableSpace Z]
    (dependent : J → J → Prop) (Δ : ℕ) (π : Measure E)
    [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation)
    (G : ℝ × (HistoryMarked dependent E × Z) → ℝ) (hG : Measurable G) :
    Measurable (fun z : ℝ × Z =>
      ∫ ω, G (z.1,(ω,z.2)) ∂historyMarkedPrior dependent Δ z.1 π activation) := by
  let f : (ℝ × Z) × HistoryMarked dependent E → ℝ := fun z =>
    (ENNReal.ofReal (historyMarkedDensity dependent (historyReferenceRho Δ) z.1.1 activation z.2)).toReal *
      G (z.1.1,(z.2,z.1.2))
  have h_historyMarkedDensity_joint_measurable : Measurable (fun z : ℝ × HistoryMarked dependent E =>
      historyMarkedDensity dependent (historyReferenceRho Δ) z.1 activation z.2) := by
    apply measurable_uncurry_of_continuous_of_measurable
      (u := fun (t : ℝ) (ω : HistoryMarked dependent E) => historyMarkedDensity dependent (historyReferenceRho Δ) t activation ω)
    · intro ω
      exact continuous_iff_continuousAt.mpr (fun t =>
        (historyMarkedDensity_hasDerivAt dependent (historyReferenceRho Δ) t activation ω).continuousAt)
    · exact fun t => historyMarkedDensity_measurable dependent (historyReferenceRho Δ) t activation ham
  have hm  :=
    ((h_historyMarkedDensity_joint_measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).ennreal_ofReal.ennreal_toReal).mul
      (hG.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  have he : (fun z : ℝ × Z => ∫ ω, G (z.1,(ω,z.2))
      ∂historyMarkedPrior dependent Δ z.1 π activation) =
      fun z => ∫ ω, f (z,ω) ∂historyMarkedReference dependent Δ π := by
    funext z
    rw [historyMarkedPrior_eq_withDensity dependent Δ z.1 π activation ham,
      integral_withDensity_eq_integral_toReal_smul
        (historyMarkedDensity_measurable dependent _ z.1 activation ham).ennreal_ofReal
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    rfl
  rw [he]
  exact hm.stronglyMeasurable.integral_prod_right'.measurable
theorem highMarginalRawLikelihood_time_measurable  [MeasurableSpace E] 
    (dependent : J → J → Prop) (Δ : ℕ) (π : Measure E)
    [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable (fun z : ℝ × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      highMarginalRawLikelihood (historyMarkedPrior dependent Δ z.1 π activation)
        n a (v-η^2*z.1) p F z.2) :=
  historyMarkedPrior_integral_joint_measurable dependent Δ π activation ham _
    (highRawSampleLikelihood_time_measurable n a v η p F hp hF)
theorem highMarginalIndexScore_time_measurable  [MeasurableSpace E]
    [StandardBorelSpace E] 
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (π : Measure E) [SFinite π] [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable (fun z : ℝ × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      highMarginalIndexScore dependent hsymm (historyMarkedPrior dependent Δ z.1 π activation)
        π activation n a (v-η^2*z.1) η p F z.2) :=
  (historyMarkedPrior_integral_joint_measurable dependent Δ π activation ham _
    (highHistoryLikelihoodDerivative_time_measurable dependent hsymm π activation ham n a v η p F hp hF)).div
    (highMarginalRawLikelihood_time_measurable dependent Δ π activation ham n a v η p F hp hF)
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] highMarginalIndexScore highMarginalRawLikelihood
  historyMarkedPrior highRawDensityMass massPowerNormalizer
theorem highMassPowerNormalizer_time_measurable  [MeasurableSpace E] 
    (dependent : J → J → Prop) (Δ : ℕ) (π : Measure E)
    [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ)
    (p : HistoryMarked dependent E → Covariate d → ℝ) (hp : Measurable (Function.uncurry p)) :
    Measurable (fun t => massPowerNormalizer (historyMarkedPrior dependent Δ t π activation)
      (fun ω => highRawDensityMass (p ω)) n) := by
  unfold massPowerNormalizer
  exact (historyMarkedPrior_integral_joint_measurable dependent Δ π activation ham _ (((highRawDensityMass_joint_measurable p hp).pow_const n).comp (measurable_fst.comp measurable_snd))).comp (show Measurable (fun t : ℝ => (t, ())) from
    measurable_id.prodMk measurable_const)
end NearlyMinimax
