module

public import NearlyMinimax.LowSmoothnessPrior

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace NearlyMinimax

set_option maxHeartbeats 800000

def encodeResponse {d n : ℕ} (a : ℝ) :
    (Fin n → Fin 3) × (Fin n → Covariate d) → (Fin n → Observation d) :=
  fun z i => (z.2 i, ternaryValue a (z.1 i))

theorem encodeResponse_measurable {d n : ℕ} (a : ℝ) :
    Measurable (encodeResponse (d := d) (n := n) a) :=
  Measurable.of_eval fun i =>
    ((measurable_pi_apply i).comp measurable_snd).prodMk
      ((measurable_of_countable _).comp ((measurable_pi_apply i).comp measurable_fst))

theorem parametric_minimax_lower {d : ℕ} (C : ModelConstants d) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ minimaxRMS C n := by
  obtain ⟨Q0⟩ := lowSmoothnessTernaryConstants_exists C
  have ha_pos := Q0.a_pos
  have hc_pos := Q0.c_pos
  let δ := min Q0.ρ (Q0.a ^ 2 * Real.sqrt Q0.c / 3)
  have hδ : 0 < δ := lt_min Q0.ρ_pos (by positivity)
  refine ⟨δ / 4, div_pos hδ (by norm_num), fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  let V₀ := Q0.v
  let V₁ := Q0.v + δ / Real.sqrt n
  have hsep : V₁ - V₀ = δ / Real.sqrt n := by dsimp [V₀, V₁]; ring
  have hsep_pos : 0 < V₁ - V₀ := hsep ▸ div_pos hδ (Real.sqrt_pos.2 hn0)
  have hsep_le : V₁ - V₀ ≤ δ := hsep ▸ div_le_self hδ.le (Real.one_le_sqrt.2 hn1)
  have hd0 : |V₀ - Q0.v| ≤ Q0.ρ := by simp [V₀, Q0.ρ_pos.le]
  have hd1 : |V₁ - Q0.v| ≤ Q0.ρ := by
    rw [show V₁ - Q0.v = V₁ - V₀ from rfl, abs_of_pos hsep_pos]
    exact hsep_le.trans (min_le_left _ _)
  have hleg0 := Q0.legal 0 V₀ (by simpa using Q0.ρ_pos.le) hd0
  have hleg1 := Q0.legal 0 V₁ (by simpa using Q0.ρ_pos.le) hd1
  have hp₀ : ∀ y, 0 ≤ ternaryMass Q0.a 0 V₀ y := fun y => hc_pos.le.trans (hleg0.2.2.1 y)
  have hp₁ : ∀ y, 0 ≤ ternaryMass Q0.a 0 V₁ y := fun y => hc_pos.le.trans (hleg1.2.2.1 y)
  have hadm (V : ℝ) (hdV : |V - Q0.v| ≤ Q0.ρ) (hnn : ∀ y, 0 ≤ ternaryMass Q0.a 0 V y) :
      Admissible C (uniformZeroParameter d Q0.a V ha_pos.ne' hnn) := by
    have hl := Q0.legal 0 V (by simpa using Q0.ρ_pos.le) hdV
    refine ⟨measurable_const, measurable_const,
      Filter.Eventually.of_forall fun _ => ⟨C.densityLower_lt_one.le, C.one_lt_densityUpper.le⟩,
      by simp [uniformZeroParameter, cubeVolume_univ],
      ⟨fun _ => 0, fun _ _ => rfl, contDiffOn_const, by simp [holderNorm_zero]⟩,
      hl.1.le, hl.2.1.le, Filter.Eventually.of_forall fun _ => ?_⟩
    simp only [uniformZeroParameter, Kernel.const_apply]
    refine ⟨ternaryMeasure_integrable .., ternaryMeasure_integrable .., ternaryMeasure_integrable ..,
      ternaryMeasure_mean Q0.a 0 V ha_pos.ne' hnn,
      by simpa using ternaryMeasure_variance Q0.a 0 V ha_pos.ne' hnn, ?_⟩
    rw [ternaryMeasure_integral Q0.a 0 V hnn]
    simpa using hl.2.2.2
  let idxMeasure (V : ℝ) : Measure (Fin 3) :=
    ∑ y : Fin 3, ENNReal.ofReal (ternaryMass Q0.a 0 V y) • Measure.dirac y
  have hidxProb (V : ℝ) (hnn : ∀ y, 0 ≤ ternaryMass Q0.a 0 V y) : IsProbabilityMeasure (idxMeasure V) := ⟨by
    simp only [idxMeasure, Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg fun y _ => hnn y, ternary_normalized Q0.a 0 V ha_pos.ne', ENNReal.ofReal_one]⟩
  let _ := cubeVolume_isProbability d
  let ν := Measure.pi fun _ : Fin n => cubeVolume d
  have hmp (V : ℝ) (hnn : ∀ y, 0 ≤ ternaryMass Q0.a 0 V y) :
      MeasurePreserving (encodeResponse (d := d) (n := n) Q0.a)
        ((Measure.pi fun _ : Fin n => idxMeasure V).prod ν)
        (sampleLaw (uniformZeroParameter d Q0.a V ha_pos.ne' hnn) n) := by
    let _ := hidxProb V hnn
    let _ := ternaryMeasure_isProbability Q0.a 0 V ha_pos.ne' hnn
    let _ : IsProbabilityMeasure (observationLaw (uniformZeroParameter d Q0.a V ha_pos.ne' hnn)) := by
      rw [uniformZeroParameter_observationLaw]; infer_instance
    have hmap : (idxMeasure V).map (ternaryValue Q0.a) = ternaryMeasure Q0.a 0 V := by
      ext s hs
      simp only [idxMeasure, ternaryMeasure, Measure.map_apply (measurable_of_countable _) hs, Measure.finsetSum_apply]
      exact Finset.sum_congr rfl fun x _ => by by_cases hx : ternaryValue Q0.a x ∈ s <;> simp [hx]
    have h1 : MeasurePreserving (fun z : Fin 3 × Covariate d => (z.2, ternaryValue Q0.a z.1))
        ((idxMeasure V).prod (cubeVolume d)) (observationLaw (uniformZeroParameter d Q0.a V ha_pos.ne' hnn)) := by
      refine ⟨measurable_snd.prodMk ((measurable_of_countable _).comp measurable_fst), ?_⟩
      rw [uniformZeroParameter_observationLaw]
      have hm := Measure.map_prod_map (idxMeasure V) (cubeVolume d) (measurable_of_countable (ternaryValue Q0.a)) measurable_id
      rw [hmap, Measure.map_id] at hm
      calc
        _ = (((idxMeasure V).prod (cubeVolume d)).map (Prod.map (ternaryValue Q0.a) id)).map Prod.swap := by
          rw [Measure.map_map measurable_swap ((measurable_of_countable _).prodMap measurable_id)]; rfl
        _ = _ := by rw [← hm, Measure.prod_swap]
    exact (measurePreserving_pi _ _ fun _ : Fin n => h1).comp
      ((measurePreserving_arrowProdEquivProdArrow (Fin 3) (Covariate d) (Fin n)
        (fun _ => idxMeasure V) (fun _ => cubeVolume d)).symm _)
  let p₀ := ternaryMass Q0.a 0 V₀
  let p₁ := ternaryMass Q0.a 0 V₁
  let Q (p : Fin 3 → ℝ) (ys : Fin n → Fin 3) : ℝ := ∏ i, p (ys i)
  have hQnn (p : Fin 3 → ℝ) (hpp : ∀ y, 0 ≤ p y) (ys : Fin n → Fin 3) : 0 ≤ Q p ys :=
    Finset.prod_nonneg fun i _ => hpp (ys i)
  have hQsum (p : Fin 3 → ℝ) (hs : ∑ y, p y = 1) : ∑ ys, Q p ys = 1 := by
    simpa [Q, hs] using (Fintype.prod_sum fun _ : Fin n => p).symm
  have hH1 : ∑ y : Fin 3, (Real.sqrt (p₀ y) - Real.sqrt (p₁ y)) ^ 2 ≤
      3 * (V₁ - V₀) ^ 2 / (8 * Q0.a ^ 4 * Q0.c) := by
    have hterm (y : Fin 3) : (Real.sqrt (p₀ y) - Real.sqrt (p₁ y)) ^ 2 ≤ (p₁ y - p₀ y) ^ 2 / (4 * Q0.c) := by
      have hs0 : Real.sqrt Q0.c ≤ Real.sqrt (p₀ y) := Real.sqrt_le_sqrt (hleg0.2.2.1 y)
      have hs1 : Real.sqrt Q0.c ≤ Real.sqrt (p₁ y) := Real.sqrt_le_sqrt (hleg1.2.2.1 y)
      have hden : 4 * Q0.c ≤ (Real.sqrt (p₀ y) + Real.sqrt (p₁ y)) ^ 2 := by
        nlinarith [Real.sq_sqrt hc_pos.le, Real.sqrt_nonneg Q0.c]
      have hid : (Real.sqrt (p₀ y) - Real.sqrt (p₁ y)) * (Real.sqrt (p₀ y) + Real.sqrt (p₁ y)) = p₀ y - p₁ y := by
        nlinarith [Real.sq_sqrt (hp₀ y), Real.sq_sqrt (hp₁ y)]
      rw [le_div_iff₀ (by positivity)]
      calc
        (Real.sqrt (p₀ y) - Real.sqrt (p₁ y)) ^ 2 * (4 * Q0.c)
          ≤ (Real.sqrt (p₀ y) - Real.sqrt (p₁ y)) ^ 2 * (Real.sqrt (p₀ y) + Real.sqrt (p₁ y)) ^ 2 :=
            mul_le_mul_of_nonneg_left hden (sq_nonneg _)
        _ = (p₁ y - p₀ y) ^ 2 := by rw [← mul_pow, hid]; ring
    refine (Finset.sum_le_sum fun y _ => hterm y).trans_eq ?_
    rw [← Finset.sum_div, Fin.sum_univ_three]
    have ha0 : Q0.a ≠ 0 := ha_pos.ne'
    have hc0 : Q0.c ≠ 0 := hc_pos.ne'
    simp [p₀, p₁, ternaryMass]
    field_simp
    ring
  let A := ∑ y : Fin 3, Real.sqrt (p₀ y * p₁ y)
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun y _ => Real.sqrt_nonneg _
  have hAeq : ∑ y : Fin 3, (Real.sqrt (p₀ y) - Real.sqrt (p₁ y)) ^ 2 = 2 - 2 * A := by
    have hpt (y : Fin 3) : (Real.sqrt (p₀ y) - Real.sqrt (p₁ y)) ^ 2 = p₀ y + p₁ y - 2 * Real.sqrt (p₀ y * p₁ y) := by
      rw [Real.sqrt_mul (hp₀ y)]; nlinarith [Real.sq_sqrt (hp₀ y), Real.sq_sqrt (hp₁ y)]
    simp_rw [hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [ternary_normalized Q0.a 0 V₀ ha_pos.ne', ternary_normalized Q0.a 0 V₁ ha_pos.ne',
      show ∑ y, Real.sqrt (p₀ y * p₁ y) = A from rfl]; ring
  have hHn : 2 - 2 * A ^ n ≤ 1 / 4 := by
    have hpow := one_add_mul_sub_le_pow (by linarith : -1 ≤ A) n
    have hδbound : δ ≤ Q0.a ^ 2 * Real.sqrt Q0.c / 3 := min_le_right _ _
    have hδsq : δ ^ 2 ≤ Q0.a ^ 4 * Q0.c / 9 := by
      have h1 := (sq_le_sq₀ hδ.le (by positivity)).mpr hδbound
      rw [div_pow, mul_pow, Real.sq_sqrt hc_pos.le] at h1
      linarith
    have hnH : (n : ℝ) * (2 - 2 * A) ≤ 1 / 4 := by
      refine (mul_le_mul_of_nonneg_left (hAeq ▸ hH1) hn0.le).trans ?_
      rw [hsep, div_pow, Real.sq_sqrt hn0.le]
      have ha4c : 0 < 8 * Q0.a ^ 4 * Q0.c := by positivity
      rw [mul_div_assoc', div_le_iff₀ ha4c]
      have hne : (n : ℝ) * (3 * (δ ^ 2 / n)) = 3 * δ ^ 2 := by field_simp
      linarith
    nlinarith
  have hAn : ∑ ys : Fin n → Fin 3, Real.sqrt (Q p₀ ys * Q p₁ ys) = A ^ n := by
    have hpt (ys : Fin n → Fin 3) : Real.sqrt (Q p₀ ys * Q p₁ ys) = ∏ i, Real.sqrt (p₀ (ys i) * p₁ (ys i)) := by
      dsimp [Q]; rw [← Finset.prod_mul_distrib, Real.sqrt_prod _ fun i _ => mul_nonneg (hp₀ _) (hp₁ _)]
    simp_rw [hpt]
    simpa [A] using (Fintype.prod_sum fun _ : Fin n => fun y => Real.sqrt (p₀ y * p₁ y)).symm
  have hfin (g : (Fin n → Fin 3) → ℝ) :
      (V₁ - V₀) ^ 2 / 4 ≤ ∑ ys, Q p₀ ys * (g ys - V₀) ^ 2 + ∑ ys, Q p₁ ys * (g ys - V₁) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    have hmin_sum : (1 / 2 : ℝ) ≤ ∑ ys, min (Q p₀ ys) (Q p₁ ys) := by
      have hpt (ys : Fin n → Fin 3) :
          3 * (Q p₀ ys + Q p₁ ys) / 8 - (Q p₀ ys + Q p₁ ys - 2 * Real.sqrt (Q p₀ ys * Q p₁ ys)) ≤
            min (Q p₀ ys) (Q p₁ ys) := by
        have hu := hQnn p₀ hp₀ ys; have hv := hQnn p₁ hp₁ ys
        rw [Real.sqrt_mul hu]
        exact le_min
          (by nlinarith [Real.sq_sqrt hu, Real.sq_sqrt hv, sq_nonneg (8 * Real.sqrt (Q p₀ ys) - 5 * Real.sqrt (Q p₁ ys))])
          (by nlinarith [Real.sq_sqrt hu, Real.sq_sqrt hv, sq_nonneg (5 * Real.sqrt (Q p₀ ys) - 8 * Real.sqrt (Q p₁ ys))])
      have hs := Finset.sum_le_sum fun ys (_ : ys ∈ Finset.univ) => hpt ys
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib,
        hQsum p₀ (ternary_normalized Q0.a 0 V₀ ha_pos.ne'),
        hQsum p₁ (ternary_normalized Q0.a 0 V₁ ha_pos.ne'), hAn] at hs
      linarith
    calc
      (V₁ - V₀) ^ 2 / 4 = (1 / 2) * ((V₁ - V₀) ^ 2 / 2) := by ring
      _ ≤ (∑ ys, min (Q p₀ ys) (Q p₁ ys)) * ((V₁ - V₀) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right hmin_sum (by positivity)
      _ = ∑ ys, min (Q p₀ ys) (Q p₁ ys) * ((V₁ - V₀) ^ 2 / 2) := Finset.sum_mul _ _ _
      _ ≤ _ := Finset.sum_le_sum fun ys _ => by
            have hw0 : 0 ≤ min (Q p₀ ys) (Q p₁ ys) := le_min (hQnn p₀ hp₀ ys) (hQnn p₁ hp₁ ys)
            have hw1 := min_le_left (Q p₀ ys) (Q p₁ ys)
            have hw2 := min_le_right (Q p₀ ys) (Q p₁ ys)
            have hg2 : (V₁ - V₀) ^ 2 / 2 ≤ (g ys - V₀) ^ 2 + (g ys - V₁) ^ 2 := by
              nlinarith [sq_nonneg (2 * g ys - V₀ - V₁)]
            nlinarith [mul_le_mul_of_nonneg_right hw1 (sq_nonneg (g ys - V₀)),
              mul_le_mul_of_nonneg_right hw2 (sq_nonneg (g ys - V₁)),
              mul_le_mul_of_nonneg_left hg2 hw0]
  suffices hmr : ENNReal.ofReal ((V₁ - V₀) ^ 2 / 8) ≤ minimaxRisk C n by
    have hscale : δ / 4 * (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (V₁ - V₀) / (2 * Real.sqrt 2) := by
      have hinv : (n : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (n : ℝ))⁻¹ := by
        rw [Real.rpow_neg hn0.le, ← Real.sqrt_eq_rpow]
      rw [hsep, hinv]
      have h2 : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
      calc
        δ / 4 * (Real.sqrt (n : ℝ))⁻¹ = (δ * (Real.sqrt (n : ℝ))⁻¹ / 2) / 2 := by ring
        _ ≤ (δ * (Real.sqrt (n : ℝ))⁻¹ / 2) / Real.sqrt 2 :=
            div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.2 (by norm_num)) h2
        _ = (δ / Real.sqrt (n : ℝ)) / (2 * Real.sqrt 2) := by ring
    refine (ENNReal.ofReal_le_ofReal hscale).trans ?_
    unfold minimaxRMS
    refine le_trans ?_ (ENNReal.rpow_le_rpow hmr (by norm_num))
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
      Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hsep_pos.le]
    have : Real.sqrt 8 = 2 * Real.sqrt 2 := by
      rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    rw [this]
  refine le_iInf fun T => ?_
  have hpiSing (V : ℝ) (hnn : ∀ y, 0 ≤ ternaryMass Q0.a 0 V y) (ys : Fin n → Fin 3) :
      (Measure.pi fun _ : Fin n => idxMeasure V) {ys} = ENNReal.ofReal (Q (ternaryMass Q0.a 0 V) ys) := by
    let _ := hidxProb V hnn
    have hset : ({ys} : Set (Fin n → Fin 3)) = Set.univ.pi fun i => {ys i} := by
      ext z; simp [funext_iff]
    dsimp [Q]
    rw [hset, Measure.pi_pi, ENNReal.ofReal_prod_of_nonneg fun i _ => hnn (ys i)]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [idxMeasure, Measure.finsetSum_apply, Measure.smul_apply, Pi.single_apply]
  let S (V : ℝ) (x : Fin n → Covariate d) : ℝ :=
    ∑ ys, Q (ternaryMass Q0.a 0 V) ys * (T.val (encodeResponse Q0.a (ys, x)) - V) ^ 2
  have hS_meas (V : ℝ) : Measurable (S V) :=
    Finset.measurable_sum _ fun ys _ =>
      (((T.property.comp ((encodeResponse_measurable Q0.a).comp
        (measurable_const.prodMk measurable_id))).sub measurable_const).pow_const 2).const_mul _
  have hS_nn (V : ℝ) (hnn : ∀ y, 0 ≤ ternaryMass Q0.a 0 V y) (x : Fin n → Covariate d) : 0 ≤ S V x :=
    Finset.sum_nonneg fun ys _ => mul_nonneg (hQnn _ hnn ys) (sq_nonneg _)
  have hR_eq (V : ℝ) (hdV : |V - Q0.v| ≤ Q0.ρ) (hnn : ∀ y, 0 ≤ ternaryMass Q0.a 0 V y) :
      (∫⁻ x, ENNReal.ofReal (S V x) ∂ν) ≤ worstCaseRisk C T := by
    let θ := uniformZeroParameter d Q0.a V ha_pos.ne' hnn
    let _ := hidxProb V hnn
    refine le_trans ?_ (meanSquaredRisk_le_worstCaseRisk C T θ (hadm V hdV hnn))
    have hm_loss : Measurable fun z : Fin n → Observation d => ENNReal.ofReal ((T.val z - V) ^ 2) :=
      ENNReal.measurable_ofReal.comp ((T.property.sub measurable_const).pow_const 2)
    have hθV : θ.variance = V := rfl
    rw [meanSquaredRisk, hθV, ← (hmp V hnn).lintegral_comp hm_loss,
      lintegral_prod_symm (fun a => ENNReal.ofReal ((T.val (encodeResponse Q0.a a) - V) ^ 2))
        (hm_loss.comp (encodeResponse_measurable Q0.a)).aemeasurable]
    refine le_of_eq (lintegral_congr fun x => ?_)
    rw [lintegral_fintype, ENNReal.ofReal_sum_of_nonneg fun ys _ => mul_nonneg (hQnn _ hnn ys) (sq_nonneg _)]
    exact Finset.sum_congr rfl fun ys _ => by
      rw [hpiSing V hnn ys, ← ENNReal.ofReal_mul (sq_nonneg _), mul_comm]
  have h2 : 2 * ENNReal.ofReal ((V₁ - V₀) ^ 2 / 8) ≤ 2 * worstCaseRisk C T := by
    have htwo : 2 * ENNReal.ofReal ((V₁ - V₀) ^ 2 / 8) = ENNReal.ofReal ((V₁ - V₀) ^ 2 / 4) := by
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
    rw [htwo, two_mul]
    let _ : IsProbabilityMeasure ν := inferInstance
    calc
      ENNReal.ofReal ((V₁ - V₀) ^ 2 / 4)
        = ∫⁻ _x, ENNReal.ofReal ((V₁ - V₀) ^ 2 / 4) ∂ν := by simp
      _ ≤ ∫⁻ x, ENNReal.ofReal (S V₀ x + S V₁ x) ∂ν :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hfin fun ys => T.val (encodeResponse Q0.a (ys, x)))
      _ = (∫⁻ x, ENNReal.ofReal (S V₀ x) ∂ν) + (∫⁻ x, ENNReal.ofReal (S V₁ x) ∂ν) := by
          simp_rw [ENNReal.ofReal_add (hS_nn V₀ hp₀ _) (hS_nn V₁ hp₁ _)]
          exact lintegral_add_left (ENNReal.measurable_ofReal.comp (hS_meas V₀)) _
      _ ≤ worstCaseRisk C T + worstCaseRisk C T := add_le_add (hR_eq V₀ hd0 hp₀) (hR_eq V₁ hd1 hp₁)
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h2

end NearlyMinimax
