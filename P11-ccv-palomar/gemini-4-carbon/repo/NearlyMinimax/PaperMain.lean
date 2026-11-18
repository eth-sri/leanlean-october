module

public import NearlyMinimax.BoundedPairMeanOperators
public import NearlyMinimax.CellPolynomialProjection
public import NearlyMinimax.LowMixtureLaw
public import NearlyMinimax.PaperCorollaries
public import NearlyMinimax.PaperGoals
public import NearlyMinimax.PaperLowerSharp
public import NearlyMinimax.PaperSharpUpper
public import NearlyMinimax.ParametricLower
public import NearlyMinimax.Projection
public import NearlyMinimax.Rates
public import NearlyMinimax.Risk

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped BigOperators ENNReal Topology

namespace NearlyMinimax

-- ============================================================================
-- 1. Low-Smoothness Grid Allocation & Elementary Pair Upper Bound
-- ============================================================================

section LowSmoothnessGridAndUpper
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def lowSmoothnessGridExponent (d : ℕ) (s : ℝ) : ℝ := 2 / ((d : ℝ) + 4 * s)

def lowSmoothnessGrid (d : ℕ) (s x : ℝ) : ℕ := Nat.ceil (4 * x ^ lowSmoothnessGridExponent d s)

def lowSmoothnessAmplitude (d : ℕ) (s b x : ℝ) : ℝ := b / (lowSmoothnessGrid d s x : ℝ) ^ s

private lemma lowSmoothnessGrid_rounding {d : ℕ} {s x : ℝ} (hs : 0 < s) (hx : 1 ≤ x) :
    4 * x ^ lowSmoothnessGridExponent d s ≤ (lowSmoothnessGrid d s x : ℝ) ∧
      (lowSmoothnessGrid d s x : ℝ) ≤ 5 * x ^ lowSmoothnessGridExponent d s := by
  have hpos : 0 < lowSmoothnessGridExponent d s := by unfold lowSmoothnessGridExponent; positivity
  have hbase : 1 ≤ x ^ lowSmoothnessGridExponent d s := Real.one_le_rpow hx hpos.le
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 4 * x ^ lowSmoothnessGridExponent d s by positivity)
  exact ⟨Nat.le_ceil _, by change (lowSmoothnessGrid d s x : ℝ) < _ at hc; linarith⟩

private lemma lowSmoothnessGrid_ge_four {d : ℕ} {s x : ℝ} (hs : 0 < s) (hx : 1 ≤ x) :
    4 ≤ lowSmoothnessGrid d s x := by
  have hpos : 0 < lowSmoothnessGridExponent d s := by unfold lowSmoothnessGridExponent; positivity
  have hbase : 1 ≤ x ^ lowSmoothnessGridExponent d s := Real.one_le_rpow hx hpos.le
  have hh := (lowSmoothnessGrid_rounding (d := d) hs hx).1
  exact_mod_cast (show (4 : ℝ) ≤ (lowSmoothnessGrid d s x : ℝ) by linarith)

private lemma lowSmoothnessGrid_positive {d : ℕ} {s x : ℝ} (hs : 0 < s) (hx : 1 ≤ x) :
    0 < (lowSmoothnessGrid d s x : ℝ) := by
  have := lowSmoothnessGrid_ge_four (d := d) hs hx; exact_mod_cast (by omega : 0 < lowSmoothnessGrid d s x)

private lemma lowSmoothness_design_occupancy {d : ℕ} {s x : ℝ}
    (hs : 0 < s) (hd : 4 * s ≤ (d : ℝ)) (hx : 1 ≤ x) :
    x * (2 / (lowSmoothnessGrid d s x : ℝ)) ^ d ≤ 1 := by
  have hx0 : 0 < x := by linarith
  have hk := lowSmoothnessGrid_positive (d := d) hs hx
  have hden : 0 < (d : ℝ) + 4 * s := by positivity
  have hpd : 1 ≤ lowSmoothnessGridExponent d s * d := by
    unfold lowSmoothnessGridExponent; rw [div_mul_eq_mul_div]; exact (le_div_iff₀ hden).2 (by linarith)
  have hxp : x ≤ x ^ (lowSmoothnessGridExponent d s * d) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx hpd
  have hgrid := pow_le_pow_left₀ (by positivity) (lowSmoothnessGrid_rounding (d := d) hs hx).1 d
  rw [mul_pow, ← Real.rpow_mul_natCast hx0.le] at hgrid
  have hpow : (2 : ℝ) ^ d ≤ (4 : ℝ) ^ d := by gcongr; norm_num
  have hbudget : x * (2 : ℝ) ^ d ≤ (lowSmoothnessGrid d s x : ℝ) ^ d := by
    calc
      _ ≤ x * (4 : ℝ) ^ d := mul_le_mul_of_nonneg_left hpow hx0.le
      _ ≤ (4 : ℝ) ^ d * x ^ (lowSmoothnessGridExponent d s * d) := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hxp (by positivity : 0 ≤ (4 : ℝ) ^ d)
      _ ≤ _ := hgrid
  rw [div_pow, ← mul_div_assoc]
  exact (div_le_iff₀ (pow_pos hk d)).2 (by simpa only [one_mul] using hbudget)

private lemma lowSmoothness_numeric_score_budget {d : ℕ} {s b x : ℝ}
    (hs : 0 < s) (hx : 1 ≤ x) :
    x ^ 2 * (lowSmoothnessAmplitude d s b x) ^ 4 / (lowSmoothnessGrid d s x : ℝ) ^ d ≤ b ^ 4 := by
  have hx0 : 0 < x := by linarith
  have hk := lowSmoothnessGrid_positive (d := d) hs hx
  have hden : 0 < (d : ℝ) + 4 * s := by positivity
  have hbase : x ^ lowSmoothnessGridExponent d s ≤ (lowSmoothnessGrid d s x : ℝ) := by
    have hh := (lowSmoothnessGrid_rounding (d := d) hs hx).1
    have hp := (Real.rpow_pos_of_pos hx0 (lowSmoothnessGridExponent d s)).le; linarith
  have hh := Real.rpow_le_rpow (Real.rpow_pos_of_pos hx0 _).le hbase hden.le
  rw [← Real.rpow_mul hx0.le, show lowSmoothnessGridExponent d s * ((d : ℝ) + 4 * s) = 2 from
    div_mul_cancel₀ _ hden.ne', Real.rpow_two] at hh
  have hp4 : ((lowSmoothnessGrid d s x : ℝ) ^ s) ^ (4 : ℕ) = (lowSmoothnessGrid d s x : ℝ) ^ (4 * s) := by
    rw [← Real.rpow_mul_natCast hk.le]; congr 1; ring
  rw [show x ^ 2 * (lowSmoothnessAmplitude d s b x) ^ 4 / (lowSmoothnessGrid d s x : ℝ) ^ d =
      b ^ 4 * (x ^ 2 / (lowSmoothnessGrid d s x : ℝ) ^ ((d : ℝ) + 4 * s)) by
    unfold lowSmoothnessAmplitude; rw [div_pow, hp4, Real.rpow_add hk, Real.rpow_natCast]; field_simp]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left ((div_le_one (Real.rpow_pos_of_pos hk _)).2 hh)
    (by positivity : 0 ≤ b ^ (4 : ℕ))

private lemma lowSmoothness_variance_separation {d : ℕ} {s b x : ℝ} (hs : 0 < s) (hx : 1 ≤ x) :
    b ^ 2 / (5 : ℝ) ^ (2 * s) * x ^ (-4 * s / ((d : ℝ) + 4 * s)) ≤ (lowSmoothnessAmplitude d s b x) ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hk := lowSmoothnessGrid_positive (d := d) hs hx
  have hupper := Real.rpow_le_rpow hk.le (lowSmoothnessGrid_rounding (d := d) hs hx).2 (by positivity : 0 ≤ 2 * s)
  rw [Real.mul_rpow (by norm_num) (Real.rpow_pos_of_pos hx0 _).le, ← Real.rpow_mul hx0.le,
    show lowSmoothnessGridExponent d s * (2 * s) = 4 * s / ((d : ℝ) + 4 * s) by unfold lowSmoothnessGridExponent; ring] at hupper
  have hh := div_le_div_of_nonneg_left (sq_nonneg b) (Real.rpow_pos_of_pos hk _) hupper
  rw [show (lowSmoothnessAmplitude d s b x) ^ 2 = b ^ 2 / (lowSmoothnessGrid d s x : ℝ) ^ (2 * s) by
    unfold lowSmoothnessAmplitude; rw [div_pow, ← Real.rpow_mul_natCast hk.le]; congr 2; ring]
  refine le_trans (le_of_eq ?_) hh
  rw [show -4 * s / ((d : ℝ) + 4 * s) = -(4 * s / ((d : ℝ) + 4 * s)) by ring, Real.rpow_neg hx0.le]; ring

private lemma elementary_upper_low_smoothness {d : ℕ} (C : ModelConstants d) (hs : C.smoothness ≤ 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 1 ≤ n →
      minimaxRMS C n ≤ ENNReal.ofReal (B * max ((n : ℝ) ^ (-(1 / 2 : ℝ)))
        ((n : ℝ) ^ (-4 * C.smoothness / ((d : ℝ) + 4 * C.smoothness)))) := by
  have hs_eq : elementarySmoothness C = C.smoothness := min_eq_left hs
  have hU : 0 < C.densityUpper := zero_lt_one.trans C.one_lt_densityUpper
  let rowB : ℝ := responseFourthBound C + (C.varianceUpper + responseSecondBound C) ^ 2
  let kerB : ℝ := 8 * responseFourthBound C + 2 * C.varianceUpper ^ 2
  let biasF : ℝ := (2 * ((d : ℝ) + 1) * C.holderBound) ^ 4 * (Real.sqrt d) ^ (4 * C.smoothness)
  let K_mse : ℝ := (64 * C.densityUpper ^ 2 * rowB + 32 * C.densityUpper ^ 2 * C.varianceUpper ^ 2) +
    16 * C.densityUpper * (kerB + C.varianceUpper ^ 2) + 2 * C.densityUpper ^ 2 * biasF
  have hrowB : 0 < rowB := add_pos_of_pos_of_nonneg (responseFourthBound_pos C) (sq_nonneg _)
  have hkerB : 0 < kerB := by have := responseFourthBound_pos C; positivity
  have hbiasF : 0 ≤ biasF := by positivity
  have hK_mse : 0 < K_mse := by positivity
  let B_rms : ℝ := 2 * Real.sqrt (K_mse * (2 * (5 : ℝ) ^ d + 1)) + (C.varianceUpper - C.varianceLower)
  have hdiam : 0 < C.varianceUpper - C.varianceLower := sub_pos.mpr C.variance_interval
  refine ⟨B_rms, by positivity, fun n hn => ?_⟩
  by_cases hn2 : 2 ≤ n
  · have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hn1 : (1 : ℝ) ≤ n := by linarith
    have hn0 : (0 : ℝ) < n := by linarith
    have hn_sub : (0 : ℝ) < (n - 1 : ℕ) := by exact_mod_cast (by omega : 0 < n - 1)
    let k := lowSmoothnessGrid d C.smoothness n
    have hk : 0 < k := by have := lowSmoothnessGrid_ge_four (d := d) C.smoothness_pos hn1; omega
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    let numK : Observation d × Observation d → ℝ := pairWindowScore (regularObservationLabel k hk) Prod.snd 0
    let denK : Observation d × Observation d → ℝ := sameLabelKernel (regularObservationLabel k hk)
    let num := PairUStatistic.pairAverage n numK
    let den := PairUStatistic.pairAverage n denK
    let flr : ℝ := 1 / (2 * (k : ℝ) ^ d)
    have hmN : Measurable num := PairUStatistic.pairAverage_measurable n
      (pairWindowScore_measurable _ (regularObservationLabel_measurable k hk) Prod.snd measurable_snd 0)
    have hmD : Measurable den := PairUStatistic.pairAverage_measurable n
      (sameLabelKernel_measurable _ (regularObservationLabel_measurable k hk))
    let est : Estimator d n := ⟨stabilizedRatio C.varianceLower C.varianceUpper flr num den,
      stabilizedRatio_measurable _ _ _ hmN hmD⟩
    let env : ℝ := 1 / (n : ℝ) + (k : ℝ) ^ d / ((n : ℝ) * (n - 1 : ℕ)) + (k : ℝ) ^ (-4 * C.smoothness)
    have hwcr : worstCaseRisk C est ≤ ENNReal.ofReal (K_mse * env) := iSup_le fun ⟨θ, hθ⟩ => by
      let _ := observationLaw_isProbability C θ hθ
      let _ := sampleLaw_isProbability C θ hθ n
      have hi := iIndepFun_pi (μ := fun _ : Fin n => observationLaw θ) (X := fun _ => id) fun _ => aemeasurable_id
      have hp := fun i => measurePreserving_eval (fun _ : Fin n => observationLaw θ) i
      have hT := (stabilizedRatio_error_memLp (sampleLaw θ n) (a := flr) hmN hmD hθ.2.2.2.2.2.1 hθ.2.2.2.2.2.2.1).integrable_sq
      change Integrable (fun z => (est.val z - θ.variance) ^ 2) (sampleLaw θ n) at hT
      rw [meanSquaredRisk, ← ofReal_integral_eq_lintegral_ofReal hT (Eventually.of_forall fun _ => sq_nonneg _)]
      refine ENNReal.ofReal_mono ?_
      have hscore_id (z : Fin n → Observation d) :
          num z - θ.variance * den z = PairUStatistic.pairAverage n (regularPairScore θ k hk) z := by
        rw [show regularPairScore θ k hk = fun w => numK w - θ.variance * denK w from
          funext fun _ => by unfold regularPairScore numK denK pairWindowScore sameLabelKernel; split_ifs <;> ring]
        unfold num den PairUStatistic.pairAverage; simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; ring
      have hS2 : MemLp (fun z => num z - θ.variance * den z) 2 (sampleLaw θ n) := by
        simp_rw [hscore_id]
        exact PairUStatistic.pairAverage_memLp_two (fun i (z : Fin n → Observation d) => z i) hi hp (regularPairScore_memLp C θ hθ k hk)
      have hD2 : MemLp den 2 (sampleLaw θ n) :=
        PairUStatistic.pairAverage_memLp_two (fun i (z : Fin n → Observation d) => z i) hi hp
          (sameLabelKernel_memLp (observationLaw θ) _ (regularObservationLabel_measurable k hk))
      have hED : 2 * flr ≤ regularGridCollisionMass θ k hk := by
        convert regularGridCollisionMass_lower C θ hθ k hk using 1; dsimp [flr]; field_simp
      have hV0 : 0 ≤ θ.variance := C.varianceLower_pos.le.trans hθ.2.2.2.2.2.1
      have hVU : θ.variance ≤ C.varianceUpper := hθ.2.2.2.2.2.2.1
      have hM := stabilized_ratio_mse_le (sampleLaw θ n) hmN hmD hS2 hD2 (by positivity) hθ.2.2.2.2.2.1 hVU hV0 hED
      have hD_fluc : (∫ z, (den z - regularGridCollisionMass θ k hk) ^ 2 ∂sampleLaw θ n) ≤
          4 / (n : ℝ) * (C.densityUpper / (k : ℝ) ^ d) ^ 2 +
          2 / ((n : ℝ) * (n - 1 : ℕ)) * (C.densityUpper / (k : ℝ) ^ d) := by
        have he := PairUStatistic.pairAverage_centered_sq_le hn2 (fun i (z : Fin n → Observation d) => z i) hi hp
          (sameLabelKernel_measurable _ (regularObservationLabel_measurable k hk))
          (sameLabelKernel_memLp (observationLaw θ) _ (regularObservationLabel_measurable k hk))
          fun x y => (sameLabelKernel_symmetric _ (regularObservationLabel_measurable k hk) (x, y)).symm
        change (∫ z, (den z - ∫ p, denK p ∂(observationLaw θ).prod (observationLaw θ)) ^ 2 ∂sampleLaw θ n) ≤ _ at he
        rw [sameLabelKernel_integral (observationLaw θ) _ (regularObservationLabel_measurable k hk)] at he
        simp only [PairUStatistic.rowIntegral, denK] at he
        rw [sameLabelKernel_row_square_integral (observationLaw θ) _ (regularObservationLabel_measurable k hk),
          sameLabelKernel_square_integral (observationLaw θ) _ (regularObservationLabel_measurable k hk)] at he
        simp only [regularObservationLabel_mass C θ hθ k hk] at he
        exact he.trans (add_le_add
          (mul_le_mul_of_nonneg_left (regularGridCollisionRowEnergy_upper C θ hθ k hk) (by positivity))
          (mul_le_mul_of_nonneg_left (regularGridCollisionMass_upper C θ hθ k hk) (by positivity)))
      have hS_mom : (∫ z, (num z - θ.variance * den z) ^ 2 ∂sampleLaw θ n) ≤
          8 / (n : ℝ) * (C.densityUpper / (k : ℝ) ^ d) ^ 2 * rowB +
          2 / ((n : ℝ) * (n - 1 : ℕ)) * kerB * (C.densityUpper / (k : ℝ) ^ d) +
          ((regularGridOscillation C k ^ 2 / 2) * (C.densityUpper / (k : ℝ) ^ d)) ^ 2 := by
        have hSp := PairUStatistic.pairAverage_memLp_two (fun i (z : Fin n → Observation d) => z i) hi hp (regularPairScore_memLp C θ hθ k hk)
        have hmean := PairUStatistic.pairAverage_integral hn2 (fun i (z : Fin n → Observation d) => z i) hi hp
          (pairWindowScore_measurable _ (regularObservationLabel_measurable k hk) Prod.snd measurable_snd θ.variance)
          (regularPairScore_memLp C θ hθ k hk)
        let bm := ∫ p, regularPairScore θ k hk p ∂(observationLaw θ).prod (observationLaw θ)
        change (∫ z, PairUStatistic.pairAverage n (regularPairScore θ k hk) z ∂sampleLaw θ n) = bm at hmean
        have hEq : (∫ z, PairUStatistic.pairAverage n (regularPairScore θ k hk) z ^ 2 ∂sampleLaw θ n) =
            (∫ z, (PairUStatistic.pairAverage n (regularPairScore θ k hk) z - bm) ^ 2 ∂sampleLaw θ n) + bm ^ 2 := by
          have hv := variance_eq_sub hSp; have hc := variance_eq_integral hSp.aemeasurable
          change variance (fun z => PairUStatistic.pairAverage n (regularPairScore θ k hk) z) (sampleLaw θ n) =
            (∫ z, PairUStatistic.pairAverage n (regularPairScore θ k hk) z ^ 2 ∂sampleLaw θ n) -
            (∫ z, PairUStatistic.pairAverage n (regularPairScore θ k hk) z ∂sampleLaw θ n) ^ 2 at hv
          change variance (fun z => PairUStatistic.pairAverage n (regularPairScore θ k hk) z) (sampleLaw θ n) =
            ∫ z, (PairUStatistic.pairAverage n (regularPairScore θ k hk) z -
              ∫ z, PairUStatistic.pairAverage n (regularPairScore θ k hk) z ∂sampleLaw θ n) ^ 2 ∂sampleLaw θ n at hc
          rw [hmean] at hv hc; linarith
        have he := PairUStatistic.pairAverage_centered_sq_le hn2 (fun i (z : Fin n → Observation d) => z i) hi hp
          (pairWindowScore_measurable _ (regularObservationLabel_measurable k hk) Prod.snd measurable_snd θ.variance)
          (regularPairScore_memLp C θ hθ k hk) (pairWindowScore_symmetric _ Prod.snd θ.variance)
        have hC2 := (responseSecondBound_pos C).le
        have hr : (∫ x, (∫ y, regularPairScore θ k hk (x, y) ∂observationLaw θ) ^ 2 ∂observationLaw θ) ≤
            2 * (C.densityUpper / (k : ℝ) ^ d) ^ 2 * rowB :=
          (regularPairScore_row_energy_le C θ hθ k hk).trans (by dsimp [rowB]; rw [abs_of_nonneg hV0]; gcongr)
        have hker : (∫ z, regularPairScore θ k hk z ^ 2 ∂(observationLaw θ).prod (observationLaw θ)) ≤
            kerB * (C.densityUpper / (k : ℝ) ^ d) :=
          (regularPairScore_kernel_energy_le C θ hθ k hk).trans
            (by dsimp [kerB]; have := pow_le_pow_left₀ hV0 hVU 2
                have : 0 ≤ regularGridCollisionMass θ k hk := by linarith [hED, show 0 < flr by positivity]
                have := regularGridCollisionMass_upper C θ hθ k hk; gcongr)
        have hfluc : (∫ z, (PairUStatistic.pairAverage n (regularPairScore θ k hk) z - bm) ^ 2 ∂sampleLaw θ n) ≤
            8 / (n : ℝ) * (C.densityUpper / (k : ℝ) ^ d) ^ 2 * rowB +
            2 / ((n : ℝ) * (n - 1 : ℕ)) * kerB * (C.densityUpper / (k : ℝ) ^ d) :=
          he.trans ((add_le_add (mul_le_mul_of_nonneg_left hr (by positivity))
            (mul_le_mul_of_nonneg_left hker (by positivity))).trans_eq (by ring))
        have hbsq := pow_le_pow_left₀ (regularPairScore_mean_nonneg C θ hθ k hk)
          ((regularPairScore_mean_le C θ hθ k hk).trans
            (mul_le_mul_of_nonneg_left (regularGridCollisionMass_upper C θ hθ k hk) (by positivity))) 2
        simp_rw [hscore_id]; rw [hEq]; exact add_le_add hfluc hbsq
      have hb' : (∫ z, (est.val z - θ.variance) ^ 2 ∂sampleLaw θ n) ≤
          (64 * C.densityUpper ^ 2 * rowB + 32 * C.densityUpper ^ 2 * C.varianceUpper ^ 2) / (n : ℝ) +
          (16 * C.densityUpper * (kerB + C.varianceUpper ^ 2)) * (k : ℝ) ^ d / ((n : ℝ) * (n - 1 : ℕ)) +
          2 * C.densityUpper ^ 2 * regularGridOscillation C k ^ 4 :=
        (hM.trans (mul_le_mul_of_nonneg_left
          (add_le_add hS_mom (mul_le_mul_of_nonneg_left hD_fluc (sq_nonneg _))) (by positivity : 0 ≤ 2 / flr ^ 2))).trans_eq
          (by dsimp [flr]; field_simp [hk0.ne', hn0.ne', hn_sub.ne', pow_ne_zero d hk0.ne']; ring)
      have hosc : regularGridOscillation C k ^ 4 = biasF * (k : ℝ) ^ (-4 * C.smoothness) := by
        have he : ((Real.sqrt d * (1 / (k : ℝ))) ^ elementarySmoothness C) ^ 4 =
            (Real.sqrt d) ^ (4 * C.smoothness) * (k : ℝ) ^ (-4 * C.smoothness) := by
          rw [hs_eq, Real.mul_rpow (Real.sqrt_nonneg _) (by positivity), mul_pow,
            ← Real.rpow_mul_natCast (Real.sqrt_nonneg _), ← Real.rpow_mul_natCast (by positivity),
            one_div, Real.inv_rpow hk0.le, ← Real.rpow_neg hk0.le]
          congr 2 <;> ring
        unfold regularGridOscillation; rw [mul_pow, he]; dsimp [biasF]; ring
      rw [hosc] at hb'; refine hb'.trans ?_
      dsimp [K_mse, env]; rw [div_eq_mul_one_div, mul_div_assoc]
      have hp3 : 0 ≤ (k : ℝ) ^ (-4 * C.smoothness) := Real.rpow_nonneg hk0.le _
      have hp1 : 0 ≤ 1 / (n : ℝ) := by positivity
      have hp2 : 0 ≤ (k : ℝ) ^ d / ((n : ℝ) * (n - 1 : ℕ)) := by positivity
      nlinarith [mul_nonneg (show 0 ≤ 16 * C.densityUpper * (kerB + C.varianceUpper ^ 2) + 2 * C.densityUpper ^ 2 * biasF by positivity) hp1,
        mul_nonneg (show 0 ≤ (64 * C.densityUpper ^ 2 * rowB + 32 * C.densityUpper ^ 2 * C.varianceUpper ^ 2) + 2 * C.densityUpper ^ 2 * biasF by positivity) hp2,
        mul_nonneg (show 0 ≤ (64 * C.densityUpper ^ 2 * rowB + 32 * C.densityUpper ^ 2 * C.varianceUpper ^ 2) + 16 * C.densityUpper * (kerB + C.varianceUpper ^ 2) by positivity) hp3]
    have hrms := ENNReal.rpow_le_rpow ((minimaxRisk_le_worstCaseRisk C est).trans hwcr) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow] at hrms
    refine hrms.trans (ENNReal.ofReal_mono ?_)
    have henv_le : env ≤ (2 * (5 : ℝ) ^ d + 1) * (1 / (n : ℝ) + (n : ℝ) ^ (-8 * C.smoothness / ((d : ℝ) + 4 * C.smoothness))) := by
      have hfirst : (k : ℝ) ^ d / ((n : ℝ) * (n - 1 : ℕ)) ≤ 2 * ((k : ℝ) ^ d / (n : ℝ) ^ 2) := by
        rw [show ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 by simpa using Nat.cast_sub (R := ℝ) hn]
        exact (div_le_div_of_nonneg_left (by positivity) (by positivity : 0 < (n : ℝ) ^ 2 / 2) (by nlinarith)).trans_eq (by ring)
      have hvar : (k : ℝ) ^ d / (n : ℝ) ^ 2 ≤ (5 : ℝ) ^ d * (n : ℝ) ^ (-8 * C.smoothness / ((d : ℝ) + 4 * C.smoothness)) := by
        have hup := pow_le_pow_left₀ hk0.le (lowSmoothnessGrid_rounding (d := d) C.smoothness_pos hn1).2 d
        rw [mul_pow, ← Real.rpow_mul_natCast hn0.le] at hup
        refine (div_le_div_of_nonneg_right hup (sq_nonneg _)).trans_eq ?_
        rw [← Real.rpow_two, mul_div_assoc, ← Real.rpow_sub hn0]
        have hden : (d : ℝ) + 4 * C.smoothness ≠ 0 := by linarith [C.smoothness_pos]
        congr 2; unfold lowSmoothnessGridExponent; field_simp; ring
      have hbias : (k : ℝ) ^ (-4 * C.smoothness) ≤ (n : ℝ) ^ (-8 * C.smoothness / ((d : ℝ) + 4 * C.smoothness)) := by
        have hbase : (n : ℝ) ^ lowSmoothnessGridExponent d C.smoothness ≤ k := by
          have hh := (lowSmoothnessGrid_rounding (d := d) C.smoothness_pos hn1).1
          have hp := Real.rpow_pos_of_pos hn0 (lowSmoothnessGridExponent d C.smoothness)
          dsimp [k]; linarith
        refine (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hn0 _) hbase (by linarith [C.smoothness_pos])).trans_eq ?_
        rw [← Real.rpow_mul hn0.le]; congr 1; unfold lowSmoothnessGridExponent; ring
      dsimp [env]
      nlinarith [mul_le_mul_of_nonneg_left hvar (by norm_num : (0 : ℝ) ≤ 2),
        show 0 ≤ 2 * (5 : ℝ) ^ d * (1 / (n : ℝ)) by positivity]
    have hsq1 : Real.sqrt (K_mse * env) ≤
        Real.sqrt (K_mse * (2 * (5 : ℝ) ^ d + 1)) *
          ((n : ℝ) ^ (-(1 / 2 : ℝ)) + (n : ℝ) ^ (-4 * C.smoothness / ((d : ℝ) + 4 * C.smoothness))) := by
      refine (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left henv_le hK_mse.le)).trans ?_
      rw [← mul_assoc, Real.sqrt_mul (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
      have hadd : Real.sqrt (1 / (n : ℝ) + (n : ℝ) ^ (-8 * C.smoothness / ((d : ℝ) + 4 * C.smoothness))) ≤
          Real.sqrt (1 / (n : ℝ)) + Real.sqrt ((n : ℝ) ^ (-8 * C.smoothness / ((d : ℝ) + 4 * C.smoothness))) := by
        refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
        nlinarith [Real.sq_sqrt (show 0 ≤ 1 / (n : ℝ) by positivity),
          Real.sq_sqrt (Real.rpow_nonneg hn0.le (-8 * C.smoothness / ((d : ℝ) + 4 * C.smoothness))),
          mul_nonneg (Real.sqrt_nonneg (1 / (n : ℝ))) (Real.sqrt_nonneg ((n : ℝ) ^ (-8 * C.smoothness / ((d : ℝ) + 4 * C.smoothness))))]
      refine hadd.trans_eq ?_
      rw [one_div, Real.sqrt_inv, Real.sqrt_eq_rpow, Real.rpow_neg hn0.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le]
      congr 2; ring
    refine hsq1.trans ?_
    let m := max ((n : ℝ) ^ (-(1 / 2 : ℝ))) ((n : ℝ) ^ (-4 * C.smoothness / ((d : ℝ) + 4 * C.smoothness)))
    have hm1 : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ m := le_max_left _ _
    have hm2 : (n : ℝ) ^ (-4 * C.smoothness / ((d : ℝ) + 4 * C.smoothness)) ≤ m := le_max_right _ _
    have hm0 : 0 ≤ m := (Real.rpow_nonneg hn0.le _).trans hm1
    dsimp [B_rms]; nlinarith [Real.sqrt_nonneg (K_mse * (2 * (5 : ℝ) ^ d + 1)), mul_nonneg hdiam.le hm0]
  · obtain rfl : n = 1 := by omega
    have he : minimaxRisk C 1 ≤ ENNReal.ofReal ((C.varianceUpper - C.varianceLower) ^ 2) :=
      (minimaxRisk_le_worstCaseRisk C (constantEstimator d 1 C.varianceLower)).trans
        (iSup_le fun θ => constantEstimator_risk_bound C θ.val θ.property)
    have hh := ENNReal.rpow_le_rpow he (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num), ← Real.sqrt_eq_rpow, Real.sqrt_sq hdiam.le] at hh
    refine hh.trans (ENNReal.ofReal_mono ?_)
    simp only [Nat.cast_one, Real.one_rpow, max_self, mul_one]; dsimp [B_rms]
    linarith [Real.sqrt_nonneg (K_mse * (2 * (5 : ℝ) ^ d + 1))]

end LowSmoothnessGridAndUpper

-- ============================================================================
-- 2. Low-Smoothness Nonparametric Lower Bound & Endpoint
-- ============================================================================

section LowSmoothnessLowerBound
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1200000

def clampUnit (x : ℝ) : ℝ := min 1 (max 0 x)

private lemma clampUnit_mem (x : ℝ) : clampUnit x ∈ Icc (0 : ℝ) 1 :=
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

private lemma clampUnit_modulus (x y : ℝ) : |clampUnit x - clampUnit y| ≤ |x - y| := by
  have hmax : |max 0 x - max 0 y| ≤ |x - y| := by
    simpa only [sub_self, abs_zero, max_eq_right (abs_nonneg (x - y))] using abs_max_sub_max_le_max (0 : ℝ) x 0 y
  have hmin : |clampUnit x - clampUnit y| ≤ |max 0 x - max 0 y| := by
    simpa only [clampUnit, sub_self, abs_zero, max_eq_right (abs_nonneg (max 0 x - max 0 y))] using
      abs_min_sub_min_le_max (1 : ℝ) (max 0 x) 1 (max 0 y)
  exact hmin.trans hmax

def gridTent (k : ℕ) (j : Fin (k + 1)) (x : ℝ) : ℝ := max 0 (1 - |(k : ℝ) * clampUnit x - j.val|)

private lemma gridTent_nonneg (k : ℕ) (j : Fin (k + 1)) (x : ℝ) : 0 ≤ gridTent k j x := le_max_left _ _
private lemma gridTent_le_one (k : ℕ) (j : Fin (k + 1)) (x : ℝ) : gridTent k j x ≤ 1 :=
  max_le zero_le_one (by linarith [abs_nonneg ((k : ℝ) * clampUnit x - j.val)])

private lemma gridTent_continuous (k : ℕ) (j : Fin (k + 1)) : Continuous (gridTent k j) := by
  unfold gridTent clampUnit; fun_prop

private lemma gridTent_modulus (k : ℕ) (j : Fin (k + 1)) (x y : ℝ) :
    |gridTent k j x - gridTent k j y| ≤ (k : ℝ) * |x - y| := by
  have h := abs_max_sub_max_le_max (0 : ℝ) (1 - |(k : ℝ) * clampUnit x - j.val|) 0 (1 - |(k : ℝ) * clampUnit y - j.val|)
  have hr : max 0 |(1 - |(k : ℝ) * clampUnit x - j.val|) - (1 - |(k : ℝ) * clampUnit y - j.val|)| =
      abs (|(k : ℝ) * clampUnit x - j.val| - |(k : ℝ) * clampUnit y - j.val|) := by
    rw [max_eq_right (abs_nonneg _), sub_sub_sub_cancel_left, abs_sub_comm]
  refine (show |gridTent k j x - gridTent k j y| ≤ _ by simpa only [gridTent, sub_self, abs_zero, hr] using h).trans
    ((abs_abs_sub_abs_le_abs_sub _ _).trans ?_)
  rw [sub_sub_sub_cancel_right, ← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
  exact mul_le_mul_of_nonneg_left (clampUnit_modulus x y) (Nat.cast_nonneg k)

def gridTentEnergy (k : ℕ) (x : ℝ) : ℝ := ∑ j : Fin (k + 1), gridTent k j x ^ 2

private lemma gridTentEnergy_lower (k : ℕ) (x : ℝ) : (1 / 4 : ℝ) ≤ gridTentEnergy k x := by
  let t := (k : ℝ) * clampUnit x
  have ht0 : 0 ≤ t := mul_nonneg (Nat.cast_nonneg k) (clampUnit_mem x).1
  have htk : t ≤ k := by simpa [t] using mul_le_mul_of_nonneg_left (clampUnit_mem x).2 (Nat.cast_nonneg k)
  let j := Nat.floor (t + 1 / 2)
  have hfl : (j : ℝ) ≤ t + 1 / 2 := Nat.floor_le (by linarith)
  have hlt : t + 1 / 2 < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have hjk : j ≤ k := by
    by_contra h; have : (k : ℝ) + 1 ≤ j := (by exact_mod_cast (by omega : k + 1 ≤ j))
    linarith
  have hj_ge : (1 / 2 : ℝ) ≤ gridTent k ⟨j, by omega⟩ x :=
    le_trans (by have : |t - j| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩; dsimp [t] at *; linarith) (le_max_right _ _)
  exact (show (1 / 4 : ℝ) ≤ gridTent k ⟨j, by omega⟩ x ^ 2 by nlinarith).trans
    (Finset.single_le_sum (f := fun i => gridTent k i x ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ _))

private lemma gridTentEnergy_pos (k : ℕ) (x : ℝ) : 0 < gridTentEnergy k x :=
  (by norm_num : (0 : ℝ) < 1 / 4).trans_le (gridTentEnergy_lower k x)

def gridTentActive (k : ℕ) (x : ℝ) : Finset (Fin (k + 1)) := Finset.univ.filter fun j => gridTent k j x ≠ 0

private lemma gridTent_active_card (k : ℕ) (x : ℝ) : (gridTentActive k x).card ≤ 2 := by
  let t := (k : ℝ) * clampUnit x
  let m := Nat.floor t
  have hsub : (gridTentActive k x).image Fin.val ⊆ {m, m + 1} := fun j hj => by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have hd : |t - i.val| < 1 := by
      by_contra h; exact (Finset.mem_filter.mp hi).2 (max_eq_left (by dsimp [t] at h; linarith))
    have hm : (m : ℝ) ≤ t := Nat.floor_le (mul_nonneg (Nat.cast_nonneg k) (clampUnit_mem x).1)
    have hlt : t < (m : ℝ) + 1 := Nat.lt_floor_add_one t
    have hlo : m ≤ i.val := by
      by_contra h; have hc : (i.val : ℝ) + 1 ≤ m := (by exact_mod_cast (by omega : i.val + 1 ≤ m))
      linarith [(abs_lt.mp hd).2]
    have hhi : i.val ≤ m + 1 := by
      by_contra h; have hc : (m : ℝ) + 2 ≤ i.val := (by exact_mod_cast (by omega : m + 2 ≤ i.val))
      linarith [(abs_lt.mp hd).1]
    have : i.val = m ∨ i.val = m + 1 := by omega
    rcases this with h | h <;> simp [h]
  simpa [Finset.card_image_of_injective _ Fin.val_injective] using (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

def gridWindow (k : ℕ) (j : Fin (k + 1)) (x : ℝ) : ℝ := gridTent k j x / Real.sqrt (gridTentEnergy k x)

private lemma gridWindow_nonneg (k : ℕ) (j : Fin (k + 1)) (x : ℝ) : 0 ≤ gridWindow k j x :=
  div_nonneg (gridTent_nonneg k j x) (Real.sqrt_nonneg _)

private lemma gridWindow_continuous (k : ℕ) (j : Fin (k + 1)) : Continuous (gridWindow k j) :=
  (gridTent_continuous k j).div (continuous_finsetSum _ fun i _ => (gridTent_continuous k i).pow 2).sqrt
    fun x => (Real.sqrt_pos.mpr (gridTentEnergy_pos k x)).ne'

private lemma gridWindow_square_partition (k : ℕ) (x : ℝ) : (∑ j : Fin (k + 1), gridWindow k j x ^ 2) = 1 := by
  simp only [gridWindow, div_pow, Real.sq_sqrt (gridTentEnergy_pos k x).le, ← Finset.sum_div]
  exact div_self (gridTentEnergy_pos k x).ne'

private lemma gridWindow_le_one (k : ℕ) (j : Fin (k + 1)) (x : ℝ) : gridWindow k j x ≤ 1 := by
  have hs : gridWindow k j x ^ 2 ≤ 1 := by
    rw [← gridWindow_square_partition k x]
    exact Finset.single_le_sum (f := fun i => gridWindow k i x ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  nlinarith [gridWindow_nonneg k j x]

private lemma gridWindow_modulus (k : ℕ) (j : Fin (k + 1)) (x y : ℝ) :
    |gridWindow k j x - gridWindow k j y| ≤ 34 * k * |x - y| := by
  let S := gridTentActive k x ∪ gridTentActive k y
  have hcard : (S.card : ℝ) ≤ 4 := by
    exact_mod_cast (Finset.card_union_le _ _).trans
      (by have := gridTent_active_card k x; have := gridTent_active_card k y; omega)
  have he_mod : |gridTentEnergy k x - gridTentEnergy k y| ≤ 8 * k * |x - y| := by
    have hz (i : Fin (k + 1)) (hi : i ∉ S) : gridTent k i x ^ 2 - gridTent k i y ^ 2 = 0 := by
      have hx : gridTent k i x = 0 := by simpa [gridTentActive] using fun h => hi (Finset.mem_union_left _ h)
      have hy : gridTent k i y = 0 := by simpa [gridTentActive] using fun h => hi (Finset.mem_union_right _ h)
      simp [hx, hy]
    change |(∑ i, gridTent k i x ^ 2) - ∑ i, gridTent k i y ^ 2| ≤ _
    rw [← Finset.sum_sub_distrib, ← Finset.sum_subset (Finset.subset_univ S) fun i _ => hz i]
    refine (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum (g := fun _ => 2 * (k : ℝ) * |x - y|) fun i _ => ?_).trans ?_)
    · rw [show gridTent k i x ^ 2 - gridTent k i y ^ 2 = (gridTent k i x - gridTent k i y) * (gridTent k i x + gridTent k i y) by ring,
        abs_mul, abs_of_nonneg (add_nonneg (gridTent_nonneg ..) (gridTent_nonneg ..))]
      nlinarith [gridTent_modulus k i x y, gridTent_le_one k i x, gridTent_le_one k i y, abs_nonneg (gridTent k i x - gridTent k i y)]
    · simp only [Finset.sum_const, nsmul_eq_mul]; nlinarith [mul_nonneg (Nat.cast_nonneg k) (abs_nonneg (x - y))]
  let A := Real.sqrt (gridTentEnergy k x)
  let B := Real.sqrt (gridTentEnergy k y)
  have hA : (1 / 2 : ℝ) ≤ A := by nlinarith [Real.sqrt_nonneg (gridTentEnergy k x), Real.sq_sqrt (gridTentEnergy_pos k x).le, gridTentEnergy_lower k x]
  have hB : (1 / 2 : ℝ) ≤ B := by nlinarith [Real.sqrt_nonneg (gridTentEnergy k y), Real.sq_sqrt (gridTentEnergy_pos k y).le, gridTentEnergy_lower k y]
  have hAp : 0 < A := by linarith
  have hBp : 0 < B := by linarith
  have hBA : |B - A| ≤ 8 * k * |x - y| := by
    have hid : |gridTentEnergy k x - gridTentEnergy k y| = |B - A| * (A + B) := by
      conv_lhs => rw [← Real.sq_sqrt (gridTentEnergy_pos k x).le, ← Real.sq_sqrt (gridTentEnergy_pos k y).le]
      change |A ^ 2 - B ^ 2| = |B - A| * (A + B)
      rw [show A ^ 2 - B ^ 2 = (A - B) * (A + B) by ring, abs_mul, abs_sub_comm A B, abs_of_nonneg (add_nonneg hAp.le hBp.le)]
    rw [hid] at he_mod; nlinarith [abs_nonneg (B - A)]
  rw [show gridWindow k j x - gridWindow k j y =
      (gridTent k j x - gridTent k j y) / A + gridTent k j y * (B - A) / (A * B) by
    change gridTent k j x / A - gridTent k j y / B = _; field_simp [hAp.ne', hBp.ne']; ring]
  refine (abs_add_le _ _).trans ?_
  have h1 : |(gridTent k j x - gridTent k j y) / A| ≤ 2 * k * |x - y| := by
    rw [abs_div, abs_of_pos hAp, div_le_iff₀ hAp]
    nlinarith [gridTent_modulus k j x y, mul_nonneg (Nat.cast_nonneg k) (abs_nonneg (x - y))]
  have h2 : |gridTent k j y * (B - A) / (A * B)| ≤ 32 * k * |x - y| := by
    rw [abs_div, abs_mul, abs_of_nonneg (gridTent_nonneg k j y), abs_of_pos (mul_pos hAp hBp), div_le_iff₀ (mul_pos hAp hBp)]
    have hAB : (1 / 4 : ℝ) ≤ A * B := by nlinarith
    nlinarith [gridTent_le_one k j y, gridTent_nonneg k j y, abs_nonneg (B - A),
      mul_nonneg (sub_nonneg.mpr (gridTent_le_one k j y)) (abs_nonneg (B - A)),
      mul_nonneg (Nat.cast_nonneg k) (abs_nonneg (x - y))]
  linarith

def gridTensorWindow (d k : ℕ) (j : Fin d → Fin (k + 1)) (x : Covariate d) : ℝ :=
  ∏ i, gridWindow k (j i) (x i)

private lemma gridTensorWindow_nonneg (d k : ℕ) (j : Fin d → Fin (k + 1)) (x : Covariate d) :
    0 ≤ gridTensorWindow d k j x := Finset.prod_nonneg fun i _ => gridWindow_nonneg k (j i) (x i)

private lemma gridTensorWindow_le_one (d k : ℕ) (j : Fin d → Fin (k + 1)) (x : Covariate d) :
    gridTensorWindow d k j x ≤ 1 :=
  Finset.prod_le_one₀ (fun i _ => gridWindow_nonneg k (j i) (x i)) fun i _ => gridWindow_le_one k (j i) (x i)

private lemma gridTensorWindow_modulus (d k : ℕ) (j : Fin d → Fin (k + 1)) (x y : Covariate d) :
    |gridTensorWindow d k j x - gridTensorWindow d k j y| ≤ 34 * k * d * euclideanNorm (x - y) := by
  have hprod (s : Finset (Fin d)) :
      |(∏ i ∈ s, gridWindow k (j i) (x i)) - ∏ i ∈ s, gridWindow k (j i) (y i)| ≤
        ∑ i ∈ s, |gridWindow k (j i) (x i) - gridWindow k (j i) (y i)| := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
      have hp : |∏ l ∈ s, gridWindow k (j l) (x l)| ≤ 1 := by
        rw [Finset.abs_prod]
        exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun l _ => by
          rw [abs_of_nonneg (gridWindow_nonneg ..)]; exact gridWindow_le_one ..
      have hgy : |gridWindow k (j i) (y i)| ≤ 1 := by
        rw [abs_of_nonneg (gridWindow_nonneg ..)]; exact gridWindow_le_one ..
      rw [show gridWindow k (j i) (x i) * (∏ l ∈ s, gridWindow k (j l) (x l)) -
          gridWindow k (j i) (y i) * (∏ l ∈ s, gridWindow k (j l) (y l)) =
        (gridWindow k (j i) (x i) - gridWindow k (j i) (y i)) * (∏ l ∈ s, gridWindow k (j l) (x l)) +
          gridWindow k (j i) (y i) * ((∏ l ∈ s, gridWindow k (j l) (x l)) - ∏ l ∈ s, gridWindow k (j l) (y l)) by ring]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      exact add_le_add (by nlinarith [abs_nonneg (gridWindow k (j i) (x i) - gridWindow k (j i) (y i))])
        (by simpa only [one_mul] using mul_le_mul hgy ih (abs_nonneg _) zero_le_one)
  refine (hprod Finset.univ).trans ((Finset.sum_le_sum (g := fun _ => 34 * (k : ℝ) * euclideanNorm (x - y)) fun i _ => ?_).trans (by simp; ring_nf; rfl))
  refine (gridWindow_modulus k (j i) (x i) (y i)).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hs : (x i - y i) ^ 2 ≤ ∑ l, (x - y) l ^ 2 :=
    Finset.single_le_sum (f := fun l => (x - y) l ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  unfold euclideanNorm
  nlinarith [Real.sq_sqrt (Finset.sum_nonneg fun l (_ : l ∈ Finset.univ) => sq_nonneg ((x - y) l)),
    Real.sqrt_nonneg (∑ l, (x - y) l ^ 2), sq_abs (x i - y i), abs_nonneg (x i - y i)]

def gridPatch (d k : ℕ) (j : Fin d → Fin (k + 1)) : Set (Covariate d) :=
  {x | ∀ i, |(k : ℝ) * clampUnit (x i) - (j i).val| ≤ 1}

private lemma gridPatch_measurable (d k : ℕ) (j : Fin d → Fin (k + 1)) : MeasurableSet (gridPatch d k j) := by
  rw [show gridPatch d k j = ⋂ i : Fin d, {x : Covariate d | |(k : ℝ) * clampUnit (x i) - (j i).val| ≤ 1} by ext; simp [gridPatch]]
  exact MeasurableSet.iInter fun i => measurableSet_le
    ((by unfold clampUnit; fun_prop : Continuous fun x : Covariate d => |(k : ℝ) * clampUnit (x i) - (j i).val|).measurable)
    measurable_const

private lemma gridTensorWindow_zero_outside_patch (d k : ℕ) (j : Fin d → Fin (k + 1))
    (x : Covariate d) (hx : x ∉ gridPatch d k j) : gridTensorWindow d k j x = 0 := by
  obtain ⟨i, hi⟩ := not_forall.mp hx
  have ht : gridTent k (j i) (x i) = 0 := max_eq_left (by linarith [lt_of_not_ge hi])
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [gridWindow, ht])

private lemma gridPatch_cube_probability_bound (d k : ℕ) (j : Fin d → Fin (k + 1)) (hk : 0 < k) :
    (cubeVolume d).real (gridPatch d k j) ≤ (2 / (k : ℝ)) ^ d := by
  have hkp : (0 : ℝ) < k := by exact_mod_cast hk
  let R : Set (Covariate d) := Set.univ.pi fun i => Icc (((j i).val - 1 : ℝ) / k) (((j i).val + 1 : ℝ) / k)
  have hsub : gridPatch d k j ∩ unitCube d ⊆ R := fun x hx i _ => by
    have hi := hx.1 i
    rw [show clampUnit (x i) = x i by simp [clampUnit, max_eq_right (hx.2 i).1, min_eq_right (hx.2 i).2]] at hi
    exact ⟨(div_le_iff₀ hkp).mpr (by linarith [(abs_le.mp hi).1]), (le_div_iff₀ hkp).mpr (by linarith [(abs_le.mp hi).2])⟩
  have hb : cubeVolume d (gridPatch d k j) ≤ ENNReal.ofReal ((2 / (k : ℝ)) ^ d) := by
    rw [cubeVolume, Measure.restrict_apply (gridPatch_measurable d k j)]
    refine (measure_mono hsub).trans_eq ?_
    rw [volume_pi, Measure.pi_pi]
    simp only [Real.volume_Icc, show ∀ i : Fin d, (((j i).val + 1 : ℝ) / k) - (((j i).val - 1 : ℝ) / k) = 2 / k from fun _ => by ring,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact (ENNReal.ofReal_pow (by positivity) d).symm
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq (ENNReal.toReal_ofReal (by positivity))

private lemma grid_observed_patch_degree (d k n : ℕ) (x : Fin n → Covariate d) (j : Fin d → Fin (k + 1)) :
    (Finset.univ.filter fun l : Fin d → Fin (k + 1) =>
      ¬Disjoint (Finset.univ.filter fun i => x i ∈ gridPatch d k j)
        (Finset.univ.filter fun i => x i ∈ gridPatch d k l)).card ≤ 5 ^ d := by
  let N1 (a : Fin (k + 1)) : Finset (Fin (k + 1)) := Finset.univ.filter fun b => |(a.val : ℝ) - b.val| ≤ 2
  have hN1 (a : Fin (k + 1)) : (N1 a).card ≤ 5 := by
    have hsub : (N1 a).image Fin.val ⊆ Finset.Icc (a.val - 2) (a.val + 2) := fun b hb => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
      have hd := abs_le.mp (Finset.mem_filter.mp hi).2
      have h1 : a.val ≤ i.val + 2 := by exact_mod_cast (by linarith : (a.val : ℝ) ≤ i.val + 2)
      have h2 : i.val ≤ a.val + 2 := by exact_mod_cast (by linarith : (i.val : ℝ) ≤ a.val + 2)
      exact Finset.mem_Icc.mpr ⟨by omega, h2⟩
    have h := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Fin.val_injective, Nat.card_Icc] at h; omega
  have hsub : (Finset.univ.filter fun l : Fin d → Fin (k + 1) =>
      ¬Disjoint (Finset.univ.filter fun i => x i ∈ gridPatch d k j)
        (Finset.univ.filter fun i => x i ∈ gridPatch d k l)) ⊆ Fintype.piFinset fun i => N1 (j i) := fun l hl => by
    obtain ⟨i0, hi, hi'⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hl).2
    refine Fintype.mem_piFinset.mpr fun r => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have h1 := abs_le.mp ((Finset.mem_filter.mp hi).2 r)
    have h2 := abs_le.mp ((Finset.mem_filter.mp hi').2 r)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  refine (Finset.card_le_card hsub).trans ?_
  rw [Fintype.card_piFinset]
  exact (Finset.prod_le_prod fun i _ => hN1 (j i)).trans_eq (by simp)

def indexedGridEquiv (d k : ℕ) : Fin ((k + 1) ^ d) ≃ (Fin d → Fin (k + 1)) :=
  (Fintype.equivFinOfCardEq (by simp)).symm

def indexedGridField (d k : ℕ) (η : ℝ) (ξ : Fin ((k + 1) ^ d) → Fin 3) (x : Covariate d) : ℝ :=
  η * ∑ j, gridTensorWindow d k (indexedGridEquiv d k j) x * ternaryValue 1 (ξ j)

private lemma ternaryValue_one_abs_le (y : Fin 3) : |ternaryValue 1 y| ≤ 1 := by
  fin_cases y <;> norm_num [ternaryValue]

private lemma indexedGridField_continuous (d k : ℕ) (η : ℝ) (ξ : Fin ((k + 1) ^ d) → Fin 3) :
    Continuous (indexedGridField d k η ξ) :=
  (continuous_finsetSum _ fun _ _ =>
    (continuous_finsetProd _ fun i _ => (gridWindow_continuous k _).comp (continuous_apply i)).mul_const _).const_mul _

private lemma gridActiveTensor_spec (d k : ℕ) (x : Covariate d) :
    let A : Finset (Fin d → Fin (k + 1)) := Fintype.piFinset fun i => gridTentActive k (x i)
    A.card ≤ 2 ^ d ∧ ∀ j ∉ A, gridTensorWindow d k j x = 0 := by
  refine ⟨by rw [Fintype.card_piFinset]; exact (Finset.prod_le_prod fun i _ => gridTent_active_card k (x i)).trans_eq (by simp),
    fun j hj => ?_⟩
  obtain ⟨i, hi⟩ := not_forall.mp (by simpa [Fintype.mem_piFinset] using hj)
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (by simp [gridWindow, show gridTent k (j i) (x i) = 0 by simpa [gridTentActive] using hi])

private lemma indexedGridField_abs_bound (d k : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (ξ : Fin ((k + 1) ^ d) → Fin 3) (x : Covariate d) :
    |indexedGridField d k η ξ x| ≤ (2 : ℝ) ^ d * η := by
  let S : Finset (Fin d → Fin (k + 1)) := Fintype.piFinset fun i => gridTentActive k (x i)
  obtain ⟨hSc, hzero⟩ := gridActiveTensor_spec d k x
  have hScard : (S.card : ℝ) ≤ (2 : ℝ) ^ d := by exact_mod_cast hSc
  have heq : indexedGridField d k η ξ x = η * ∑ j ∈ S, gridTensorWindow d k j x * ternaryValue 1 (ξ ((indexedGridEquiv d k).symm j)) := by
    unfold indexedGridField; congr 1
    rw [Fintype.sum_equiv (indexedGridEquiv d k) _ (fun j => gridTensorWindow d k j x * ternaryValue 1 (ξ ((indexedGridEquiv d k).symm j))) fun _ => by simp]
    exact (Finset.sum_subset (Finset.subset_univ S) fun j _ hj => by simp [hzero j hj]).symm
  rw [heq, abs_mul, abs_of_nonneg hη, mul_comm]
  refine mul_le_mul_of_nonneg_right ((Finset.abs_sum_le_sum_abs ..).trans
    ((Finset.sum_le_sum (g := fun _ => (1 : ℝ)) fun j _ => ?_).trans (by simpa using hScard))) hη
  rw [abs_mul, abs_of_nonneg (gridTensorWindow_nonneg d k j x)]
  simpa using mul_le_mul (gridTensorWindow_le_one d k j x) (ternaryValue_one_abs_le _) (abs_nonneg _) zero_le_one

private lemma indexedGridField_holder_bound (d k : ℕ) (s b : ℝ) (hk : 1 ≤ k)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hb : 0 ≤ b)
    (ξ : Fin ((k + 1) ^ d) → Fin 3) (x y : Covariate d) :
    |indexedGridField d k (b / (k : ℝ) ^ s) ξ x - indexedGridField d k (b / (k : ℝ) ^ s) ξ y| ≤
      (68 * (2 : ℝ) ^ d * (d + 1)) * b * euclideanNorm (x - y) ^ s := by
  have hkp : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  let η := b / (k : ℝ) ^ s
  have hη : 0 ≤ η := by positivity
  have hlip : |indexedGridField d k η ξ x - indexedGridField d k η ξ y| ≤
      (68 * (2 : ℝ) ^ d * (d + 1)) * η * k * euclideanNorm (x - y) := by
    let Ax : Finset (Fin d → Fin (k + 1)) := Fintype.piFinset fun i => gridTentActive k (x i)
    let Ay : Finset (Fin d → Fin (k + 1)) := Fintype.piFinset fun i => gridTentActive k (y i)
    let S := Ax ∪ Ay
    obtain ⟨hAx, hzx⟩ := gridActiveTensor_spec d k x
    obtain ⟨hAy, hzy⟩ := gridActiveTensor_spec d k y
    have hScard : (S.card : ℝ) ≤ 2 * (2 : ℝ) ^ d := by
      have : S.card ≤ 2 ^ d + 2 ^ d := (Finset.card_union_le Ax Ay).trans (Nat.add_le_add hAx hAy)
      have hc : (S.card : ℝ) ≤ (2 : ℝ) ^ d + (2 : ℝ) ^ d := by exact_mod_cast this
      linarith
    have heq : indexedGridField d k η ξ x - indexedGridField d k η ξ y =
        η * ∑ j ∈ S, (gridTensorWindow d k j x - gridTensorWindow d k j y) * ternaryValue 1 (ξ ((indexedGridEquiv d k).symm j)) := by
      unfold indexedGridField; rw [← mul_sub, ← Finset.sum_sub_distrib]; congr 1
      rw [Fintype.sum_equiv (indexedGridEquiv d k) _
        (fun j => (gridTensorWindow d k j x - gridTensorWindow d k j y) * ternaryValue 1 (ξ ((indexedGridEquiv d k).symm j)))
        fun _ => by simp; ring]
      exact (Finset.sum_subset (Finset.subset_univ S) fun j _ hj => by
        simp [hzx j fun hx => hj (Finset.mem_union_left _ hx), hzy j fun hy => hj (Finset.mem_union_right _ hy)]).symm
    rw [heq, abs_mul, abs_of_nonneg hη]
    have hsum : |∑ j ∈ S, (gridTensorWindow d k j x - gridTensorWindow d k j y) *
        ternaryValue 1 (ξ ((indexedGridEquiv d k).symm j))| ≤ 68 * (2 : ℝ) ^ d * (d + 1) * k * euclideanNorm (x - y) := by
      refine (Finset.abs_sum_le_sum_abs ..).trans
        ((Finset.sum_le_sum (g := fun _ => 34 * (k : ℝ) * d * euclideanNorm (x - y)) fun j _ => ?_).trans ?_)
      · rw [abs_mul]
        simpa using mul_le_mul (gridTensorWindow_modulus d k j x y) (ternaryValue_one_abs_le _)
          (abs_nonneg _) (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
      · simp only [Finset.sum_const, nsmul_eq_mul]
        have hn : 0 ≤ euclideanNorm (x - y) := Real.sqrt_nonneg _
        nlinarith [mul_le_mul_of_nonneg_right hScard (mul_nonneg (by positivity : (0 : ℝ) ≤ 34 * k * d) hn),
          mul_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ d * k) hn]
    exact (mul_le_mul_of_nonneg_left hsum hη).trans_eq (by ring)
  let A := 68 * (2 : ℝ) ^ d * ((d : ℝ) + 1)
  have hA : 0 ≤ A := by positivity
  let r := euclideanNorm (x - y)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have heq_r : A * η * ((k : ℝ) * r) ^ s = A * b * r ^ s := by
    dsimp [η]; rw [Real.mul_rpow hkp.le hr]; field_simp [(Real.rpow_pos_of_pos hkp s).ne']
  by_cases hkr : (k : ℝ) * r ≤ 1
  · exact (show |indexedGridField d k η ξ x - indexedGridField d k η ξ y| ≤ A * η * ((k : ℝ) * r) by dsimp [A, r]; linarith [hlip]).trans
      ((mul_le_mul_of_nonneg_left (Real.self_le_rpow_of_le_one (mul_nonneg hkp.le hr) hkr hs1) (mul_nonneg hA hη)).trans_eq heq_r)
  · have h1 : 1 ≤ ((k : ℝ) * r) ^ s := Real.one_le_rpow (le_of_not_ge hkr) hs
    have hbdd : |indexedGridField d k η ξ x - indexedGridField d k η ξ y| ≤ A * η := by
      have hsub := abs_sub_le (indexedGridField d k η ξ x) 0 (indexedGridField d k η ξ y)
      simp only [sub_zero, zero_sub, abs_neg] at hsub
      dsimp [A]; nlinarith [indexedGridField_abs_bound d k η hη ξ x, indexedGridField_abs_bound d k η hη ξ y,
        mul_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ d) hη]
    exact hbdd.trans ((by nlinarith [mul_nonneg hA hη] : A * η ≤ A * η * ((k : ℝ) * r) ^ s).trans_eq heq_r)

private lemma patch_expected_score_energy_support_bound (n : ℕ) (a V η z ρ c : ℝ)
    (g w : Fin n → ℝ) (S : Finset (Fin n))
    (ha : 0 < a) (hρ : 0 ≤ ρ) (hc : 0 < c)
    (hz : z ∈ Icc (-1 : ℝ) 1) (hwzero : ∀ i, i ∉ S → w i = 0)
    (hw : ∀ i ∈ S, |w i| ≤ 1)
    (hreg : ∀ u ∈ Icc (-1 : ℝ) 1, ∀ i ∈ S, |g i + η * w i * u| ≤ ρ)
    (hq : ∀ u ∈ Icc (-1 : ℝ) 1, ∀ i ∈ S, ∀ y,
      0 ≤ ternaryMass a (g i + η * w i * u) V y ∧ ternaryMass a (g i + η * w i * u) V y ≤ 1)
    (hlower : ∀ i ∈ S, ∀ y, c ≤ ternaryMass a (g i + η * w i * z) V y)
    (hp : ∀ i y, 0 < ternaryMass a (g i + η * w i * z) V y) :
    patchExpectedScoreEnergy n a V η g w z ≤
      if 2 ≤ S.card then ternaryScoreExponentialConstant a ρ c ^ S.card * η ^ 4 else 0 := by
  have hratio (m' : ℕ) (gm wm : Fin m' → ℝ) (ym : Fin m' → Fin 3)
      (hpm : ∀ k, 0 < ternaryMass a (gm k + η * wm k * z) V (ym k)) :
      patchObservableScore m' a V η gm wm ym z =
        symmetricDifference (patchResponseProduct m' a V η gm wm ym) /
          patchResponseProduct m' a V η gm wm ym z -
        η ^ 2 * ∑ i, (wm i) ^ 2 *
          (ternaryVarianceDerivative a (ym i) / ternaryMass a (gm i + η * wm i * z) V (ym i)) := by
    unfold patchObservableScore patchScoreNumerator; rw [sub_div]
    have hvr (i : Fin m') : patchVarianceTerm m' a V η gm wm ym z i / patchResponseProduct m' a V η gm wm ym z =
        ternaryVarianceDerivative a (ym i) / ternaryMass a (gm i + η * wm i * z) V (ym i) := by
      unfold patchVarianceTerm patchResponseProduct
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      exact mul_div_mul_right _ _ (Finset.prod_pos fun k _ => hpm k).ne'
    simp_rw [mul_div_assoc, Finset.sum_div, mul_div_assoc, hvr]
  unfold patchExpectedScoreEnergy
  split_ifs with hcount
  · let e := S.equivFin.symm
    have hsq (y : Fin n → Fin 3) :
        (patchObservableScore n a V η g w y z) ^ 2 ≤ ternaryScoreExponentialConstant a ρ c ^ S.card * η ^ 4 := by
      have hres : patchObservableScore n a V η g w y z =
          patchObservableScore S.card a V η (fun i => g (e i)) (fun i => w (e i)) (fun i => y (e i)) z := by
        let O : ℝ := ∏ i ∈ (Finset.univ : Finset (Fin n)) \ S, ternaryMass a (g i) V (y i)
        have hO : O ≠ 0 := (Finset.prod_pos fun i hi => by simpa [hwzero i (Finset.mem_sdiff.mp hi).2] using hp i (y i)).ne'
        have hfac (u : ℝ) : patchResponseProduct n a V η g w y u =
            O * patchResponseProduct S.card a V η (fun i => g (e i)) (fun i => w (e i)) (fun i => y (e i)) u := by
          unfold patchResponseProduct; rw [← Finset.prod_sdiff (Finset.subset_univ S)]; congr 1
          · exact Finset.prod_congr rfl fun i hi => by simp [hwzero i (Finset.mem_sdiff.mp hi).2]
          · rw [Finset.prod_subtype S fun _ => Iff.rfl]; exact (Fintype.prod_equiv e _ _ fun _ => rfl).symm
        have hrat (u : ℝ) : patchResponseProduct n a V η g w y u / patchResponseProduct n a V η g w y z =
            patchResponseProduct S.card a V η (fun i => g (e i)) (fun i => w (e i)) (fun i => y (e i)) u /
              patchResponseProduct S.card a V η (fun i => g (e i)) (fun i => w (e i)) (fun i => y (e i)) z := by
          rw [hfac u, hfac z]; exact mul_div_mul_left _ _ hO
        rw [hratio n g w y fun i => hp i (y i), hratio S.card _ _ _ fun i => hp (e i) (y (e i))]
        congr 1
        · unfold symmetricDifference; simp only [sub_div, add_div, mul_div_assoc]; rw [hrat 1, hrat (-1), hrat 0]
        · congr 1
          rw [← Finset.sum_subset (Finset.subset_univ S) fun i _ hi => by simp [hwzero i hi],
            Finset.sum_subtype S fun _ => Iff.rfl]
          exact (Fintype.sum_equiv e _ _ fun _ => rfl).symm
      rw [hres]
      let M := (2 * ρ + a) / a ^ 2
      have hs := patch_score_square_bound S.card a V η z M (2 / a ^ 2) (1 / a ^ 2) c
        (fun i => g (e i)) (fun i => w (e i)) (fun i => y (e i)) (by omega) hz
        (by dsimp [M]; positivity) (by positivity) (by positivity) hc
        (fun i => hw (e i) (e i).property)
        (fun u hu i => (abs_of_nonneg (hq u hu (e i) (e i).property (y (e i))).1).trans_le (hq u hu (e i) (e i).property (y (e i))).2)
        (fun u hu i => ternary_mean_derivative_abs_bound a _ ρ ha hρ (hreg u hu (e i) (e i).property) (y (e i)))
        (fun i => ternary_mean_second_derivative_abs_bound a ha (y (e i)))
        (fun i => ternary_variance_derivative_abs_bound a ha (y (e i)))
        (fun i => hlower (e i) (e i).property (y (e i)))
      rw [show M ^ 2 + 2 / a ^ 2 + 1 / a ^ 2 = M ^ 2 + 3 / a ^ 2 by ring] at hs
      simpa [ternaryScoreExponentialConstant, M] using
        score_bound_exponential_absorption S.card (M ^ 2 + 3 / a ^ 2) c η _ (by omega) hc hs
    calc _ ≤ ∑ y : Fin n → Fin 3, patchResponseProduct n a V η g w y z * (ternaryScoreExponentialConstant a ρ c ^ S.card * η ^ 4) :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hsq y) (Finset.prod_nonneg fun i _ => (hp i (y i)).le)
      _ = _ := by rw [← Finset.sum_mul, patch_response_normalized n a V η g w z ha.ne', one_mul]
  · refine le_of_eq (Finset.sum_eq_zero fun y _ => ?_)
    rcases (show S.card = 0 ∨ S.card = 1 by omega) with h0 | h1
    · have hS := Finset.card_eq_zero.mp h0
      simp [patchObservableScore, patch_score_cancel_zero n a V η g w y z fun i => hwzero i (by simp [hS]), mul_zero]
    · obtain ⟨i, hS⟩ := Finset.card_eq_one.mp h1
      simp [patchObservableScore, patch_score_cancel_singleton n a V η g w y z ha.ne' i fun k hki => hwzero k (by simpa [hS] using hki), mul_zero]

private lemma finite_prior_amgm_minimax_lower {d m n : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (η : ℝ) (hη : 0 < η)
    (F : (Fin m → Fin 3) → Covariate d → ℝ) (hF_cont : ∀ ξ, Continuous (F ξ))
    (hadm : ∀ t ∈ Icc (0 : ℝ) 1, ∀ ξ, ∃ θ : RegressionParameter d,
      Admissible C θ ∧ θ.variance = P.v - η ^ 2 * t ∧
      ∃ hp : ∀ x y, 0 ≤ ternaryMass P.a (F ξ x) (P.v - η ^ 2 * t) y,
        sampleLaw θ n = sampleLaw (uniformTernaryParameter P.a (P.v - η ^ 2 * t) (F ξ) (hF_cont ξ).measurable P.a_pos.ne' hp) n)
    (hL_pos : ∀ t ∈ Icc (0 : ℝ) 1, ∀ (x : Fin n → Covariate d) ξ y,
      0 < finiteResponseLikelihood m n P.a (P.v - η ^ 2 * t) (fun ξ' i => F ξ' (x i)) ξ y)
    (hener_le : ∀ t ∈ Icc (0 : ℝ) 1,
      (∫⁻ x : Fin n → Covariate d, ENNReal.ofReal
        (∑ ξ : Fin m → Fin 3, activationProductPrior m t ξ *
          ∑ y : Fin n → Fin 3, finiteResponseLikelihood m n P.a (P.v - η ^ 2 * t) (fun ξ' i => F ξ' (x i)) ξ y *
            finiteExperimentScore m n P.a (P.v - η ^ 2 * t) η (fun ξ' i => F ξ' (x i)) ξ y ^ 2)
        ∂Measure.pi fun _ : Fin n => cubeVolume d) ≤ 1) :
    ENNReal.ofReal ((η ^ 2 / 3) ^ 2) ≤ minimaxRisk C n := by
  let _ := cubeVolume_isProbability d
  let ν := Measure.pi fun _ : Fin n => cubeVolume d
  let _ : IsProbabilityMeasure ν := inferInstance
  let f (x : Fin n → Covariate d) : (Fin m → Fin 3) → Fin n → ℝ := fun ξ i => F ξ (x i)
  refine le_iInf fun T => ?_
  let E (x : Fin n → Covariate d) (y : Fin n → Fin 3) : ℝ := T.val (encodeDesignResponse P.a (x, y))
  let riskX (t : ℝ) (x : Fin n → Covariate d) : ℝ :=
    ∑ ξ : Fin m → Fin 3, activationProductPrior m t ξ *
      ∑ y : Fin n → Fin 3, finiteResponseLikelihood m n P.a (P.v - η ^ 2 * t) (f x) ξ y * (E x y - (P.v - η ^ 2 * t)) ^ 2
  let enerX (t : ℝ) (x : Fin n → Covariate d) : ℝ :=
    ∑ ξ : Fin m → Fin 3, activationProductPrior m t ξ *
      ∑ y : Fin n → Fin 3, finiteResponseLikelihood m n P.a (P.v - η ^ 2 * t) (f x) ξ y *
        finiteExperimentScore m n P.a (P.v - η ^ 2 * t) η (f x) ξ y ^ 2
  have hrisk_nn (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : Fin n → Covariate d) : 0 ≤ riskX t x :=
    Finset.sum_nonneg fun ξ _ => mul_nonneg (Finset.prod_nonneg fun j _ => activation_prior_nonnegative t ht.1 ht.2 (ξ j))
      (Finset.sum_nonneg fun y _ => mul_nonneg (hL_pos t ht x ξ y).le (sq_nonneg _))
  have hener_nn (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : Fin n → Covariate d) : 0 ≤ enerX t x :=
    Finset.sum_nonneg fun ξ _ => mul_nonneg (Finset.prod_nonneg fun j _ => activation_prior_nonnegative t ht.1 ht.2 (ξ j))
      (Finset.sum_nonneg fun y _ => mul_nonneg (hL_pos t ht x ξ y).le (sq_nonneg _))
  have htm_cont (c₀ a₀ : ℝ) (y : Fin 3) : Continuous fun t : ℝ => ternaryMass a₀ c₀ (P.v - η ^ 2 * t) y := by
    fin_cases y <;> simp [ternaryMass] <;> fun_prop
  have hprior_cont (ξ : Fin m → Fin 3) : Continuous fun t => activationProductPrior m t ξ :=
    continuous_iff_continuousAt.mpr fun t => (activation_product_prior_hasDerivAt m t ξ).continuousAt
  have hL_cont (x : Fin n → Covariate d) (ξ : Fin m → Fin 3) (y : Fin n → Fin 3) :
      Continuous fun t => finiteResponseLikelihood m n P.a (P.v - η ^ 2 * t) (f x) ξ y :=
    continuous_finsetProd _ fun i _ => htm_cont (f x ξ i) P.a (y i)
  have hnum_cont (x : Fin n → Covariate d) (ξ : Fin m → Fin 3) (y : Fin n → Fin 3) :
      Continuous fun t => finiteExperimentScoreNumerator m n P.a (P.v - η ^ 2 * t) η (f x) ξ y := by
    unfold finiteExperimentScoreNumerator latentDifference finiteResponseVarianceTerm
    refine (continuous_finsetSum _ fun _ _ => ?_).sub (continuous_const.mul (continuous_finsetSum _ fun _ _ => ?_))
    · exact ((continuous_const.mul (hL_cont x _ y)).add (continuous_const.mul (hL_cont x _ y))).sub (hL_cont x _ y)
    · exact continuous_const.mul (continuous_finsetProd _ fun l _ => htm_cont (f x ξ l) P.a (y l))
  have hrisk_cont (x : Fin n → Covariate d) : Continuous fun t => riskX t x :=
    continuous_finsetSum _ fun ξ _ => (hprior_cont ξ).mul <|
      continuous_finsetSum _ fun y _ => (hL_cont x ξ y).mul (by fun_prop)
  have hener_contOn (x : Fin n → Covariate d) : ContinuousOn (fun t => enerX t x) (Icc 0 1) :=
    continuousOn_finsetSum _ fun ξ _ => (hprior_cont ξ).continuousOn.mul <| by
      unfold finiteExperimentScore
      exact continuousOn_finsetSum _ fun y _ => (hL_cont x ξ y).continuousOn.mul
        (((hnum_cont x ξ y).continuousOn.div (hL_cont x ξ y).continuousOn fun t ht => (hL_pos t ht x ξ y).ne').pow 2)
  -- Factored weighted AM-GM bound over `(ξ, y)`
  have hamgm {r t : ℝ} (hr : 0 < r) (ht : t ∈ Icc (0 : ℝ) 1) (x : Fin n → Covariate d)
      (B : (Fin m → Fin 3) → (Fin n → Fin 3) → ℝ) :
      2 * r * |∑ ξ : Fin m → Fin 3, activationProductPrior m t ξ *
        ∑ y : Fin n → Fin 3, finiteResponseLikelihood m n P.a (P.v - η ^ 2 * t) (f x) ξ y *
          (E x y - (P.v - η ^ 2 * t)) * B ξ y| ≤
        riskX t x + r ^ 2 * ∑ ξ : Fin m → Fin 3, activationProductPrior m t ξ *
          ∑ y : Fin n → Fin 3, finiteResponseLikelihood m n P.a (P.v - η ^ 2 * t) (f x) ξ y * (B ξ y) ^ 2 := by
    calc 2 * r * |∑ ξ, _|
      _ ≤ 2 * r * ∑ ξ, |activationProductPrior m t ξ * ∑ y, _| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs ..) (by positivity)
      _ ≤ ∑ ξ, activationProductPrior m t ξ * ∑ y, finiteResponseLikelihood m n P.a (P.v - η ^ 2 * t) (f x) ξ y *
            ((E x y - (P.v - η ^ 2 * t)) ^ 2 + r ^ 2 * (B ξ y) ^ 2) := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun ξ _ => ?_
          have hp_nn : 0 ≤ activationProductPrior m t ξ :=
            Finset.prod_nonneg fun j _ => activation_prior_nonnegative t ht.1 ht.2 (ξ j)
          rw [abs_mul, abs_of_nonneg hp_nn, ← mul_assoc, mul_comm (2 * r), mul_assoc]
          refine mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs ..) (by positivity)).trans ?_) hp_nn
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun y _ => ?_
          rw [mul_assoc (finiteResponseLikelihood m n P.a (P.v - η ^ 2 * t) (f x) ξ y),
            abs_mul, abs_of_nonneg (hL_pos t ht x ξ y).le, ← mul_assoc, mul_comm (2 * r), mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (by rw [abs_mul]; nlinarith [sq_abs (E x y - (P.v - η ^ 2 * t)), sq_abs (B ξ y),
              sq_nonneg (|E x y - (P.v - η ^ 2 * t)| - r * |B ξ y|)])
            (hL_pos t ht x ξ y).le
      _ = _ := by
          dsimp [riskX]
          simp_rw [mul_add, Finset.sum_add_distrib, mul_add, Finset.sum_add_distrib]
          rw [Finset.mul_sum]; congr 1; refine Finset.sum_congr rfl fun ξ _ => ?_
          simp_rw [← mul_assoc, mul_comm _ (r ^ 2), mul_assoc]
          rw [← Finset.mul_sum, ← mul_assoc, mul_comm _ (r ^ 2), mul_assoc]
  have hpt_amgm (r : ℝ) (hr : 0 < r) (x : Fin n → Covariate d) :
      2 * r * η ^ 2 ≤ riskX 0 x + riskX 1 x + (∫ t in (0 : ℝ)..1, riskX t x) +
        r ^ 2 * (2 + ∫ t in (0 : ℝ)..1, enerX t x) := by
    let g (t : ℝ) : ℝ := finiteExperimentExpectation m n P.a P.v η t (f x) (E x)
    let g' (t : ℝ) : ℝ := ∑ ξ : Fin m → Fin 3, activationProductPrior m t ξ *
      ∑ y : Fin n → Fin 3, finiteResponseLikelihood m n P.a (P.v - η ^ 2 * t) (f x) ξ y *
        E x y * finiteExperimentScore m n P.a (P.v - η ^ 2 * t) η (f x) ξ y
    have hg'_cont : ContinuousOn g' (Icc 0 1) := by
      have heq : EqOn g' (fun t => ∑ ξ : Fin m → Fin 3, activationProductPrior m t ξ *
          ∑ y : Fin n → Fin 3, E x y * finiteExperimentScoreNumerator m n P.a (P.v - η ^ 2 * t) η (f x) ξ y) (Icc 0 1) :=
        fun t ht => Finset.sum_congr rfl fun ξ _ => congrArg (activationProductPrior m t ξ * ·)
          (Finset.sum_congr rfl fun y _ => by
            unfold finiteExperimentScore
            have hne : finiteResponseLikelihood m n P.a (P.v - η ^ 2 * t) (f x) ξ y ≠ 0 := (hL_pos t ht x ξ y).ne'
            field_simp [hne])
      exact (continuous_finsetSum _ fun ξ _ => (hprior_cont ξ).mul
        (continuous_finsetSum _ fun y _ => continuous_const.mul (hnum_cont x ξ y))).continuousOn.congr heq
    have hftc : (∫ t in (0 : ℝ)..1, g' t) = g 1 - g 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (by simpa [uIcc_of_le zero_le_one] using fun t ht =>
          finite_experiment_observable_score_hasDerivAt m n P.a P.v η t (f x) (E x) (hL_pos t ht x))
        (hg'_cont.intervalIntegrable_of_Icc zero_le_one)
    have hg'_bound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 2 * r * |g' t| ≤ riskX t x + r ^ 2 * enerX t x := by
      rw [show g' t = ∑ ξ : Fin m → Fin 3, activationProductPrior m t ξ *
          ∑ y : Fin n → Fin 3, finiteResponseLikelihood m n P.a (P.v - η ^ 2 * t) (f x) ξ y *
            (E x y - (P.v - η ^ 2 * t)) * finiteExperimentScore m n P.a (P.v - η ^ 2 * t) η (f x) ξ y by
        dsimp [g']; refine Finset.sum_congr rfl fun ξ _ => congrArg (activationProductPrior m t ξ * ·) ?_
        have hc := finite_experiment_score_centered m n P.a (P.v - η ^ 2 * t) η (f x) ξ P.a_pos.ne' (hL_pos t ht x ξ)
        rw [show (∑ y, finiteResponseLikelihood m n P.a (P.v - η ^ 2 * t) (f x) ξ y * E x y *
            finiteExperimentScore m n P.a (P.v - η ^ 2 * t) η (f x) ξ y) =
          (∑ y, finiteResponseLikelihood m n P.a (P.v - η ^ 2 * t) (f x) ξ y * (E x y - (P.v - η ^ 2 * t)) *
            finiteExperimentScore m n P.a (P.v - η ^ 2 * t) η (f x) ξ y) +
          (P.v - η ^ 2 * t) * ∑ y, finiteResponseLikelihood m n P.a (P.v - η ^ 2 * t) (f x) ξ y *
            finiteExperimentScore m n P.a (P.v - η ^ 2 * t) η (f x) ξ y by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun _ _ => by ring, hc, mul_zero, add_zero]]
      exact hamgm hr ht x (finiteExperimentScore m n P.a (P.v - η ^ 2 * t) η (f x))
    have hend (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 2 * r * |g t - (P.v - η ^ 2 * t)| ≤ riskX t x + r ^ 2 := by
      rw [show g t - (P.v - η ^ 2 * t) = ∑ ξ : Fin m → Fin 3, activationProductPrior m t ξ *
          ∑ y : Fin n → Fin 3, finiteResponseLikelihood m n P.a (P.v - η ^ 2 * t) (f x) ξ y * (E x y - (P.v - η ^ 2 * t)) * 1 by
        dsimp [g, finiteExperimentExpectation]
        simp_rw [mul_one, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
          finite_response_normalized m n P.a _ (f x) _ P.a_pos.ne', one_mul,
          mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, activation_product_prior_normalized, one_mul]]
      refine (hamgm hr ht x fun _ _ => 1).trans_eq ?_
      simp only [one_pow, mul_one, finite_response_normalized m n P.a _ (f x) _ P.a_pos.ne',
        activation_product_prior_normalized]
    have hrI := (hrisk_cont x).intervalIntegrable (μ := volume) 0 1
    have heI := (hener_contOn x).intervalIntegrable_of_Icc (μ := volume) zero_le_one
    have hint_le : 2 * r * |g 1 - g 0| ≤ (∫ t in (0 : ℝ)..1, riskX t x) + r ^ 2 * (∫ t in (0 : ℝ)..1, enerX t x) := by
      have h1 := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := g') zero_le_one
      rw [hftc, Real.norm_eq_abs] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * r)
      rw [← intervalIntegral.integral_const_mul] at h2
      exact h2.trans ((intervalIntegral.integral_mono_on zero_le_one
        ((hg'_cont.norm.const_mul (2 * r)).intervalIntegrable_of_Icc (μ := volume) zero_le_one)
        (hrI.add (heI.const_mul (r ^ 2)))
        fun t ht => by simpa [Real.norm_eq_abs] using hg'_bound t ht).trans_eq
        (by rw [intervalIntegral.integral_add hrI (heI.const_mul (r ^ 2)), intervalIntegral.integral_const_mul]))
    have htri : η ^ 2 ≤ |g 1 - (P.v - η ^ 2 * 1)| + |g 1 - g 0| + |g 0 - (P.v - η ^ 2 * 0)| := by
      have hsep_v : |(P.v - η ^ 2 * 1) - (P.v - η ^ 2 * 0)| = η ^ 2 := by simp [abs_of_nonneg (sq_nonneg η)]
      have hsub1 := abs_sub_le (P.v - η ^ 2 * 1) (g 1) (P.v - η ^ 2 * 0)
      have hsub2 := abs_sub_le (g 1) (g 0) (P.v - η ^ 2 * 0)
      rw [abs_sub_comm (P.v - η ^ 2 * 1) (g 1)] at hsub1; linarith
    nlinarith [hend 0 ⟨le_rfl, zero_le_one⟩, hend 1 ⟨zero_le_one, le_rfl⟩,
      mul_le_mul_of_nonneg_left htri (by positivity : 0 ≤ 2 * r)]
  have hrisk_int_le (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (∫⁻ x, ENNReal.ofReal (riskX t x) ∂ν) ≤ worstCaseRisk C T := by
    have hstate (ξ : Fin m → Fin 3) :
        (∫⁻ x, ENNReal.ofReal (∑ y : Fin n → Fin 3,
          finiteResponseLikelihood m n P.a (P.v - η ^ 2 * t) (f x) ξ y * (E x y - (P.v - η ^ 2 * t)) ^ 2) ∂ν) ≤ worstCaseRisk C T := by
      obtain ⟨θ, hθ, hθV, hp_ξ, hθ_eq⟩ := hadm t ht ξ
      refine le_trans ?_ (meanSquaredRisk_le_worstCaseRisk C T θ hθ)
      have hmap := uniformTernaryParameter_sample_index_map n P.a (P.v - η ^ 2 * t)
        (F ξ) (hF_cont ξ).measurable P.a_pos.ne' hp_ξ
      have hm_loss : Measurable fun z : Fin n → Observation d => ENNReal.ofReal ((T.val z - (P.v - η ^ 2 * t)) ^ 2) :=
        ENNReal.measurable_ofReal.comp ((T.property.sub_const _).pow_const 2)
      let _ := responseSampleIndexKernel_markov n P.a (P.v - η ^ 2 * t) (F ξ) (hF_cont ξ).measurable P.a_pos.ne' hp_ξ
      rw [meanSquaredRisk, hθV, hθ_eq, ← hmap, lintegral_map hm_loss (encodeDesignResponse_measurable P.a),
        Measure.lintegral_compProd (f := fun a => ENNReal.ofReal ((T.val (encodeDesignResponse P.a a) - (P.v - η ^ 2 * t)) ^ 2))
          (hm_loss.comp (encodeDesignResponse_measurable P.a))]
      refine le_of_eq (lintegral_congr fun x => ?_)
      rw [responseSampleIndexKernel_apply, lintegral_finsetSum_measure,
        ENNReal.ofReal_sum_of_nonneg fun y _ => mul_nonneg (hL_pos t ht x ξ y).le (sq_nonneg _)]
      exact Finset.sum_congr rfl fun y _ => by
        rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul, ENNReal.ofReal_mul (hL_pos t ht x ξ y).le]; rfl
    have hm_y (ξ : Fin m → Fin 3) (y : Fin n → Fin 3) :
        Measurable fun x => finiteResponseLikelihood m n P.a (P.v - η ^ 2 * t) (f x) ξ y * (E x y - (P.v - η ^ 2 * t)) ^ 2 :=
      (Finset.measurable_fun_prod _ fun i _ => ternaryMass_measurable_comp P.a _ _
        (((hF_cont ξ).comp (continuous_apply i)).measurable) (y i)).mul
        (((T.property.comp (encodeDesignResponse_measurable P.a)).comp
          (measurable_id.prodMk measurable_const)).sub_const _ |>.pow_const 2)
    have hpri_nn (ξ : Fin m → Fin 3) : 0 ≤ activationProductPrior m t ξ :=
      Finset.prod_nonneg fun j _ => activation_prior_nonnegative t ht.1 ht.2 (ξ j)
    simp_rw [show (fun x => ENNReal.ofReal (riskX t x)) = fun x => ∑ ξ : Fin m → Fin 3, ENNReal.ofReal (activationProductPrior m t ξ) *
        ENNReal.ofReal (∑ y, finiteResponseLikelihood m n P.a (P.v - η ^ 2 * t) (f x) ξ y * (E x y - (P.v - η ^ 2 * t)) ^ 2) from
      funext fun x => by
        dsimp [riskX]
        rw [ENNReal.ofReal_sum_of_nonneg fun ξ _ => mul_nonneg (hpri_nn ξ)
          (Finset.sum_nonneg fun y _ => mul_nonneg (hL_pos t ht x ξ y).le (sq_nonneg _))]
        exact Finset.sum_congr rfl fun ξ _ => ENNReal.ofReal_mul (hpri_nn ξ)]
    rw [lintegral_finsetSum _ fun ξ _ => ((Finset.measurable_fun_sum _ fun y _ => hm_y ξ y).ennreal_ofReal).const_mul _]
    refine (Finset.sum_le_sum (g := fun ξ => ENNReal.ofReal (activationProductPrior m t ξ) * worstCaseRisk C T) fun ξ _ => ?_).trans_eq
      (by rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun ξ _ => hpri_nn ξ,
            activation_product_prior_normalized, ENNReal.ofReal_one, one_mul])
    rw [lintegral_const_mul _ (Finset.measurable_fun_sum _ fun y _ => hm_y ξ y).ennreal_ofReal]
    exact mul_le_mul_of_nonneg_left (hstate ξ) zero_le
  have htm_jcont (a₀ : ℝ) (y : Fin 3) : Continuous fun z : ℝ × ℝ => ternaryMass a₀ z.1 z.2 y := by
    fin_cases y <;> simp [ternaryMass] <;> fun_prop
  have hq_jm (ξ' : Fin m → Fin 3) (i : Fin n) (y : Fin 3) :
      Measurable fun tx : ℝ × (Fin n → Covariate d) => ternaryMass P.a (F ξ' (tx.2 i)) (P.v - η ^ 2 * tx.1) y :=
    (htm_jcont P.a y).measurable.comp <| Measurable.prodMk
      ((hF_cont ξ').measurable.comp ((measurable_pi_apply i).comp (measurable_snd (α := ℝ) (β := Fin n → Covariate d))))
      (by fun_prop)
  have hL_jm (ξ' : Fin m → Fin 3) (y : Fin n → Fin 3) :
      Measurable fun tx : ℝ × (Fin n → Covariate d) => finiteResponseLikelihood m n P.a (P.v - η ^ 2 * tx.1) (f tx.2) ξ' y :=
    Finset.measurable_fun_prod _ fun i _ => hq_jm ξ' i (y i)
  have hrisk_jmeas : Measurable fun tx : ℝ × (Fin n → Covariate d) => riskX tx.1 tx.2 :=
    Finset.measurable_fun_sum _ fun ξ _ => ((hprior_cont ξ).measurable.comp measurable_fst).mul <|
      Finset.measurable_fun_sum _ fun y _ => (hL_jm ξ y).mul
        ((((T.property.comp (encodeDesignResponse_measurable P.a)).comp
          (measurable_snd.prodMk measurable_const)).sub (by fun_prop)).pow_const 2)
  have hener_jmeas : Measurable fun tx : ℝ × (Fin n → Covariate d) => enerX tx.1 tx.2 :=
    Finset.measurable_fun_sum _ fun ξ _ => ((hprior_cont ξ).measurable.comp measurable_fst).mul <|
      Finset.measurable_fun_sum _ fun y _ => (hL_jm ξ y).mul <|
        ((((Finset.measurable_fun_sum _ fun _ _ =>
          (((hL_jm _ y).const_mul _).add ((hL_jm _ y).const_mul _)).sub (hL_jm _ y)).sub
          ((Finset.measurable_fun_sum _ fun _ _ =>
            (Finset.measurable_fun_prod _ fun l _ => hq_jm ξ l (y l)).const_mul _).const_mul _)).div
          (hL_jm ξ y)).pow_const 2)
  have hconvR (x : Fin n → Covariate d) :
      ENNReal.ofReal (∫ t in (0 : ℝ)..1, riskX t x) = ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (riskX t x) := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact ofReal_integral_eq_lintegral_ofReal ((hrisk_cont x).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => hrisk_nn t ⟨ht.1.le, ht.2⟩ x)
  have hconvE (x : Fin n → Covariate d) :
      ENNReal.ofReal (∫ t in (0 : ℝ)..1, enerX t x) = ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (enerX t x) := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact ofReal_integral_eq_lintegral_ofReal ((hener_contOn x).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => hener_nn t ⟨ht.1.le, ht.2⟩ x)
  have hm_intR : Measurable fun x => ENNReal.ofReal (∫ t in (0 : ℝ)..1, riskX t x) := by
    simp_rw [hconvR]
    exact (hrisk_jmeas.ennreal_ofReal : Measurable (Function.uncurry fun t x => ENNReal.ofReal (riskX t x))).lintegral_prod_left'
  have hm_intE : Measurable fun x => ENNReal.ofReal (∫ t in (0 : ℝ)..1, enerX t x) := by
    simp_rw [hconvE]
    exact (hener_jmeas.ennreal_ofReal : Measurable (Function.uncurry fun t x => ENNReal.ofReal (enerX t x))).lintegral_prod_left'
  have hm_r0 : Measurable fun x => ENNReal.ofReal (riskX 0 x) :=
    (hrisk_jmeas.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hm_r1 : Measurable fun x => ENNReal.ofReal (riskX 1 x) :=
    (hrisk_jmeas.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hswap_risk : (∫⁻ x, ENNReal.ofReal (∫ t in (0 : ℝ)..1, riskX t x) ∂ν) ≤ worstCaseRisk C T := by
    simp_rw [hconvR]
    rw [lintegral_lintegral_swap ((hrisk_jmeas.comp measurable_swap).ennreal_ofReal :
      Measurable (Function.uncurry fun x t => ENNReal.ofReal (riskX t x))).aemeasurable]
    exact (setLIntegral_mono' measurableSet_Ioc (g := fun _ => worstCaseRisk C T) fun t ht => hrisk_int_le t ⟨ht.1.le, ht.2⟩).trans_eq
      (by simp [Real.volume_Ioc])
  have hswap_ener : (∫⁻ x, ENNReal.ofReal (∫ t in (0 : ℝ)..1, enerX t x) ∂ν) ≤ 1 := by
    simp_rw [hconvE]
    rw [lintegral_lintegral_swap ((hener_jmeas.comp measurable_swap).ennreal_ofReal :
      Measurable (Function.uncurry fun x t => ENNReal.ofReal (enerX t x))).aemeasurable]
    exact (setLIntegral_mono' measurableSet_Ioc (g := fun _ => (1 : ℝ≥0∞)) fun t ht => hener_le t ⟨ht.1.le, ht.2⟩).trans_eq
      (by simp [Real.volume_Ioc])
  have hmain_r (r : ℝ) (hr : 0 < r) :
      ENNReal.ofReal (2 * r * η ^ 2) ≤ 3 * worstCaseRisk C T + ENNReal.ofReal (3 * r ^ 2) := by
    calc ENNReal.ofReal (2 * r * η ^ 2)
      _ = ∫⁻ _x, ENNReal.ofReal (2 * r * η ^ 2) ∂ν := by simp
      _ ≤ ∫⁻ x, (ENNReal.ofReal (riskX 0 x) + ENNReal.ofReal (riskX 1 x) +
            ENNReal.ofReal (∫ t in (0 : ℝ)..1, riskX t x) +
            ENNReal.ofReal (r ^ 2) * (ENNReal.ofReal 2 + ENNReal.ofReal (∫ t in (0 : ℝ)..1, enerX t x))) ∂ν := by
          refine lintegral_mono fun x => (ENNReal.ofReal_le_ofReal (hpt_amgm r hr x)).trans_eq ?_
          have hiR0 : 0 ≤ ∫ t in (0 : ℝ)..1, riskX t x :=
            intervalIntegral.integral_nonneg zero_le_one fun t ht => hrisk_nn t ht x
          have hiE0 : 0 ≤ ∫ t in (0 : ℝ)..1, enerX t x :=
            intervalIntegral.integral_nonneg zero_le_one fun t ht => hener_nn t ht x
          have hr0 := hrisk_nn 0 ⟨le_rfl, zero_le_one⟩ x
          have hr1 := hrisk_nn 1 ⟨zero_le_one, le_rfl⟩ x
          rw [ENNReal.ofReal_add (add_nonneg (add_nonneg hr0 hr1) hiR0) (mul_nonneg (sq_nonneg r) (add_nonneg zero_le_two hiE0)),
            ENNReal.ofReal_add (add_nonneg hr0 hr1) hiR0,
            ENNReal.ofReal_add hr0 hr1, ENNReal.ofReal_mul (sq_nonneg r), ENNReal.ofReal_add zero_le_two hiE0]
      _ = (∫⁻ x, ENNReal.ofReal (riskX 0 x) ∂ν) + (∫⁻ x, ENNReal.ofReal (riskX 1 x) ∂ν) +
            (∫⁻ x, ENNReal.ofReal (∫ t in (0 : ℝ)..1, riskX t x) ∂ν) +
            ENNReal.ofReal (r ^ 2) * (ENNReal.ofReal 2 + ∫⁻ x, ENNReal.ofReal (∫ t in (0 : ℝ)..1, enerX t x) ∂ν) := by
          rw [lintegral_add_left (by fun_prop), lintegral_add_left (by fun_prop),
            lintegral_add_left hm_r0, lintegral_const_mul _ (by fun_prop),
            lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ worstCaseRisk C T + worstCaseRisk C T + worstCaseRisk C T + ENNReal.ofReal (r ^ 2) * (ENNReal.ofReal 2 + 1) := by
          gcongr
          · exact hrisk_int_le 0 ⟨le_rfl, zero_le_one⟩
          · exact hrisk_int_le 1 ⟨zero_le_one, le_rfl⟩
      _ = 3 * worstCaseRisk C T + ENNReal.ofReal (3 * r ^ 2) := by
          congr 1
          · ring
          · rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_two zero_le_one,
              ← ENNReal.ofReal_mul (sq_nonneg r)]; congr 1; ring
  by_cases htop : worstCaseRisk C T = ∞
  · simp [htop]
  · let W := (worstCaseRisk C T).toReal
    have hW0 : 0 ≤ W := ENNReal.toReal_nonneg
    have hWeq : worstCaseRisk C T = ENNReal.ofReal W := (ENNReal.ofReal_toReal htop).symm
    by_cases hWpos : 0 < W
    · have hm := hmain_r (Real.sqrt W) (Real.sqrt_pos.2 hWpos)
      rw [hWeq, Real.sq_sqrt hW0, ← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add (by positivity) (by positivity)] at hm
      have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hm
      change 2 * Real.sqrt W * η ^ 2 ≤ 3 * W + 3 * W at hreal
      have hle : η ^ 2 / 3 ≤ Real.sqrt W := by nlinarith [Real.sq_sqrt hW0, Real.sqrt_pos.2 hWpos]
      rw [hWeq]; exact ENNReal.ofReal_le_ofReal (by nlinarith [Real.sq_sqrt hW0])
    · have hWz : W = 0 := le_antisymm (not_lt.mp hWpos) hW0
      have hm := hmain_r (η ^ 2 / 3) (by positivity)
      rw [hWeq, hWz, ENNReal.ofReal_zero, mul_zero, zero_add] at hm
      nlinarith [(ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hm, sq_pos_of_pos hη]

private lemma low_smoothness_nonparametric_minimax_lower {d : ℕ} (C : ModelConstants d)
    (hs1 : C.smoothness ≤ 1) (hd : 4 * C.smoothness ≤ (d : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      ENNReal.ofReal (c * (n : ℝ) ^ (-4 * C.smoothness / ((d : ℝ) + 4 * C.smoothness))) ≤ minimaxRMS C n := by
  obtain ⟨P⟩ := lowSmoothnessTernaryConstants_exists C
  let M_c : ℝ := (2 : ℝ) ^ d + 2
  let H_c : ℝ := (2 : ℝ) ^ d + 68 * (2 : ℝ) ^ d * (d + 1)
  let K_exp : ℝ := ternaryScoreExponentialConstant P.a P.ρ P.c
  have hK_exp : 0 ≤ K_exp := by dsimp [K_exp, ternaryScoreExponentialConstant]; positivity
  let Q_c : ℝ := (40 : ℝ) ^ d * K_exp ^ 2 * Real.exp K_exp
  have hM_c : 0 < M_c := by positivity
  have hH_c : 0 < H_c := by positivity
  have hQ_c : 0 ≤ Q_c := by positivity
  let b : ℝ := min (min (min (min 1 (P.ρ / M_c)) (Real.sqrt P.ρ)) (C.holderBound / H_c)) (1 / (Q_c + 1))
  have hb : 0 < b := lt_min
    (lt_min (lt_min (lt_min zero_lt_one (div_pos P.ρ_pos hM_c)) (Real.sqrt_pos.mpr P.ρ_pos))
      (div_pos C.holderBound_pos hH_c)) (div_pos zero_lt_one (by linarith))
  have hbQ : b ≤ 1 / (Q_c + 1) := min_le_right _ _
  have hbH : b ≤ C.holderBound / H_c := (min_le_left _ _).trans (min_le_right _ _)
  have hbS : b ≤ Real.sqrt P.ρ := ((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _)
  have hbM : b ≤ P.ρ / M_c := (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _)).trans (min_le_right _ _)
  have hb1 : b ≤ 1 := (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _)).trans (min_le_left _ _)
  have hfield_b : M_c * b ≤ P.ρ := by have := (le_div_iff₀ hM_c).mp hbM; nlinarith
  have hvar_b : b ^ 2 ≤ P.ρ := by nlinarith [Real.sq_sqrt P.ρ_pos.le, Real.sqrt_nonneg P.ρ]
  have hhold_b : H_c * b ≤ C.holderBound := by have := (le_div_iff₀ hH_c).mp hbH; nlinarith
  have hscore_b : Q_c * b ^ 4 ≤ 1 := by
    have hb4 : b ^ 4 ≤ b := by
      calc b ^ 4 = b ^ 3 * b := by ring
        _ ≤ 1 * b := mul_le_mul_of_nonneg_right (pow_le_one₀ hb.le hb1) hb.le
        _ = b := one_mul b
    have := (le_div_iff₀ (by linarith : 0 < Q_c + 1)).mp hbQ
    exact (mul_le_mul_of_nonneg_left hb4 hQ_c).trans (by nlinarith)
  refine ⟨b ^ 2 / (3 * (5 : ℝ) ^ (2 * C.smoothness)), div_pos (sq_pos_of_pos hb) (by positivity), fun n hn => ?_⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let k := lowSmoothnessGrid d C.smoothness n
  let η := lowSmoothnessAmplitude d C.smoothness b n
  have hk4 := lowSmoothnessGrid_ge_four (d := d) C.smoothness_pos hnR
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hk0 : 0 < k := by omega
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk0
  have hη_pos : 0 < η := div_pos hb (Real.rpow_pos_of_pos hkr _)
  have hη : 0 ≤ η := hη_pos.le
  have hηb : η ≤ b := div_le_self hb.le (Real.one_le_rpow (by exact_mod_cast hk) C.smoothness_pos.le)
  have hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ := (mul_le_mul_of_nonneg_left hηb (by positivity)).trans hfield_b
  have hvariance : η ^ 2 ≤ P.ρ := (pow_le_pow_left₀ hη hηb 2).trans hvar_b
  have hmean : n * (2 / (k : ℝ)) ^ d ≤ 1 := lowSmoothness_design_occupancy C.smoothness_pos hd hnR
  have hbudget : Q_c * n ^ 2 * η ^ 4 / (k : ℝ) ^ d ≤ 1 :=
    (le_of_eq (by dsimp [k, η]; ring)).trans
      ((mul_le_mul_of_nonneg_left (lowSmoothness_numeric_score_budget (d := d) C.smoothness_pos hnR) hQ_c).trans hscore_b)
  let m := (k + 1) ^ d
  have horder : C.order = 0 := by
    have : C.order < 1 := by exact_mod_cast C.order_lt.trans_le hs1
    omega
  have hmr : ENNReal.ofReal ((η ^ 2 / 3) ^ 2) ≤ minimaxRisk C n := by
    refine finite_prior_amgm_minimax_lower (m := m) C P η hη_pos
      (indexedGridField d k η) (indexedGridField_continuous d k η)
      (fun t ht ξ => ⟨P.pathParameter (indexedGridField d k η ξ) (indexedGridField_continuous d k η ξ) η t ht hvariance
          fun x => (indexedGridField_abs_bound d k η hη ξ x).trans (by nlinarith),
        P.pathParameter_admissible_order_zero _ _ η t ht hvariance _ horder
          ((2 : ℝ) ^ d * b) ((68 * (2 : ℝ) ^ d * (d + 1)) * b) (by positivity) (by positivity)
          (by dsimp [H_c] at hhold_b; nlinarith)
          (fun x => (indexedGridField_abs_bound d k η hη ξ x).trans (mul_le_mul_of_nonneg_left hηb (by positivity)))
          (fun x y => indexedGridField_holder_bound d k C.smoothness b hk C.smoothness_pos.le hs1 hb.le ξ x y),
        rfl, fun x y => P.c_pos.le.trans ((P.path_legality η t _ ht hvariance
          ((indexedGridField_abs_bound d k η hη ξ x).trans (by nlinarith))).2.2.1 y), rfl⟩)
      (fun t ht x ξ y => Finset.prod_pos fun i _ => P.c_pos.trans_le ((P.path_legality η t _ ht hvariance
        ((indexedGridField_abs_bound d k η hη ξ (x i)).trans (by nlinarith))).2.2.1 (y i)))
      fun t ht => ?_
    let _ := cubeVolume_isProbability d
    let ν := Measure.pi fun _ : Fin n => cubeVolume d
    let _ : IsProbabilityMeasure ν := inferInstance
    let e : ℕ → ℝ := fun c => if 2 ≤ c then K_exp ^ c * η ^ 4 else 0
    have he_nn (c : ℕ) : 0 ≤ e c := by dsimp [e]; split_ifs <;> positivity
    let w (x : Fin n → Covariate d) (i : Fin n) (j : Fin m) : ℝ :=
      gridTensorWindow d k (indexedGridEquiv d k j) (x i)
    have hf_lat (x : Fin n → Covariate d) :
        (fun ξ' i => indexedGridField d k η ξ' (x i)) = latentRegression m n η (fun _ => 0) (w x) := by
      funext ξ' i; simp [latentRegression, indexedGridField, w, m]
    have hpt_ξ (x : Fin n → Covariate d) (ξ : Fin m → Fin 3) :
        (∑ y : Fin n → Fin 3, finiteResponseLikelihood m n P.a (P.v - η ^ 2 * t) (fun ξ' i => indexedGridField d k η ξ' (x i)) ξ y *
          finiteExperimentScore m n P.a (P.v - η ^ 2 * t) η (fun ξ' i => indexedGridField d k η ξ' (x i)) ξ y ^ 2) ≤
          (5 : ℝ) ^ d * ∑ j : Fin m, e (designPatchCount n (gridPatch d k (indexedGridEquiv d k j)) x) := by
      rw [hf_lat x]
      have hw_sq (i : Fin n) : ∑ j : Fin m, w x i j ^ 2 = 1 :=
        (Fintype.sum_equiv (indexedGridEquiv d k) (fun j => w x i j ^ 2) (fun j => gridTensorWindow d k j (x i) ^ 2) fun _ => rfl).trans <| by
          simp only [gridTensorWindow, ← Finset.prod_pow, ← Fintype.prod_sum fun r (j : Fin (k + 1)) => gridWindow k j (x i r) ^ 2,
            gridWindow_square_partition, Finset.prod_const_one]
      have hdeg (j : Fin m) :
          (Finset.univ.filter fun l : Fin m =>
            ¬Disjoint (Finset.univ.filter fun i => x i ∈ gridPatch d k (indexedGridEquiv d k j))
              (Finset.univ.filter fun i => x i ∈ gridPatch d k (indexedGridEquiv d k l))).card ≤ 5 ^ d := by
        rw [Finset.card_equiv (indexedGridEquiv d k) (t := Finset.univ.filter fun l =>
          ¬Disjoint (Finset.univ.filter fun i => x i ∈ gridPatch d k (indexedGridEquiv d k j))
            (Finset.univ.filter fun i => x i ∈ gridPatch d k l)) fun _ => by simp]
        exact grid_observed_patch_degree d k n x _
      have hp_pos (i : Fin n) (y : Fin 3) : 0 < ternaryMass P.a (latentRegression m n η (fun _ => 0) (w x) ξ i) (P.v - η ^ 2 * t) y := by
        rw [← congrFun (congrFun (hf_lat x) ξ) i]
        exact P.c_pos.trans_le ((P.path_legality η t _ ht hvariance
          ((indexedGridField_abs_bound d k η hη ξ (x i)).trans (by nlinarith))).2.2.1 y)
      have hfull := latent_full_score_variance_bound m n P.a (P.v - η ^ 2 * t) η (fun _ => 0) (w x) ξ
        (fun j => Finset.univ.filter fun i => x i ∈ gridPatch d k (indexedGridEquiv d k j)) (5 ^ d)
        (fun j i hi => gridTensorWindow_zero_outside_patch d k _ (x i) fun hm => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hm⟩))
        hw_sq hdeg P.a_pos.ne' hp_pos
      simp_rw [ternary_index_product_integral] at hfull
      change _ ≤ ((5 ^ d : ℕ) : ℝ) * ∑ j : Fin m, ∑ y, finiteResponseLikelihood m n P.a (P.v - η ^ 2 * t) (latentRegression m n η (fun _ => 0) (w x)) ξ y *
        finiteCoordinateScore m n P.a (P.v - η ^ 2 * t) η (latentRegression m n η (fun _ => 0) (w x)) (w x) ξ y j ^ 2 at hfull
      push_cast at hfull
      refine hfull.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (by positivity))
      rw [show (∑ y : Fin n → Fin 3, finiteResponseLikelihood m n P.a (P.v - η ^ 2 * t) (latentRegression m n η (fun _ => 0) (w x)) ξ y *
          finiteCoordinateScore m n P.a (P.v - η ^ 2 * t) η (latentRegression m n η (fun _ => 0) (w x)) (w x) ξ y j ^ 2) =
          patchExpectedScoreEnergy n P.a (P.v - η ^ 2 * t) η
            (latentRegressionWithout m n η (fun _ => 0) (w x) ξ j) (fun i => w x i j) (ternaryValue 1 (ξ j)) from
        Finset.sum_congr rfl fun y _ => by
          rw [latent_coordinate_score_eq_patch]; congr 1
          simp only [finiteResponseLikelihood, patchResponseProduct]
          simp_rw [latent_regression_decomposition m n η (fun _ => 0) (w x) ξ j]]
      let g_ex := latentRegressionWithout m n η (fun _ => 0) (w x) ξ j
      let z := ternaryValue 1 (ξ j)
      have hz : z ∈ Icc (-1 : ℝ) 1 := abs_le.mp (ternaryValue_one_abs_le (ξ j))
      have hw_le (i : Fin n) : |w x i j| ≤ 1 := by
        dsimp [w]; rw [abs_of_nonneg (gridTensorWindow_nonneg ..)]; exact gridTensorWindow_le_one ..
      have hreg_u (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) (i : Fin n) : |g_ex i + η * w x i j * u| ≤ P.ρ := by
        have hdz : |u - z| ≤ 2 := by
          have := abs_sub_le u 0 z; simp only [sub_zero, zero_sub, abs_neg] at this
          linarith [abs_le.mpr hu, abs_le.mpr hz]
        have hl := latent_regression_decomposition m n η (fun _ => 0) (w x) ξ j i
        rw [← congrFun (congrFun (hf_lat x) ξ) i] at hl
        rw [show g_ex i + η * w x i j * u = indexedGridField d k η ξ (x i) + η * w x i j * (u - z) by dsimp [g_ex, z] at *; linarith]
        have ht1 : |η * w x i j * (u - z)| ≤ 2 * η := by
          rw [abs_mul, abs_mul, abs_of_nonneg hη]
          simpa only [one_mul, mul_comm] using
            mul_le_mul (mul_le_mul_of_nonneg_left (hw_le i) hη) hdz (abs_nonneg _) (by positivity : 0 ≤ η * 1)
        exact (abs_add_le _ _).trans (by nlinarith [indexedGridField_abs_bound d k η hη ξ (x i)])
      have hp_u (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) (i : Fin n) (y : Fin 3) :
          0 < ternaryMass P.a (g_ex i + η * w x i j * u) (P.v - η ^ 2 * t) y :=
        P.c_pos.trans_le ((P.path_legality η t _ ht hvariance (hreg_u u hu i)).2.2.1 y)
      let S := Finset.univ.filter fun i : Fin n => x i ∈ gridPatch d k (indexedGridEquiv d k j)
      simpa [e, K_exp, designPatchCount, S] using patch_expected_score_energy_support_bound n P.a (P.v - η ^ 2 * t) η z P.ρ P.c
        g_ex (fun i => w x i j) S P.a_pos P.ρ_pos.le P.c_pos hz
        (fun i hi => gridTensorWindow_zero_outside_patch d k _ (x i) fun hm => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hm⟩))
        (fun i _ => hw_le i) (fun u hu i _ => hreg_u u hu i)
        (fun u hu i _ y => ⟨(hp_u u hu i y).le, ternary_mass_le_one P.a _ _ P.a_pos.ne' (fun y' => (hp_u u hu i y').le) y⟩)
        (fun i _ y => (P.path_legality η t _ ht hvariance (hreg_u z hz i)).2.2.1 y)
        (fun i y => hp_u z hz i y)
    have hpt_all (x : Fin n → Covariate d) :
        (∑ ξ : Fin m → Fin 3, activationProductPrior m t ξ *
          ∑ y : Fin n → Fin 3, finiteResponseLikelihood m n P.a (P.v - η ^ 2 * t) (fun ξ' i => indexedGridField d k η ξ' (x i)) ξ y *
            finiteExperimentScore m n P.a (P.v - η ^ 2 * t) η (fun ξ' i => indexedGridField d k η ξ' (x i)) ξ y ^ 2) ≤
          (5 : ℝ) ^ d * ∑ j : Fin m, e (designPatchCount n (gridPatch d k (indexedGridEquiv d k j)) x) :=
      (Finset.sum_le_sum (g := fun ξ => activationProductPrior m t ξ *
          ((5 : ℝ) ^ d * ∑ j : Fin m, e (designPatchCount n (gridPatch d k (indexedGridEquiv d k j)) x)))
        fun ξ _ => mul_le_mul_of_nonneg_left (hpt_ξ x ξ)
          (Finset.prod_nonneg fun r _ => activation_prior_nonnegative t ht.1 ht.2 (ξ r))).trans_eq
        (by rw [← Finset.sum_mul, activation_product_prior_normalized, one_mul])
    have hpatch_int (j : Fin m) :
        (∫⁻ x, ENNReal.ofReal (e (designPatchCount n (gridPatch d k (indexedGridEquiv d k j)) x)) ∂ν) ≤
          ENNReal.ofReal (K_exp ^ 2 * Real.exp K_exp * η ^ 4 * (n * (2 / (k : ℝ)) ^ d) ^ 2) := by
      let A := gridPatch d k (indexedGridEquiv d k j)
      have hA := gridPatch_measurable d k (indexedGridEquiv d k j)
      have hI : Integrable (fun x => e (designPatchCount n A x)) ν :=
        Integrable.of_bound ((measurable_of_countable e).comp (design_patch_count_measurable n A hA)).aestronglyMeasurable
          (∑ c ∈ Finset.range (n + 1), e c) (Eventually.of_forall fun x => by
            rw [Real.norm_eq_abs, abs_of_nonneg (he_nn _)]
            exact Finset.single_le_sum (fun c _ => he_nn c) (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (design_patch_count_le n A x))))
      rw [← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun _ => he_nn _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hvol := gridPatch_cube_probability_bound d k (indexedGridEquiv d k j) hk0
      have hmA : n * (cubeVolume d).real A ≤ 1 := (mul_le_mul_of_nonneg_left hvol (Nat.cast_nonneg n)).trans hmean
      exact (iid_design_collision_energy_bound (cubeVolume d) n A hA K_exp η e hK_exp hmA
        (by simp [e]) (by simp [e]) fun c hc => by simp [e, hc]).trans (by gcongr)
    have hm_j (j : Fin m) : Measurable fun x => ENNReal.ofReal (e (designPatchCount n (gridPatch d k (indexedGridEquiv d k j)) x)) :=
      ((measurable_of_countable e).comp (design_patch_count_measurable n _ (gridPatch_measurable d k _))).ennreal_ofReal
    calc (∫⁻ x, ENNReal.ofReal _ ∂ν)
      _ ≤ ∫⁻ x, ENNReal.ofReal ((5 : ℝ) ^ d * ∑ j : Fin m, e (designPatchCount n (gridPatch d k (indexedGridEquiv d k j)) x)) ∂ν :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hpt_all x)
      _ = ENNReal.ofReal ((5 : ℝ) ^ d) * ∑ j : Fin m, ∫⁻ x, ENNReal.ofReal (e (designPatchCount n (gridPatch d k (indexedGridEquiv d k j)) x)) ∂ν := by
          simp_rw [ENNReal.ofReal_mul (show 0 ≤ (5 : ℝ) ^ d by positivity), ENNReal.ofReal_sum_of_nonneg fun j _ => he_nn _]
          rw [lintegral_const_mul _ (Finset.measurable_fun_sum _ fun j _ => hm_j j), lintegral_finsetSum _ fun j _ => hm_j j]
      _ ≤ ENNReal.ofReal ((5 : ℝ) ^ d) * ∑ _j : Fin m, ENNReal.ofReal (K_exp ^ 2 * Real.exp K_exp * η ^ 4 * (n * (2 / (k : ℝ)) ^ d) ^ 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hpatch_int j) zero_le
      _ ≤ 1 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast m, ← ENNReal.ofReal_mul (Nat.cast_nonneg m),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal (le_trans ?_ hbudget)
          have hm_le : (m : ℝ) ≤ (2 * (k : ℝ)) ^ d := by
            have hk1 : (k : ℝ) + 1 ≤ 2 * k := by exact_mod_cast (by omega : k + 1 ≤ 2 * k)
            simpa only [m, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using pow_le_pow_left₀ (by positivity) hk1 d
          refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm_le (by positivity)) (by positivity)).trans_eq ?_
          dsimp [Q_c]; rw [show (40 : ℝ) = 5 * 2 ^ 3 by norm_num]
          simp only [mul_pow, div_pow, show ((2 : ℝ) ^ 3) ^ d = ((2 : ℝ) ^ d) ^ 3 by rw [← pow_mul, ← pow_mul, Nat.mul_comm 3 d]]
          field_simp [hkr.ne']
  have hsep := lowSmoothness_variance_separation (d := d) (b := b) C.smoothness_pos hnR
  have hsc : b ^ 2 / (3 * (5 : ℝ) ^ (2 * C.smoothness)) *
      (n : ℝ) ^ (-4 * C.smoothness / ((d : ℝ) + 4 * C.smoothness)) ≤ η ^ 2 / 3 :=
    (le_of_eq (by ring)).trans (div_le_div_of_nonneg_right hsep (by norm_num))
  refine (ENNReal.ofReal_le_ofReal hsc).trans ?_
  unfold minimaxRMS
  refine le_trans ?_ (ENNReal.rpow_le_rpow hmr (by norm_num))
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
    Real.sqrt_sq (by positivity : 0 ≤ η ^ 2 / 3)]

end LowSmoothnessLowerBound

-- ============================================================================
-- 3. Parametric Projection Upper Bound & All Five Main Paper Endpoints
-- ============================================================================

section ParametricAndMainEndpoints
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private lemma independent_error_product_memLp_two {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ε : ι → Ω → ℝ) (hε : ∀ i, MemLp (ε i) 4 μ) (i j : ι) :
    MemLp (fun ω => ε i ω * ε j ω) 2 μ := by
  let _ : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [← two_mul, show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp),
      ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]⟩
  convert (hε j).mul (r := 2) (hε i) using 1; funext ω; simp [mul_comm]

private lemma independent_error_product_covariance {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ε : ι → Ω → ℝ) (hind : iIndepFun ε μ) (hε : ∀ i, MemLp (ε i) 4 μ)
    (hmean : ∀ i, (∫ ω, ε i ω ∂μ) = 0) (V : ℝ)
    (hsecond : ∀ i, (∫ ω, ε i ω ^ 2 ∂μ) = V) (i j k l : ι) :
    covariance (fun ω => ε i ω * ε j ω) (fun ω => ε k ω * ε l ω) μ =
      (if i = k ∧ j = l then (if i = j then (∫ ω, ε i ω ^ 4 ∂μ) - V ^ 2 else V ^ 2) else 0) +
      (if i = l ∧ j = k ∧ i ≠ j then V ^ 2 else 0) := by
  have hlist (xs : List ι) :
      (∫ ω, (xs.map (ε · ω)).prod ∂μ) = ∏ a ∈ xs.toFinset, ∫ ω, ε a ω ^ xs.count a ∂μ := by
    have hid (ω) : (xs.map (ε · ω)).prod = ∏ a : ι, ε a ω ^ xs.count a :=
      (Finset.prod_list_map_count ..).trans (Finset.prod_subset (Finset.subset_univ _)
        fun _ _ h => by rw [List.count_eq_zero.2 (by simpa using h), pow_zero])
    simp_rw [hid]
    have hiPow : iIndepFun (fun a ω => ε a ω ^ xs.count a) μ :=
      hind.comp (fun a z => z ^ xs.count a) fun _ => measurable_id.pow_const _
    rw [hiPow.integral_fun_prod_eq_prod_integral fun a => (hε a).aestronglyMeasurable.pow _]
    exact (Finset.prod_subset (Finset.subset_univ _) fun _ _ h => by simp [List.count_eq_zero.2 (by simpa using h)]).symm
  have h4 : (∫ ω, ε i ω * ε j ω * ε k ω * ε l ω ∂μ) =
      if i = j then if k = l then (if i = k then (∫ ω, ε i ω ^ 4 ∂μ) else V ^ 2) else 0
      else if i = k ∧ j = l then V ^ 2 else if i = l ∧ j = k then V ^ 2 else 0 := by
    have he := hlist [i, j, k, l]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ← mul_assoc] at he
    rw [he]
    by_cases hij : i = j <;> by_cases hik : i = k <;> by_cases hil : i = l <;>
      by_cases hjk : j = k <;> by_cases hjl : j = l <;> by_cases hkl : k = l <;>
      subst_vars <;>
      simp_all [List.toFinset_cons, List.toFinset_nil, List.count_cons, List.count_nil,
        Finset.prod_insert, Finset.prod_singleton, pow_one, pow_two] <;>
      simp_all [eq_comm, pow_two]
    all_goals exact Or.inl (hsecond _)
  have htwo (a : ι) : MemLp (ε a) 2 μ := (hε a).mono_exponent (by norm_num)
  have hcov2 := projection_coordinate_covariance μ (fun ω a => ε a ω) V htwo hind hmean hsecond
  rw [covariance_eq_sub (independent_error_product_memLp_two μ ε hε i j)
    (independent_error_product_memLp_two μ ε hε k l)]
  simp only [Pi.mul_apply, ← mul_assoc]; rw [h4, hcov2 i j, hcov2 k l]
  clear h4 hlist hcov2 htwo hε hind hmean hsecond
  by_cases hij : i = j <;> by_cases hik : i = k <;> by_cases hil : i = l <;>
    by_cases hjk : j = k <;> by_cases hjl : j = l <;> by_cases hkl : k = l <;>
    subst_vars <;> simp_all [eq_comm, pow_two]

private lemma minimax_rms_projection_parametric_upper {d : ℕ} (C : ModelConstants d) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 1 ≤ n → (d : ℝ) ≤ 4 * C.smoothness →
      minimaxRMS C n ≤ ENNReal.ofReal (B * (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
  let q : ℕ := (C.order + 1) ^ d
  have hq : 0 < q := by positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hdR : (0 : ℝ) < d := by exact_mod_cast C.dimension_pos
  have hVu : 0 < C.varianceUpper := C.varianceLower_pos.trans C.variance_interval
  let K_grid : ℝ := 4 * max C.fourthBound (2 * C.varianceUpper ^ 2) + 32 * C.varianceUpper * C.holderBound ^ 2
  let K_bias : ℝ := 4 * (taylorErrorFactor C * C.holderBound * (2 * (2 * q : ℝ) ^ (d : ℝ)⁻¹) ^ C.smoothness) ^ 4
  let K_tot : ℝ := K_grid + K_bias + 2 * q * (C.varianceUpper - C.varianceLower) ^ 2 + 1
  have hKg : 0 ≤ K_grid := by
    have : 0 ≤ max C.fourthBound (2 * C.varianceUpper ^ 2) :=
      (by positivity : (0 : ℝ) ≤ 2 * C.varianceUpper ^ 2).trans (le_max_right _ _)
    positivity
  have hKb : 0 ≤ K_bias := by positivity
  have hKt : 0 < K_tot := by positivity
  refine ⟨Real.sqrt (2 * K_tot), Real.sqrt_pos.mpr (by positivity), fun n hn hparam => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  suffices hmse : minimaxRisk C n ≤ ENNReal.ofReal (2 * K_tot * ((n : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2) by
    unfold minimaxRMS
    refine (ENNReal.rpow_le_rpow hmse (by norm_num)).trans_eq ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (Real.rpow_nonneg hnR.le _)]
  rw [show ((n : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (n : ℝ)⁻¹ by
    rw [← Real.rpow_mul_natCast hnR.le]; norm_num; exact Real.rpow_neg_one _]
  by_cases hbudget : 2 * q ≤ n
  · let r := ((n : ℝ) / (2 * q)) ^ (d : ℝ)⁻¹
    let k := ⌊r⌋₊
    have hb1 : 1 ≤ (n : ℝ) / (2 * q) := (le_div_iff₀ (by positivity)).mpr (by exact_mod_cast (by linarith))
    have hk : 0 < k := Nat.floor_pos.mpr (Real.one_le_rpow hb1 (by positivity))
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hkle : (k : ℝ) ≤ r := Nat.floor_le (by positivity)
    have hroot : r ^ d = (n : ℝ) / (2 * q) := Real.rpow_inv_natCast_pow (by positivity) C.dimension_pos.ne'
    have hcols : (k : ℝ) ^ d * (C.order + 1 : ℕ) ^ d ≤ (n : ℝ) / 2 := by
      have hb := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * q)).mp ((pow_le_pow_left₀ (by positivity) hkle d).trans_eq hroot)
      rw [show ((C.order + 1 : ℕ) : ℝ) ^ d = q by simp [q]]; linarith
    let est : Estimator d n := ⟨fun z => projectionEstimator
      (1 - empiricalDesignProjection (cellPolynomialDesign (ℓ := C.order)
        (fun i => regularGridCell k hk (z i).1) (fun i => (z i).1))) (fun i => (z i).2),
      empirical_residual_estimator_measurable _ _
        (cell_polynomial_design_measurable _ _
          (measurable_pi_iff.mpr fun i => (regular_grid_cell_measurable k hk).comp (by fun_prop)) (by fun_prop))
        (by fun_prop)⟩
    refine (minimaxRisk_le_worstCaseRisk C est).trans (iSup_le fun ⟨θ, hθ⟩ => ?_)
    let _ := designLaw_isProbability C θ hθ
    let _ : IsProbabilityMeasure (designVectorLaw θ n) :=
      inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin n => designLaw θ))
    rw [meanSquaredRisk_conditioning C _ θ hθ]
    refine (lintegral_mono_ae (g := fun _ => ENNReal.ofReal (2 * K_tot * (n : ℝ)⁻¹)) ?_).trans_eq (by simp)
    filter_upwards [admissible_conditional_error_facts C θ hθ n] with x ⟨hcube, hε, hind, hmean, hsecond, hfourth⟩
    let μ := conditionalErrorLaw θ x
    let ε : Fin n → (Fin n → ℝ) → ℝ := fun i u => u i
    let B := cellPolynomialDesign (ℓ := C.order) (fun i => regularGridCell k hk (x i)) x
    let A := 1 - empiricalDesignProjection B
    let f : Fin n → ℝ := fun i => θ.regression (x i)
    let b := taylorErrorFactor C * C.holderBound * (1 / (k : ℝ)) ^ C.smoothness
    have hP := empirical_design_projection_spec B
    have hA := projection_complement _ hP.1 hP.2.1
    have hdeg : (n : ℝ) / 2 ≤ A.trace := by
      have htr : (n : ℝ) - k ^ d * (C.order + 1 : ℕ) ^ d ≤ A.trace := by
        simpa only [Fintype.card_fin, Fintype.card_fun, Nat.cast_pow] using
          cell_polynomial_residual_degrees (ℓ := C.order) (fun i => regularGridCell k hk (x i)) x
      linarith
    have hd : 0 < A.trace := (half_pos hnR).trans_le hdeg
    classical
    choose P hP_tay using fun c => admissible_regression_taylor_cell C θ hθ (regularGridCorner k c)
      (regular_grid_corner_mem_cube k hk c) (1 / k) (by positivity)
    have hres : projectionEnergy (A *ᵥ f) ≤ n * b ^ 2 := by
      simpa [Fintype.card_fin] using cell_polynomial_residual_bound (fun i => regularGridCell k hk (x i)) x
        f P (fun c => (hP_tay c).1) b
        (mul_nonneg (mul_nonneg (taylorErrorFactor_pos C).le C.holderBound_pos.le) (Real.rpow_nonneg (by positivity) _))
        fun i => (hP_tay _).2 (x i) (hcube i) (regular_grid_cell_radius k hk (x i) (hcube i))
    have htwo (i : Fin n) : MemLp (ε i) 2 μ := (hε i).mono_exponent (by norm_num)
    have hprod := independent_error_product_memLp_two μ ε hε
    have hcov2 := projection_coordinate_covariance μ (fun ω i => ε i ω) θ.variance htwo hind hmean hsecond
    have hcov4 := independent_error_product_covariance μ ε hind hε hmean θ.variance hsecond
    have hX := projection_estimator_memLp_two μ A hA.1 f (fun ω i => ε i ω) htwo hprod
    have hsqI : Integrable (fun ω => (projectionEstimator A (f + fun i => ε i ω) - θ.variance) ^ 2) μ := by
      simpa only [Real.norm_eq_abs, sq_abs, Pi.sub_apply] using
        (hX.sub (memLp_const θ.variance)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    change (∫⁻ u, ENNReal.ofReal ((projectionEstimator A (f + fun i => ε i u) - θ.variance) ^ 2) ∂μ) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal hsqI (Eventually.of_forall fun _ => sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ((projection_estimator_mse_bound μ A hA.1 hA.2 hd f
      (fun ω i => ε i ω) θ.variance (max C.fourthBound (2 * θ.variance ^ 2))
      (fun i => (∫ ω, ε i ω ^ 4 ∂μ) - θ.variance ^ 2)
      htwo hmean hcov2 hprod hcov4
      (fun i => by linarith [hfourth i, le_max_left C.fourthBound (2 * θ.variance ^ 2), sq_nonneg θ.variance])
      (le_max_right _ _)).trans ?_)
    have hV0 : 0 ≤ θ.variance := C.varianceLower_pos.le.trans hθ.2.2.2.2.2.1
    have hVhi : θ.variance ≤ C.varianceUpper := hθ.2.2.2.2.2.2.1
    have heH : projectionEnergy (A *ᵥ f) ≤ n * C.holderBound ^ 2 := by
      refine (projection_energy_le A hA.1 hA.2 f).trans ?_
      unfold projectionEnergy dotProduct
      exact (Finset.sum_le_sum (g := fun _ : Fin n => C.holderBound ^ 2) fun i _ => by
        simpa [pow_two] using (sq_le_sq₀ (abs_nonneg _) C.holderBound_pos.le).mpr
          (admissible_regression_value_bound C θ hθ (x i) (hcube i))).trans_eq (by simp)
    have he0 := projectionEnergy_nonneg (A *ᵥ f)
    have hC4 : 0 ≤ max C.fourthBound (2 * θ.variance ^ 2) := (by positivity : 0 ≤ 2 * θ.variance ^ 2).trans (le_max_right _ _)
    have halg : (2 * max C.fourthBound (2 * θ.variance ^ 2) * A.trace + 8 * θ.variance * projectionEnergy (A *ᵥ f)) / A.trace ^ 2 +
        (projectionEnergy (A *ᵥ f) / A.trace) ^ 2 ≤
        (4 * max C.fourthBound (2 * θ.variance ^ 2) + 32 * θ.variance * C.holderBound ^ 2) / n + 4 * b ^ 4 := by
      rw [div_pow, ← add_div, div_add' _ _ _ hnR.ne', div_le_div_iff₀ (sq_pos_of_pos hd) hnR]
      have hnsq : (n : ℝ) ^ 2 ≤ 4 * A.trace ^ 2 := by nlinarith
      have hesq : projectionEnergy (A *ᵥ f) ^ 2 ≤ (n : ℝ) ^ 2 * b ^ 4 := by nlinarith [(sq_le_sq₀ he0 (by positivity)).mpr hres]
      nlinarith [mul_nonneg (mul_nonneg hC4 hd.le) (show 0 ≤ 2 * A.trace - n by linarith),
        mul_le_mul_of_nonneg_left heH (by positivity : 0 ≤ 8 * θ.variance * n),
        mul_le_mul_of_nonneg_left hnsq (by positivity : 0 ≤ 8 * θ.variance * C.holderBound ^ 2),
        mul_le_mul_of_nonneg_left hesq hnR.le,
        mul_le_mul_of_nonneg_left hnsq (by positivity : 0 ≤ (n : ℝ) * b ^ 4)]
    refine halg.trans ?_
    have hKg_le : 4 * max C.fourthBound (2 * θ.variance ^ 2) + 32 * θ.variance * C.holderBound ^ 2 ≤ K_grid := by
      have hm := max_le_max_left C.fourthBound (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hV0 hVu.le).mpr hVhi) (by norm_num : (0 : ℝ) ≤ 2))
      nlinarith [mul_le_mul_of_nonneg_right hVhi (by positivity : 0 ≤ 32 * C.holderBound ^ 2)]
    have hr2k : r ≤ 2 * k := by
      have : (1 : ℝ) ≤ k := (by exact_mod_cast hk)
      linarith [Nat.lt_floor_add_one r]
    have hrpos : 0 < r := Real.rpow_pos_of_pos (by positivity) _
    have hiw : 1 / (k : ℝ) ≤ (2 * (2 * q : ℝ) ^ (d : ℝ)⁻¹) * (n : ℝ) ^ (-(d : ℝ)⁻¹) := by
      have h2r : 1 / (k : ℝ) ≤ 2 / r := (div_le_div_iff₀ hkR hrpos).mpr (by linarith)
      refine h2r.trans_eq ?_
      dsimp [r]; rw [Real.div_rpow hnR.le (by positivity), Real.rpow_neg hnR.le]; field_simp
    have hp := Real.rpow_le_rpow (by positivity) hiw C.smoothness_pos.le
    have hcoef : 0 ≤ taylorErrorFactor C * C.holderBound := mul_nonneg (taylorErrorFactor_pos C).le C.holderBound_pos.le
    have hpow := pow_le_pow_left₀ (mul_nonneg hcoef (Real.rpow_nonneg (by positivity) _)) (mul_le_mul_of_nonneg_left hp hcoef) 4
    have hbias : 4 * b ^ 4 ≤ K_bias * (n : ℝ)⁻¹ := by
      refine (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 4)).trans ?_
      rw [Real.mul_rpow (by positivity) (by positivity)]
      have hpw : (((n : ℝ) ^ (-(d : ℝ)⁻¹)) ^ C.smoothness) ^ 4 = (n : ℝ) ^ (-(4 * C.smoothness / d)) := by
        rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul (by positivity), ← Real.rpow_mul hnR.le]; congr 1; ring
      have hle1 : (n : ℝ) ^ (-(4 * C.smoothness / d)) ≤ (n : ℝ)⁻¹ := by
        rw [← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg ((one_le_div hdR).mpr hparam))
      exact (show _ = K_bias * (n : ℝ) ^ (-(4 * C.smoothness / d)) by simp only [K_bias, mul_pow, hpw]; ring).le.trans
        (mul_le_mul_of_nonneg_left hle1 hKb)
    have h1 : (4 * max C.fourthBound (2 * θ.variance ^ 2) + 32 * θ.variance * C.holderBound ^ 2) / n ≤ K_grid * (n : ℝ)⁻¹ := by
      rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right hKg_le (inv_nonneg.mpr hnR.le)
    have hKt_le : K_grid + K_bias ≤ 2 * K_tot := by
      dsimp [K_tot]; nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * q) (sq_nonneg (C.varianceUpper - C.varianceLower))]
    nlinarith [mul_le_mul_of_nonneg_right hKt_le (inv_nonneg.mpr hnR.le)]
  · refine (minimaxRisk_le_worstCaseRisk C (constantEstimator d n C.varianceLower)).trans
      (iSup_le fun ⟨θ, hθ⟩ => (constantEstimator_risk_bound C θ hθ).trans (ENNReal.ofReal_le_ofReal ?_))
    have hsmall : (n : ℝ) ≤ 2 * q := by exact_mod_cast (by omega : n ≤ 2 * q)
    apply (le_mul_inv_iff₀ hnR).mpr; dsimp [K_tot]
    nlinarith [mul_le_mul_of_nonneg_left hsmall (sq_nonneg (C.varianceUpper - C.varianceLower))]

-- Endpoints

theorem paper_low_smoothness {d : ℕ} (C : ModelConstants d) : LowSmoothnessClaim C := fun hs => by
  have hden : 0 < (d : ℝ) + 4 * C.smoothness := by linarith [Nat.cast_nonneg (α := ℝ) d, C.smoothness_pos]
  obtain ⟨c, hc, hlower⟩ : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      ENNReal.ofReal (c * lowSmoothnessScale C.smoothness d n) ≤ minimaxRMS C n := by
    by_cases hd : (d : ℝ) ≤ 4 * C.smoothness
    · obtain ⟨c, hc, hb⟩ := parametric_minimax_lower C
      refine ⟨c, hc, fun n hn => ?_⟩
      rw [lowSmoothnessScale, max_eq_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
        (neg_le_neg ((le_div_iff₀ hden).mpr (by nlinarith))))]
      exact hb n hn
    · obtain ⟨c, hc, hb⟩ := low_smoothness_nonparametric_minimax_lower C hs (le_of_not_ge hd)
      refine ⟨c, hc, fun n hn => ?_⟩
      rw [lowSmoothnessScale, max_eq_right (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
        (neg_le_neg ((div_le_iff₀ hden).mpr (by nlinarith)))),
        show -(4 * C.smoothness / ((d : ℝ) + 4 * C.smoothness)) = -4 * C.smoothness / ((d : ℝ) + 4 * C.smoothness) by ring]
      exact hb n hn
  obtain ⟨B, _, hupper⟩ := elementary_upper_low_smoothness C hs
  let A := max B (max 1 c⁻¹)
  have hA : 0 < A := zero_lt_one.trans_le ((le_max_left 1 c⁻¹).trans (le_max_right _ _))
  have hAc : A⁻¹ ≤ c := inv_inv c ▸ (inv_le_inv₀ hA (inv_pos.mpr hc)).mpr ((le_max_right 1 c⁻¹).trans (le_max_right _ _))
  refine ⟨A, hA, fun n hn => ?_⟩
  have hscale : 0 ≤ lowSmoothnessScale C.smoothness d n := (Real.rpow_nonneg (Nat.cast_nonneg n) _).trans (le_max_left _ _)
  have hu : minimaxRMS C n ≤ ENNReal.ofReal (B * lowSmoothnessScale C.smoothness d n) := by
    simpa only [lowSmoothnessScale, show -4 * C.smoothness / ((d : ℝ) + 4 * C.smoothness) =
      -(4 * C.smoothness / ((d : ℝ) + 4 * C.smoothness)) by ring] using hupper n hn
  exact ⟨(ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hAc hscale)).trans (hlower n hn),
    hu.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hscale))⟩

theorem paper_parametric {d : ℕ} (C : ModelConstants d) : ParametricClaim C := fun _ hparametric => by
  obtain ⟨c, hc, hlower⟩ := parametric_minimax_lower C
  obtain ⟨B, _, hupper⟩ := minimax_rms_projection_parametric_upper C
  let A := max B (max 1 c⁻¹)
  have hA : 0 < A := zero_lt_one.trans_le ((le_max_left 1 c⁻¹).trans (le_max_right _ _))
  have hAc : A⁻¹ ≤ c := inv_inv c ▸ (inv_le_inv₀ hA (inv_pos.mpr hc)).mpr ((le_max_right 1 c⁻¹).trans (le_max_right _ _))
  refine ⟨A, hA, fun n hn => ?_⟩
  have hscale := Real.rpow_nonneg (Nat.cast_nonneg n) (-(1 / 2 : ℝ))
  exact ⟨(ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hAc hscale)).trans (hlower n hn),
    (hupper n hn hparametric).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hscale))⟩

theorem paper_main {d : ℕ} (C : ModelConstants d) : MainBracketClaim C :=
  mainBracketClaim_of_separate_bounds C (paper_upper_sharp C) (paper_lower_sharp C)

theorem paper_exponent_limit {d : ℕ} (C : ModelConstants d) (hreg : highSmoothnessRegime C) :
    Tendsto (fun n : ℕ => -Real.log (minimaxRMS C n).toReal / Real.log (n : ℝ))
      atTop (𝓝 (rateExponent C.smoothness d)) :=
  paper_exponent_limit_of_mainBracketClaim C hreg (paper_main C)

theorem paper_polynomial_bounds {d : ℕ} (C : ModelConstants d) (hreg : highSmoothnessRegime C) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ n : ℕ in atTop,
        c * (n : ℝ) ^ (-rateExponent C.smoothness d - epsilon) ≤ (minimaxRMS C n).toReal ∧
        (minimaxRMS C n).toReal ≤ A * (n : ℝ) ^ (-rateExponent C.smoothness d) := by
  obtain ⟨c, A, hc, hA, hb⟩ := hasNatRateBracket_of_mainBracketClaim C hreg (paper_main C)
  refine ⟨c, A, hc, hA, fun epsilon he => ?_⟩
  have hu := tendsto_stretched_log_factor (paper_stretchConstant_pos C hreg)
    (lowerLogPower C.smoothness d + paperLogGap C)
  filter_upwards [hb,
    tendsto_natCast_atTop_atTop.eventually (eventually_correction_between_powers
      (stretchConstant C.smoothness d (paperTau C)) (lowerLogPower C.smoothness d) he),
    tendsto_natCast_atTop_atTop.eventually (hu.eventually (gt_mem_nhds zero_lt_one)),
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with n hn hlow hupp hn1
  have hn0 : 0 < (n : ℝ) := by linarith only [hn1]
  have hp : 0 < Real.exp (-rateExponent C.smoothness d * Real.log n) := Real.exp_pos _
  refine ⟨?_, ?_⟩
  · refine le_trans ?_ hn.1
    rw [rateScale_eq_base_mul_correction, show (n : ℝ) ^ (-rateExponent C.smoothness d - epsilon) =
      Real.exp (-rateExponent C.smoothness d * Real.log n) * (n : ℝ) ^ (-epsilon) by
      rw [Real.rpow_def_of_pos hn0, Real.rpow_def_of_pos hn0, ← Real.exp_add]; congr 1; ring]
    simp only [← mul_assoc]
    exact mul_le_mul_of_nonneg_left hlow.1 (mul_pos hc hp).le
  · refine hn.2.trans ?_
    rw [rateScale_eq_base_mul_correction, Real.rpow_def_of_pos hn0, mul_comm (Real.log (n : ℝ)) (-rateExponent C.smoothness d)]
    exact (by gcongr : _ ≤ A * (Real.exp (-rateExponent C.smoothness d * Real.log n) * 1)).trans_eq (by ring)

end ParametricAndMainEndpoints
end NearlyMinimax
