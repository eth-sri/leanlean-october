/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardLimitConvB

/-! # Limit of the far-region term of the cutoff Ward identity

The far-region test function `x ↦ ∫ (1 − ρ(y)) k₂(y) φ(x) k₁(x) T_n'(x − y)v dM(y)` only sees
pairs at distance at least `2δ`, where the truncated kernel is the limit kernel once the cutoff is
fine enough. It is therefore a random test function, equicontinuous with modulus proportional to the
far mass `∫ (1 − ρ) k₂ dM`, converging uniformly at the same scale; its integrals against the
cutoff chaos converge in probability. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]
variable {γ q δ : ℝ} {ρ kt k₂ φ : ℂ → ℝ} {D : Set ℂ}
variable {P : Measure Ω} {X : Ω → Distr} {M : Ω → Measure ℂ} {Xc : Ω → ℂ → ℝ → ℝ}

namespace BPZLimitData

section
variable (hd : BPZLimitData γ q δ ρ kt k₂ φ D) {B : ℝ} (hB : ∀ x, |φ x| ≤ B) {c : ℝ} (hc : 0 ≤ c)
  (v : ℂ) {k L : ℂ → ℝ}
include hd B hB hc

/-- The far-region integrand is dominated by the far weight. -/
theorem abs_mixIntegrand_le
    (hL : ∀ w, |L w| ≤ c * ‖v‖ / ‖w‖) {Kk : ℝ} (hk : ∀ x, ρ x * |k x| ≤ Kk) (x y : ℂ) :
    |(1 - ρ y) * k₂ y * (φ x * k x * L (x - y))| ≤
      c * ‖v‖ / (2 * δ) * B * Kk * ((1 - ρ y) * k₂ y) := by
  have hw : 0 ≤ (1 - ρ y) * k₂ y := mul_nonneg (sub_nonneg.mpr (hd.ρ_le_one y)) (hd.k₂_nonneg y)
  have hB₀ := (abs_nonneg _).trans (hB x)
  have hK₀ := (mul_nonneg (hd.ρ_nonneg x) (abs_nonneg _)).trans (hk x)
  have hδ := hd.δ_pos
  by_cases hx : φ x = 0
  · simpa [hx] using (show 0 ≤ c * ‖v‖ / (2 * δ) * B * Kk * ((1 - ρ y) * k₂ y) by positivity)
  by_cases hy : ρ y = 1
  · simp [hy]
  have ht := subset_tsupport φ hx
  have hsep := hd.sep x ht y (lt_of_le_of_ne (hd.ρ_le_one _) hy)
  have hL' := (hL (x - y)).trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hsep)
  have hK : |k x| ≤ Kk := by simpa [hd.rho_eq_one ht] using hk x
  rw [abs_mul ((1 - ρ y) * k₂ y), abs_of_nonneg hw, abs_mul, abs_mul]
  calc _ ≤ ((1 - ρ y) * k₂ y) * (B * Kk * (c * ‖v‖ / (2 * δ))) := by gcongr <;> exact hB x
       _ = _ := by ring

theorem integrable_mixIntegrand
    (hLm : Measurable L) (hL : ∀ w, |L w| ≤ c * ‖v‖ / ‖w‖) {Kk : ℝ}
    (hk : ∀ x, ρ x * |k x| ≤ Kk) {m : Measure ℂ}
    (hint : Integrable (fun y => (1 - ρ y) * k₂ y) m) (x : ℂ) :
    Integrable (fun y => (1 - ρ y) * k₂ y * (φ x * k x * L (x - y))) m := by
  refine (hint.const_mul (c * ‖v‖ / (2 * δ) * B * Kk)).mono' ?_
    (Eventually.of_forall fun y => ?_)
  · exact (((measurable_const.sub hd.ρ_meas).mul hd.k₂_meas).mul
      (measurable_const.mul (hLm.comp (measurable_const.sub measurable_id)))).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    apply hd.abs_mixIntegrand_le <;> assumption

end

/-- The far-region test functions converge. -/
theorem conv_mix (hd : BPZLimitData γ q δ ρ kt k₂ φ D) (hp : BPZWardProb P X γ M Xc ρ k₂ D)
    (v : ℂ) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => ∫ x, bpzMixTest φ ρ (bpzWardCutWeight γ q n kt) k₂
        (fun w => bpzTruncLogDeriv n w v) (M ω) x ∂bpzCutChaos P Xc γ n ω) atTop
      (fun ω => ∫ x, bpzMixTest φ ρ k₂ k₂ (bpzKern v) (M ω) x ∂M ω) := by
  have  := hp.hX.1
  have hμ := bpzWeakConv_gmc P X hp.hX hd.γ_pos hp.γ2 M hp.hM hp.hMm Xc hp.hXc
  obtain ⟨K, hK0, hK⟩ := hd.cutWeight_bound
  obtain ⟨R, hR0, hR⟩ := hd.rho_zero_of_norm
  obtain ⟨B, hB0, hB⟩ := hd.phi_bdd
  have hδ := hd.δ_pos
  set I₂ : Ω → ℝ := fun ω => ∫ y, (1 - ρ y) * k₂ y ∂M ω with hI₂
  have hI₂m : Measurable I₂ :=
    (measurable_integral_measure ((measurable_const.sub hd.ρ_meas).mul hd.k₂_meas)).comp hp.hMm
  have hI₂0 : ∀ ω, 0 ≤ I₂ ω := fun ω => integral_nonneg fun y =>
    mul_nonneg (by linarith [hd.ρ_le_one y]) (hd.k₂_nonneg y)
  set C₀ : ℝ := ‖v‖ / (2 * δ) * B * K + 1 with hC₀
  have hC₀1 : 1 ≤ C₀ := by
    have : 0 ≤ ‖v‖ / (2 * δ) * B * K := by positivity
    linarith
  set V : Ω → ℝ := fun ω => C₀ * I₂ ω with hV
  have hTn : ∀ (n : ℕ) w, |bpzTruncLogDeriv n w v| ≤ 1 * ‖v‖ / ‖w‖ := fun n w => by
    rw [one_mul]; exact abs_bpzTruncLogDeriv_apply_le n w v
  have hKv : ∀ w, |bpzKern v w| ≤ 1 * ‖v‖ / ‖w‖ := fun w => by
    rw [one_mul]; exact abs_bpzKern_le v w
  have hk₁  := fun n x =>
    (hd.rho_abs_cutWeight_le hK hK0 n x).1
  have hk₂  := fun x => (hd.rho_abs_cutWeight_le hK hK0 0 x).2
  have hTm : ∀ n : ℕ, Measurable fun w => bpzTruncLogDeriv n w v := fun n =>
    (ContinuousLinearMap.apply ℝ ℝ v).continuous.measurable.comp (measurable_bpzTruncLogDeriv n)
  -- the joint measurability of the random test functions
  have hjoint : ∀ (k L : ℂ → ℝ), Measurable k → Measurable L →
      Measurable (fun p : Ω × ℂ => bpzMixTest φ ρ k k₂ L (M p.1) p.2) := by
    intro k L hk hL
    unfold bpzMixTest
    exact measurable_integral_finite_family M hp.hMm hp.hM.1
      (fun x y => (1 - ρ y) * k₂ y * (φ x * k x * L (x - y)))
      ((((measurable_const.sub (hd.ρ_meas.comp measurable_snd)).mul
        (hd.k₂_meas.comp measurable_snd)).mul
        (((hd.phi_cont.measurable.comp measurable_fst).mul (hk.comp measurable_fst)).mul
          (hL.comp (measurable_fst.sub measurable_snd)))))
  -- bounds by the far mass
  have hbound : ∀ (k L : ℂ → ℝ), (∀ w, |L w| ≤ 1 * ‖v‖ / ‖w‖) → (∀ x, ρ x * |k x| ≤ K) →
      ∀ᵐ ω ∂P, ∀ x, |bpzMixTest φ ρ k k₂ L (M ω) x| ≤ V ω := by
    intro k L hL hk
    filter_upwards [hp.k₂_int] with ω hω x
    refine (hd.abs_mixTest_le hB zero_le_one v hL hω x).trans ?_
    have h1 : 1 * ‖v‖ / (2 * δ) * B * (ρ x * |k x|) ≤ C₀ := by
      calc 1 * ‖v‖ / (2 * δ) * B * (ρ x * |k x|) ≤ 1 * ‖v‖ / (2 * δ) * B * K :=
            mul_le_mul_of_nonneg_left (hk x) (by positivity)
        _ ≤ C₀ := by rw [hC₀, one_mul]; linarith
    calc 1 * ‖v‖ / (2 * δ) * B * (ρ x * |k x|) * I₂ ω ≤ C₀ * I₂ ω :=
          mul_le_mul_of_nonneg_right h1 (hI₂0 ω)
      _ = V ω := rfl
  have hsupp : ∀ (k L : ℂ → ℝ) ω x, R < ‖x‖ → bpzMixTest φ ρ k k₂ L (M ω) x = 0 := by
    intro k L ω x hx
    unfold bpzMixTest
    rw [hd.phi_zero_of_rho_zero (hR x hx)]
    simp
  let w := fun y => (1 - ρ y) * k₂ y
  have hw y : 0 ≤ w y := mul_nonneg (sub_nonneg.mpr (hd.ρ_le_one y)) (hd.k₂_nonneg y)
  have herr (ω) {F G : ℂ → ℝ} {e : ℝ} (he : 0 ≤ e) (hi : Integrable w (M ω))
      (hF : Integrable (fun y => w y * F y) (M ω)) (hG : Integrable (fun y => w y * G y) (M ω))
      (h : ∀ y, ρ y ≠ 1 → |F y - G y| ≤ e) :
      |(∫ y, w y * F y ∂M ω) - (∫ y, w y * G y ∂M ω)| ≤ e * V ω := by
    rw [← integral_sub hF hG, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (hi.const_mul e) (ae_of_all _ fun y => ?_)).trans ?_
    · rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (hw y)]
      by_cases hy : ρ y = 1
      · simp [w, hy]
      · simpa only [mul_comm (w y)] using mul_le_mul_of_nonneg_left (h y hy) (hw y)
    · rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (hI₂0 ω) hC₀1) he
  let a := fun x => φ x * k₂ x
  have has : HasCompactSupport a := hd.φ_compact.mul_right
  have hac : Continuous a := by
    have h : a = fun x => (φ x * kt x) * normPlus x ^ (4 + γ ^ 2 * q) := by
      ext x; dsimp [a]; rw [hd.k₂_eq]; ring
    rw [h]
    exact hd.f_C1.continuous.mul (bpz_continuous_normPlus.rpow_const fun x => Or.inl (bpz_normPlus_pos x).ne')
  have ha x : |a x| ≤ B * K := by
    by_cases hx : φ x = 0
    · simpa [a, hx] using mul_nonneg hB0 hK0
    · have hh : |k₂ x| ≤ K := by simpa [hd.rho_eq_one (subset_tsupport φ hx)] using hk₂ x
      rw [show a x = φ x * k₂ x from rfl, abs_mul]
      gcongr; exact hB x
  have hsep (x y : ℂ) (hx : φ x ≠ 0) (hy : ρ y ≠ 1) : 2 * δ ≤ ‖x - y‖ :=
    hd.sep x (subset_tsupport φ hx) y (lt_of_le_of_ne (hd.ρ_le_one y) hy)
  refine hμ.tendstoInMeasure_random_test
    (fun n ω x => bpzMixTest φ ρ (bpzWardCutWeight γ q n kt) k₂ (fun w => bpzTruncLogDeriv n w v)
      (M ω) x)
    (fun ω x => bpzMixTest φ ρ k₂ k₂ (bpzKern v) (M ω) x)
    (fun n => hjoint _ _ (hd.measurable_cutWeight n) (hTm n))
    (hjoint _ _ hd.k₂_meas (measurable_bpzKern v)) hR0 (V := V) (hI₂m.const_mul C₀)
    (fun ω => mul_nonneg (by linarith) (hI₂0 ω))
    (fun n => hbound _ _ (hTn n) (hk₁ n)) (hbound _ _ hKv hk₂)
    (fun n ω x hx => hsupp _ _ ω x hx) (fun ω x hx => hsupp _ _ ω x hx) ?_ ?_
  · intro ε hε
    obtain ⟨d, hd', hclose⟩ := bpz_weighted_kern_uniform (a := fun x _ => a x) (by positivity : 0 < 2 * δ)
      (fun x _ => ha x) (fun e he => by
        obtain ⟨r, hr, hu⟩ := bpz_unifCont_of_compact hac has e he
        exact ⟨r, hr, fun x x' _ => hu x x'⟩) v hε
    refine ⟨d, hd', ?_⟩
    filter_upwards [hp.k₂_int] with ω hi x x' hxx
    refine herr ω hε.le hi
      (hd.integrable_mixIntegrand hB zero_le_one v (measurable_bpzKern v) hKv hk₂ hi x)
      (hd.integrable_mixIntegrand hB zero_le_one v (measurable_bpzKern v) hKv hk₂ hi x') fun y hy => ?_
    exact hclose x x' y hxx (fun h => hsep _ _ (left_ne_zero_of_mul h) hy)
      (fun h => hsep _ _ (left_ne_zero_of_mul h) hy)
  · intro ε hε
    let C := B * (‖v‖ / (2 * δ))
    have hC : 0 ≤ C := by dsimp [C]; positivity
    let e := ε / (C + 1)
    have he : 0 < e := by dsimp [e]; positivity
    have htail := (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).eventually
      (gt_mem_nhds (by positivity : 0 < 2 * δ))
    filter_upwards [hd.cutWeight_tendsto e he, htail] with n hn ht
    filter_upwards [hp.k₂_int] with ω hi x
    refine herr ω hε.le hi (hd.integrable_mixIntegrand hB zero_le_one v (hTm n) (hTn n) (hk₁ n) hi x)
      (hd.integrable_mixIntegrand hB zero_le_one v (measurable_bpzKern v) hKv hk₂ hi x) ?_
    intro y hy
    by_cases hx : φ x = 0
    · simp [hx, hε.le]
    have hs := hsep x y hx hy
    have hK := (abs_bpzKern_le v (x - y)).trans
      (div_le_div_of_nonneg_left (norm_nonneg v) (by positivity) hs)
    have hk := hn x (by rw [hd.rho_eq_one (subset_tsupport φ hx)]; exact one_ne_zero)
    rw [← hd.k₂_eq] at hk
    change |φ x * bpzWardCutWeight γ q n kt x * bpzTruncLogDeriv n (x - y) v -
      φ x * k₂ x * bpzKern v (x - y)| ≤ ε
    rw [bpzTruncLogDeriv_apply_eq_kern n (ht.trans_le hs) v, ← sub_mul, ← mul_sub, abs_mul, abs_mul]
    calc _ ≤ B * e * (‖v‖ / (2 * δ)) := by gcongr; exact hB x
         _ ≤ ε := by
           have h : e * (C + 1) = ε := div_mul_cancel₀ _ (by positivity)
           rw [mul_comm B e, mul_assoc]
           change e * C ≤ ε
           linarith

end BPZLimitData

end DOZZ.Proofs
