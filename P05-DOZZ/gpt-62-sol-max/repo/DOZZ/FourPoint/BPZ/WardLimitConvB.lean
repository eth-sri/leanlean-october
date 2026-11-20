/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardLimitConvA

/-! # Limits of the double integrals of the cutoff Ward identity

The double integral of the antisymmetrized cutoff kernel against the cutoff chaos converges in
probability to that of the limit kernel `(φ(x)ρ(y) − φ(y)ρ(x)) k(x) k(y) K_v(x − y)/2` against the
limit chaos: the kernels are bounded uniformly, coincide with the limit kernel away from the
diagonal up to the uniformly convergent pinned weights, and the limit chaos has no atoms. The
far-region test functions converge as random test functions. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]
variable {γ q δ : ℝ} {ρ kt k₂ φ : ℂ → ℝ} {D : Set ℂ}
variable {P : Measure Ω} {X : Ω → Distr} {M : Ω → Measure ℂ} {Xc : Ω → ℂ → ℝ → ℝ}

theorem bpz_abs_mul_sub_mul_le {p p' u u' A B : ℝ} (hp : |p'| ≤ A) (hu : |u| ≤ B) :
    |p * u - p' * u'| ≤ |p - p'| * B + A * |u - u'| := by
  have : p * u - p' * u' = (p - p') * u + p' * (u - u') := by ring
  rw [this]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left hu (abs_nonneg _)
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_right hp (abs_nonneg _)

theorem bpz_three_frac_mul_le_one {S K V : ℝ} (hS : 0 ≤ S) (hK : 0 ≤ K) (hV : 0 ≤ V) :
    S * K * V / ((S + 1) * (K + 1) * (V + 1)) ≤ 1 := by
  rw [div_le_one (by positivity)]
  have h1 : S * K ≤ (S + 1) * (K + 1) := by nlinarith
  have h2  := mul_le_mul_of_nonneg_right h1 hV
  nlinarith [mul_nonneg (mul_nonneg hS hK) hV]

/-- Uniform continuity of a weighted singular kernel on separated pairs. The separation
condition is only needed where the multiplier is nonzero. -/
theorem bpz_weighted_kern_uniform {a : ℂ → ℂ → ℝ} {A η : ℝ} (hη : 0 < η)
    (hA : ∀ x y, |a x y| ≤ A)
    (ha : ∀ ε > 0, ∃ d > 0, ∀ x x' y, ‖x - x'‖ ≤ d → |a x y - a x' y| ≤ ε)
    (v : ℂ) {ε : ℝ} (hε : 0 < ε) : ∃ d > 0, ∀ x x' y, ‖x - x'‖ ≤ d →
      (a x y ≠ 0 → η ≤ ‖x - y‖) → (a x' y ≠ 0 → η ≤ ‖x' - y‖) →
      |a x y * bpzKern v (x - y) - a x' y * bpzKern v (x' - y)| ≤ ε := by
  let C := ‖v‖ / η
  let L := 3 * ‖v‖ / η ^ 2
  have hA₀ := (abs_nonneg _).trans (hA 0 0)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  obtain ⟨d, hd, hda⟩ := ha (ε / 2 / (C + 1)) (by positivity)
  let D := ε / 2 / (A * L + 1)
  refine ⟨min d D, lt_min hd (by dsimp [D]; positivity), fun x x' y hxx hx hx' => ?_⟩
  have h₁ : |a x y - a x' y| * C ≤ ε / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < C + 1)).mp (hda x x' y (hxx.trans (min_le_left _ _)))
    linarith [abs_nonneg (a x y - a x' y)]
  have h₂ : A * (L * ‖x - x'‖) ≤ ε / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < A * L + 1)).mp
      (show ‖x - x'‖ ≤ ε / 2 / (A * L + 1) from hxx.trans (min_le_right _ _))
    linarith [norm_nonneg (x - x')]
  have hk (z : ℂ) (hz : η ≤ ‖z - y‖) : |bpzKern v (z - y)| ≤ C :=
    (abs_bpzKern_le v _).trans (div_le_div_of_nonneg_left (norm_nonneg v) hη hz)
  by_cases hax : a x y = 0 <;> by_cases hax' : a x' y = 0
  · simp [hax, hax', hε.le]
  · simp only [hax, zero_mul, zero_sub, abs_neg] at h₁ ⊢
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hk _ (hx' hax')) (abs_nonneg _)).trans (h₁.trans (by linarith))
  · simp only [hax', zero_mul, sub_zero] at h₁ ⊢
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hk _ (hx hax)) (abs_nonneg _)).trans (h₁.trans (by linarith))
  · have hΔ : |bpzKern v (x - y) - bpzKern v (x' - y)| ≤ L * ‖x - x'‖ := by
      simpa only [L, sub_sub_sub_cancel_right, div_mul_eq_mul_div] using
        abs_bpzKern_sub_le v hη (hx hax) (hx' hax')
    refine (bpz_abs_mul_sub_mul_le (hA x' y) (hk _ (hx hax))).trans ?_
    linarith [mul_le_mul_of_nonneg_left hΔ hA₀]

/-- The antisymmetrized limit kernel is uniformly continuous in the first variable away from
the diagonal. -/
theorem bpz_antisym_kern_cont {a b : ℂ → ℝ} (ha : Continuous a) (hac : HasCompactSupport a)
    (hb : Continuous b) (hbc : HasCompactSupport b) (v : ℂ) :
    ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x x' y, η ≤ ‖x - y‖ →
      ‖x - x'‖ ≤ δ → |(a x * b y - a y * b x) / 2 * bpzKern v (x - y) -
        (a x' * b y - a y * b x') / 2 * bpzKern v (x' - y)| ≤ ε := by
  intro η hη ε hε
  obtain ⟨A, hA⟩ := ha.bounded_above_of_compact_support hac
  obtain ⟨B, hB⟩ := hb.bounded_above_of_compact_support hbc
  simp only [Real.norm_eq_abs] at hA hB
  have hA₀ := (abs_nonneg _).trans (hA 0)
  have hB₀ := (abs_nonneg _).trans (hB 0)
  let p := fun x y => (a x * b y - a y * b x) / 2
  have hp x y : |p x y| ≤ A * B := by
    simp only [p, abs_div, abs_two]
    have h₁ : |a x * b y| ≤ A * B := by rw [abs_mul]; gcongr; exacts [hA _, hB _]
    have h₂ : |a y * b x| ≤ A * B := by rw [abs_mul]; gcongr; exacts [hA _, hB _]
    linarith [abs_sub (a x * b y) (a y * b x)]
  have huc (e : ℝ) (he : 0 < e) : ∃ d > 0, ∀ x x' y, ‖x - x'‖ ≤ d → |p x y - p x' y| ≤ e := by
    let t := e / (A + B + 1)
    have ht : 0 < t := by dsimp [t]; positivity
    obtain ⟨d₁, hd₁, hu₁⟩ := bpz_unifCont_of_compact ha hac t ht
    obtain ⟨d₂, hd₂, hu₂⟩ := bpz_unifCont_of_compact hb hbc t ht
    refine ⟨min d₁ d₂, lt_min hd₁ hd₂, fun x x' y hx => ?_⟩
    rw [show p x y - p x' y = ((a x - a x') * b y - a y * (b x - b x')) / 2 by dsimp [p]; ring,
      abs_div, abs_two]
    have h₁ : |(a x - a x') * b y| ≤ t * B := by
      rw [abs_mul]; exact mul_le_mul (hu₁ x x' (hx.trans (min_le_left _ _))) (hB y) (abs_nonneg _) ht.le
    have h₂ : |a y * (b x - b x')| ≤ A * t := by
      rw [abs_mul]; exact mul_le_mul (hA y) (hu₂ x x' (hx.trans (min_le_right _ _))) (abs_nonneg _) hA₀
    have hte : t * (A + B + 1) = e := div_mul_cancel₀ _ (by positivity)
    linarith [abs_sub ((a x - a x') * b y) (a y * (b x - b x'))]
  obtain ⟨d, hd, h⟩ := bpz_weighted_kern_uniform (half_pos hη) hp huc v hε
  refine ⟨min d (η / 2), lt_min hd (half_pos hη), fun x x' y hy hx => ?_⟩
  have := norm_sub_le_norm_sub_add_norm_sub x x' y
  have h₁ := hx.trans (min_le_right d (η / 2))
  exact h x x' y (hx.trans (min_le_left _ _)) (fun _ => by linarith) (fun _ => by linarith)

namespace BPZLimitData

section
variable (hd : BPZLimitData γ q δ ρ kt k₂ φ D)
include hd

theorem rho_abs_cutWeight_le {K : ℝ}
    (hK : ∀ r : ℝ, 0 ≤ r → ∀ y, ρ y ≠ 0 →
      bpzWardCutWeight γ q r kt y ≤ K ∧ kt y * normPlus y ^ (4 + γ ^ 2 * q) ≤ K)
    (hK0 : 0 ≤ K) (n : ℕ) (y : ℂ) :
    ρ y * |bpzWardCutWeight γ q n kt y| ≤ K ∧ ρ y * |k₂ y| ≤ K := by
  by_cases hy : ρ y = 0
  · rw [hy, zero_mul, zero_mul]; exact ⟨hK0, hK0⟩
  have hw0 : 0 ≤ bpzWardCutWeight γ q n kt y := by
    unfold bpzWardCutWeight
    have := hd.kt_nonneg y
    have := Real.rpow_nonneg (bpz_normPlus_pos y).le (4 : ℝ)
    positivity
  obtain ⟨h1, h2⟩ := hK n (Nat.cast_nonneg n) y hy
  rw [← hd.k₂_eq] at h2
  rw [abs_of_nonneg hw0, abs_of_nonneg (hd.k₂_nonneg y)]
  exact ⟨(mul_le_mul (hd.ρ_le_one y) h1 hw0 zero_le_one).trans (by linarith),
    (mul_le_mul (hd.ρ_le_one y) h2 (hd.k₂_nonneg y) zero_le_one).trans (by linarith)⟩

theorem symKer_eq_zero {R : ℝ}
    (hR : ∀ y, R < ‖y‖ → ρ y = 0) (k L : ℂ → ℝ) {x y : ℂ} (h : R < ‖x‖ ∨ R < ‖y‖) :
    bpzSymKer φ ρ k L x y = 0 := by
  unfold bpzSymKer
  rcases h with h | h
  · rw [hR x h, hd.phi_zero_of_rho_zero (hR x h)]; ring
  · rw [hR y h, hd.phi_zero_of_rho_zero (hR y h)]; ring

end

theorem symKer_eq_antisym (k L : ℂ → ℝ) (x y : ℂ) :
    bpzSymKer φ ρ k L x y = ((φ x * k x) * (ρ y * k y) - (φ y * k y) * (ρ x * k x)) / 2 * L (x - y) := by
  unfold bpzSymKer; ring

section
variable (hd : BPZLimitData γ q δ ρ kt k₂ φ D)
include hd

/-- The cutoff kernels converge uniformly away from the diagonal. -/
theorem symKer_unif (v : ℂ) :
    ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ x y, η ≤ ‖x - y‖ →
      |bpzSymKer φ ρ (bpzWardCutWeight γ q n kt) (fun w => bpzLamDeriv n w v) x y -
        bpzSymKer φ ρ k₂ (bpzKern v) x y| ≤ ε := by
  intro η hη ε hε
  obtain ⟨K, hK0, hK⟩ := hd.cutWeight_bound
  obtain ⟨B, hB0, hB⟩ := hd.phi_bdd
  set V : ℝ := ‖v‖ with hVdef
  have hV0  := norm_nonneg v
  set ε' : ℝ := ε * η / (2 * ((B + 1) * (K + 1) * (V + 1))) with hε'
  have hε'0 : 0 < ε' := by positivity
  have htail : ∀ᶠ n : ℕ in atTop, 2 * Real.exp (-(n : ℝ)) < η := by
    have := ((Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul
      2).eventually (gt_mem_nhds (show (2 : ℝ) * 0 < η by linarith))
    assumption
  filter_upwards [hd.cutWeight_tendsto ε' hε'0, htail] with n hn htn x y hxy
  have hL  :=
    bpzLamDeriv_apply_eq_kern n (lt_of_lt_of_le htn hxy) v
  have heq : bpzSymKer φ ρ (bpzWardCutWeight γ q n kt) (fun w => bpzLamDeriv n w v) x y -
      bpzSymKer φ ρ k₂ (bpzKern v) x y =
        (φ x * ρ y - φ y * ρ x) * (bpzWardCutWeight γ q n kt x * bpzWardCutWeight γ q n kt y -
          k₂ x * k₂ y) * bpzKern v (x - y) / 2 := by
    unfold bpzSymKer
    beta_reduce
    rw [hL]
    ring
  rw [heq]
  by_cases hρ0 : ρ x = 0 ∨ ρ y = 0
  · rcases hρ0 with h | h
    · rw [h, hd.phi_zero_of_rho_zero h]; simp; positivity
    · rw [h, hd.phi_zero_of_rho_zero h]; simp; positivity
  push Not at hρ0
  obtain ⟨hx0, hy0⟩ := hρ0
  have hdx := hn x hx0
  have hdy := hn y hy0
  rw [← hd.k₂_eq] at hdx hdy
  have hk1x := (hK n (Nat.cast_nonneg n) x hx0).1
  have hk2y := (hK n (Nat.cast_nonneg n) y hy0).2
  rw [← hd.k₂_eq] at hk2y
  have hw0 : 0 ≤ bpzWardCutWeight γ q n kt x := by
    unfold bpzWardCutWeight
    have := hd.kt_nonneg x
    have := Real.rpow_nonneg (bpz_normPlus_pos x).le (4 : ℝ)
    positivity
  have hprod : |bpzWardCutWeight γ q n kt x * bpzWardCutWeight γ q n kt y - k₂ x * k₂ y| ≤
      2 * (K * ε') := by
    have : bpzWardCutWeight γ q n kt x * bpzWardCutWeight γ q n kt y - k₂ x * k₂ y =
        bpzWardCutWeight γ q n kt x * (bpzWardCutWeight γ q n kt y - k₂ y) +
          k₂ y * (bpzWardCutWeight γ q n kt x - k₂ x) := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hw0, abs_of_nonneg (hd.k₂_nonneg y)]
    have e1 := mul_le_mul hk1x hdy (abs_nonneg _) hK0
    have e2 := mul_le_mul hk2y hdx (abs_nonneg _) hK0
    linarith
  have hφρ : |φ x * ρ y - φ y * ρ x| ≤ 2 * B := by
    have e1 : |φ x * ρ y| ≤ B := by
      rw [abs_mul, abs_of_nonneg (hd.ρ_nonneg y)]
      exact (mul_le_mul (hB x) (hd.ρ_le_one y) (hd.ρ_nonneg y) hB0).trans (by linarith)
    have e2 : |φ y * ρ x| ≤ B := by
      rw [abs_mul, abs_of_nonneg (hd.ρ_nonneg x)]
      exact (mul_le_mul (hB y) (hd.ρ_le_one x) (hd.ρ_nonneg x) hB0).trans (by linarith)
    have := (abs_sub _ _).trans (add_le_add e1 e2)
    linarith
  have hKb  :=
    (abs_bpzKern_le v _).trans (div_le_div_of_nonneg_left (norm_nonneg v) hη hxy)
  rw [abs_div, abs_two, abs_mul, abs_mul]
  have hfin : 2 * B * (2 * (K * ε')) * (V / η) / 2 ≤ ε := by
    have := bpz_three_frac_mul_le_one hB0 hK0 hV0
    have hrw : 2 * B * (2 * (K * ε')) * (V / η) / 2 =
        ε * (B * K * V / ((B + 1) * (K + 1) * (V + 1))) := by
      rw [hε']; field_simp
    rw [hrw]
    calc ε * (B * K * V / ((B + 1) * (K + 1) * (V + 1))) ≤ ε * 1 :=
          mul_le_mul_of_nonneg_left this hε.le
      _ = ε := mul_one _
  calc |φ x * ρ y - φ y * ρ x| *
        |bpzWardCutWeight γ q n kt x * bpzWardCutWeight γ q n kt y - k₂ x * k₂ y| *
        |bpzKern v (x - y)| / 2
      ≤ 2 * B * (2 * (K * ε')) * (V / η) / 2 := by gcongr
    _ ≤ ε := hfin

/-- The symmetric double integrals converge. -/
theorem conv_sym (hp : BPZWardProb P X γ M Xc ρ k₂ D)
    (v : ℂ) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => ∫ x, ∫ y, bpzSymKer φ ρ (bpzWardCutWeight γ q n kt)
        (fun w => bpzLamDeriv n w v) x y ∂bpzCutChaos P Xc γ n ω ∂bpzCutChaos P Xc γ n ω) atTop
      (fun ω => ∫ x, ∫ y, bpzSymKer φ ρ k₂ (bpzKern v) x y ∂M ω ∂M ω) := by
  have  := hp.hX.1
  have hμ := bpzWeakConv_gmc P X hp.hX hd.γ_pos hp.γ2 M hp.hM hp.hMm Xc hp.hXc
  have hatom := gmc_noAtoms_ae P X hp.hX γ hd.γ_pos hp.γ2 M hp.hM hp.hMm
  obtain ⟨K, hK0, hK⟩ := hd.cutWeight_bound
  obtain ⟨R, hR0, hR⟩ := hd.rho_zero_of_norm
  obtain ⟨B, hB0, hB⟩ := hd.phi_bdd
  obtain ⟨Lφ, hLφ⟩ := hd.φ_lip
  have hδ := hd.δ_pos
  set Cs : ℝ := 2 * ‖v‖ * ((Lφ : ℝ) + B / δ) with hCs
  have hCs0 : 0 ≤ Cs := by positivity
  have hLn : ∀ (n : ℕ) w, |bpzLamDeriv n w v| ≤ 2 * ‖v‖ / ‖w‖ := fun n w =>
    abs_bpzLamDeriv_apply_le n w v
  have hK2 : ∀ w, |bpzKern v w| ≤ 2 * ‖v‖ / ‖w‖ := fun w =>
    (abs_bpzKern_le v w).trans (div_le_div_of_nonneg_right (by linarith [norm_nonneg v])
      (norm_nonneg w))
  have hbd : ∀ (n : ℕ) x y, |bpzSymKer φ ρ (bpzWardCutWeight γ q n kt)
      (fun w => bpzLamDeriv n w v) x y| ≤ Cs * (K * K) := by
    intro n x y
    refine (hd.abs_symKer_le hB hLφ zero_le_two v (hLn n) x y).trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hd.rho_abs_cutWeight_le hK hK0 n x).1
      (hd.rho_abs_cutWeight_le hK hK0 n y).1 (mul_nonneg (hd.ρ_nonneg y) (abs_nonneg _)) hK0)
      hCs0
  have hbd₀ : ∀ x y, |bpzSymKer φ ρ k₂ (bpzKern v) x y| ≤ Cs * (K * K) := by
    intro x y
    refine (hd.abs_symKer_le hB hLφ zero_le_two v hK2 x y).trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hd.rho_abs_cutWeight_le hK hK0 0 x).2
      (hd.rho_abs_cutWeight_le hK hK0 0 y).2 (mul_nonneg (hd.ρ_nonneg y) (abs_nonneg _)) hK0)
      hCs0
  have hLm : ∀ n : ℕ, Measurable fun w => bpzLamDeriv n w v := fun n =>
    (ContinuousLinearMap.apply ℝ ℝ v).continuous.measurable.comp (measurable_bpzLamDeriv n)
  have hac : Continuous fun x => φ x * k₂ x := by
    have h : (fun x => φ x * k₂ x) = fun x => (φ x * kt x) * normPlus x ^ (4 + γ ^ 2 * q) := by
      funext x; rw [hd.k₂_eq]; ring
    rw [h]
    exact hd.f_C1.continuous.mul (bpz_continuous_normPlus.rpow_const fun x => Or.inl
      (bpz_normPlus_pos x).ne')
  have has : HasCompactSupport fun x => φ x * k₂ x := bpz_hasCompactSupport_of_ball (R := R)
    fun x hx => by rw [hd.phi_zero_of_rho_zero (hR x hx), zero_mul]
  have hbs : HasCompactSupport fun x => ρ x * k₂ x := bpz_hasCompactSupport_of_ball (R := R)
    fun x hx => by rw [hR x hx, zero_mul]
  refine hμ.tendstoInMeasure_double hatom
    (fun n => bpzSymKer φ ρ (bpzWardCutWeight γ q n kt) (fun w => bpzLamDeriv n w v))
    (bpzSymKer φ ρ k₂ (bpzKern v))
    (fun n => measurable_bpzSymKer hd.phi_cont.measurable hd.ρ_meas
      (hd.measurable_cutWeight n) (hLm n))
    (measurable_bpzSymKer hd.phi_cont.measurable hd.ρ_meas hd.k₂_meas (measurable_bpzKern v))
    hR0 hbd hbd₀ (fun n x y h => hd.symKer_eq_zero hR _ _ h)
    (fun x y h => hd.symKer_eq_zero hR _ _ h) ?_ (hd.symKer_unif v)
  intro η hη ε hε
  obtain ⟨δ', hδ', h⟩ := bpz_antisym_kern_cont hac has hd.rho_k₂_cont hbs v η hη ε hε
  refine ⟨δ', hδ', fun x x' y hxy hxx' => ?_⟩
  rw [symKer_eq_antisym, symKer_eq_antisym]
  apply h <;> assumption

end

end BPZLimitData

end DOZZ.Proofs
