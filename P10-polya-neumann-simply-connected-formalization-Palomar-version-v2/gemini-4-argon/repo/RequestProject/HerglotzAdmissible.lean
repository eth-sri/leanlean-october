module

public import RequestProject.HerglotzDensity

/-!
# Admissible Herglotz data

For small `|k|`, every `w ∈ ℓ²` can be shifted along `e₀` to the Herglotz vector `y_a(z₀)` of a
density whose negative coefficients vanish at a given point `z₁` and whose wave has zero mean
over `Ω` (`exists_admissible_herglotzVec`).
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology

noncomputable section
namespace PolyaNeumann
variable {Ω : Set ℂ}

local notation "Φ0" => Real.sqrt 2

lemma herglotzCoeff_zero_eq_herglotzVec {a : ℝ → ℂ} (ha : IsDirDensity a) k z :
    herglotzCoeff k a 0 z = (Φ0 : ℂ) * (herglotzVec ha k z : ℕ → ℂ) 0 := by
  rw [herglotzVec_apply]
  unfold herglotzSeq
  rw [if_pos rfl]
  have hr : Φ0 ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  field_simp

/-- The mean functional `v ↦ ∫_Ω u_{a_v}`. -/
def synthMean (Ω : Set ℂ) (k : ℝ) (z₁ : ℂ) (v : Ell2) : ℂ :=
  ∫ z in Ω, herglotzCoeff k (synthDens k z₁ v) 0 z

lemma synthMean_smul (k : ℝ) (z₁ : ℂ) c v :
    synthMean Ω k z₁ (c • v) = c * synthMean Ω k z₁ v := by
  unfold synthMean
  rw [← integral_const_mul]
  congr 1
  funext z
  rw [herglotzCoeff_zero_eq_herglotzVec (isDirDensity_synthDens k z₁ _),
    herglotzCoeff_zero_eq_herglotzVec (isDirDensity_synthDens k z₁ v),
    herglotzVec_synthDens_smul]
  simp
  ring

/-- **Admissible Herglotz data.** For a bounded `Ω` of positive area and points `z₀, z₁`, there is
`δ > 0` such that for `|k| < δ` every `w ∈ ℓ²` can be moved along `e₀` to the Herglotz vector
`y_a(z₀)` of a density whose negative coefficients vanish at `z₁` and whose wave has zero mean
over `Ω`. -/
theorem exists_admissible_herglotzVec (hb : Bornology.IsBounded Ω)
    (hΩ : 0 < (volume Ω).toReal) (z₀ z₁ : ℂ) :
    ∃ δ > 0, ∀ k : ℝ, |k| < δ → ∀ w : Ell2, ∃ (t : ℂ) (a : ℝ → ℂ) (ha : IsDirDensity a),
      herglotzVec ha k z₀ = w + t • basisVec 0 ∧
      (∀ j : ℕ, 1 ≤ j → herglotzCoeff k a (-(j : ℤ)) z₁ = 0) ∧
      ∫ z in Ω, herglotzCoeff k a 0 z = 0 := by
  obtain ⟨R₀, hR₀⟩ := hb.subset_closedBall z₁
  set R := max R₀ 0 with hRdef
  set d := ‖z₀ - z₁‖ with hd
  have hs2 : 0 < Φ0 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨min (1 / (4 * Φ0 * (d + 1))) (1 / (4 * (R + 1))), by positivity,
    fun k hk w => ?_⟩
  have hk1 := (hk.trans_le (min_le_left _ _)).le
  have hk2 := (hk.trans_le (min_le_right _ _)).le
  have hε : |k| * Φ0 * d ≤ 1 / 4 := by
    rw [le_div_iff₀ (by positivity)] at hk1
    nlinarith [abs_nonneg k]
  have hkR : |k| * R ≤ 1 / 4 := by
    rw [le_div_iff₀ (by positivity)] at hk2
    nlinarith [abs_nonneg k]
  have hsurj := synthOp_surjective (k := k) (z₁ := z₁) (z₀ := z₀) (by rw [← hd]; linarith)
  -- the preimage of `e₀`
  obtain ⟨v₂, hv₂⟩ := hsurj (basisVec 0)
  have hT2 := norm_herglotzVec_synthDens_sub_le k z₁ z₀ v₂
  rw [← synthOp_apply, hv₂, ← hd] at hT2
  have hv2n : ‖v₂‖ ≤ 4 / 3 := by
    have := norm_le_insert' v₂ (basisVec 0)
    rw [show ‖basisVec 0‖ = 1 by simp [basisVec], norm_sub_rev] at this
    nlinarith [norm_nonneg v₂]
  have hv20 : ‖v₂ 0 - 1‖ ≤ 1 / 3 := by
    have h1 := lp.norm_apply_le_norm (p := 2) (by norm_num) (v₂ - basisVec 0) 0
    rw [show (v₂ - basisVec 0 : Ell2) 0 = v₂ 0 - 1 by
      simp [basisVec], norm_sub_rev v₂] at h1
    nlinarith [norm_nonneg v₂]
  have hlam2 : synthMean Ω k z₁ v₂ ≠ 0 := by
    intro h0
    have h1 : ‖synthMean Ω k z₁ v₂ - (volume Ω).toReal * ((Φ0) * (v₂ : ℕ → ℂ) 0)‖ ≤ 2 * |k| * ‖v₂‖ * R * (volume Ω).toReal := by
      haveI : IsFiniteMeasure (volume.restrict Ω) := ⟨by simpa using hb.measure_lt_top (μ := volume)⟩
      unfold synthMean
      rw [← (show ∫ _ in Ω, Φ0 * v₂ 0 = (volume Ω).toReal * ((Φ0) * v₂ 0) by
        rw [setIntegral_const, Complex.real_smul, Measure.real_def]), ← integral_sub (integrableOn_herglotzCoeff hb (isDirDensity_synthDens k z₁ v₂).intervalIntegrable k 0) (integrable_const _)]
      have := norm_setIntegral_le_of_norm_le_const_ae' (C := 2 * |k| * ‖v₂‖ * R)
        (f := fun z => herglotzCoeff k (synthDens k z₁ v₂) 0 z - Φ0 * v₂ 0)
        (hb.measure_lt_top (μ := volume)) (Eventually.of_forall fun z hz => ?_)
      · simpa [Measure.real_def] using this
      show ‖herglotzCoeff k (synthDens k z₁ v₂) 0 z - Φ0 * v₂ 0‖ ≤ _
      rw [herglotzCoeff_zero_eq_herglotzVec (isDirDensity_synthDens k z₁ v₂), ← mul_sub, norm_mul,
        Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      have h1 : ‖(herglotzVec (isDirDensity_synthDens k z₁ v₂) k z) 0 - v₂ 0‖ ≤
          ‖herglotzVec (isDirDensity_synthDens k z₁ v₂) k z - v₂‖ := by
        simpa using lp.norm_apply_le_norm (p := 2) (by norm_num) (herglotzVec (isDirDensity_synthDens k z₁ v₂) k z - v₂) 0
      have h3 : ‖z - z₁‖ ≤ R := by simpa [dist_eq_norm] using (hR₀.trans (closedBall_subset_closedBall (le_max_left _ _)) : Ω ⊆ closedBall z₁ R) hz
      have hs2 : Φ0 * Φ0 = 2 := Real.mul_self_sqrt (by norm_num)
      calc _ ≤ _ :=
            mul_le_mul_of_nonneg_left (h1.trans (norm_herglotzVec_synthDens_sub_le k z₁ z v₂)) (Real.sqrt_nonneg _)
        _ = 2 * |k| * ‖v₂‖ * ‖z - z₁‖ := by linear_combination (|k| * ‖v₂‖ * ‖z - z₁‖) * hs2
        _ ≤ 2 * |k| * ‖v₂‖ * R := by gcongr
    rw [h0, zero_sub, norm_neg, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hΩ.le, Real.norm_of_nonneg hs2.le] at h1
    have h3 : 2 / 3 ≤ ‖v₂ 0‖ := by
      have := norm_sub_norm_le 1 (v₂ 0)
      rw [norm_one, norm_sub_rev] at this
      linarith
    have h4 : 2 * |k| * ‖v₂‖ * R ≤ 2 / 3 := by nlinarith [abs_nonneg k, norm_nonneg v₂]
    have h5 : 1.4 < Φ0 := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    have h6 : 2 / 3 < Φ0 * ‖v₂ 0‖ := by nlinarith
    nlinarith
  -- the preimage of `w`
  obtain ⟨v₁, hv₁⟩ := hsurj w
  set t : ℂ := -(synthMean Ω k z₁ v₁ / synthMean Ω k z₁ v₂) with ht
  refine ⟨t, synthDens k z₁ (v₁ + t • v₂), isDirDensity_synthDens k z₁ _, ?_, fun j hj =>
    herglotzCoeff_synthDens_neg k z₁ _ j hj, ?_⟩
  · rw [← synthOp_apply, map_add, map_smul, hv₁, hv₂]
  · show synthMean Ω k z₁ (v₁ + t • v₂) = 0
    have h_inl k z₁ v w : synthMean Ω k z₁ (v + w) = synthMean Ω k z₁ v + synthMean Ω k z₁ w := by
      unfold synthMean
      rw [← integral_add (integrableOn_herglotzCoeff hb
          (isDirDensity_synthDens k z₁ v).intervalIntegrable k 0)
        (integrableOn_herglotzCoeff hb (isDirDensity_synthDens k z₁ w).intervalIntegrable k 0)]
      congr 1
      funext z
      rw [herglotzCoeff_zero_eq_herglotzVec (isDirDensity_synthDens k z₁ _),
        herglotzCoeff_zero_eq_herglotzVec (isDirDensity_synthDens k z₁ v),
        herglotzCoeff_zero_eq_herglotzVec (isDirDensity_synthDens k z₁ w),
        herglotzVec_synthDens_add]
      simp
      ring
    rw [h_inl, synthMean_smul, ht]
    field_simp
    ring

end PolyaNeumann

end
