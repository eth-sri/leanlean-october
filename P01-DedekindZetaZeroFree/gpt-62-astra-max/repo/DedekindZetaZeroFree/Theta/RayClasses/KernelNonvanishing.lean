module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterUnitarityAndOrthogonality
public import DedekindZetaZeroFree.LFunctions.Hecke.ThetaMellinCalibration

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

open scoped NumberField

section

variable (F : Type) [Field F] [NumberField F] (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)

include hm in
theorem rayCharacter_allIdealSeries_tendsto_one :
    Filter.Tendsto (fun σ : ℝ =>
      ∑' I : Ideal (𝓞 F), η I * (Ideal.absNorm I : ℂ) ^ (-(σ : ℂ)))
      Filter.atTop (nhds (1 : ℂ)) := by
  classical
  let g : Ideal (𝓞 F) → ℂ := fun I => if I = ⊤ then 1 else 0
  have hg : (∑' I, g I) = 1 := by simp [g]
  rw [← hg]
  apply tendsto_tsum_of_dominated_convergence
    (DedekindZetaZeroFree.Odlyzko.summable_ideal_absNorm_rpow F (σ := 2) (by norm_num))
  · intro I
    by_cases htop : I = ⊤
    · subst I
      simpa [g, η.map_top'] using
        Filter.tendsto_const_nhds
    by_cases hbot : I = ⊥
    · simpa [g, htop, ((η.eq_zero_iff' I).mpr (Or.inl hbot))] using
        Filter.tendsto_const_nhds
    have hn : 1 < (Ideal.absNorm I : ℝ) := by
      have hn0 := mt Ideal.absNorm_eq_zero_iff.mp hbot
      have hn1 := mt Ideal.absNorm_eq_one_iff.mp htop
      exact_mod_cast (show 1 < Ideal.absNorm I by omega)
    have hr : Filter.Tendsto (fun σ : ℝ => (Ideal.absNorm I : ℝ) ^ (-σ))
        Filter.atTop (nhds 0) := by
      simp_rw [Real.rpow_def_of_pos (lt_trans zero_lt_one hn)]
      exact Real.tendsto_exp_atBot.comp
        (Filter.tendsto_neg_atTop_atBot.const_mul_atBot (Real.log_pos hn))
    have heq (σ : ℝ) : (Ideal.absNorm I : ℂ) ^ (-(σ : ℂ)) =
        (((Ideal.absNorm I : ℝ) ^ (-σ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]
      simp
    simpa only [g, if_neg htop, heq, Function.comp_apply, Complex.ofReal_zero,
      mul_zero] using ((Complex.continuous_ofReal.tendsto 0).comp hr).const_mul (η I)
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with σ hσ
    intro I
    by_cases hbot : I = ⊥
    · simp only [((η.eq_zero_iff' I).mpr (Or.inl hbot)), zero_mul, norm_zero]
      positivity
    have hn : 1 ≤ (Ideal.absNorm I : ℝ) := by
      have hn0 := mt Ideal.absNorm_eq_zero_iff.mp hbot
      exact_mod_cast (show 1 ≤ Ideal.absNorm I by omega)
    rw [norm_mul]
    have hnorm : ‖(Ideal.absNorm I : ℂ) ^ (-(σ : ℂ))‖ =
        (Ideal.absNorm I : ℝ) ^ (-σ) := by
      rw [← Complex.ofReal_neg, ← Complex.ofReal_natCast,
        ← Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    rw [hnorm]
    calc
      _ ≤
          1 * (Ideal.absNorm I : ℝ) ^ (-σ) :=
        mul_le_mul_of_nonneg_right (rayClassCharacter_norm_le_one hm η I)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ (Ideal.absNorm I : ℝ) ^ (-(2 : ℝ)) := by
        rw [one_mul]
        exact Real.rpow_le_rpow_of_exponent_le hn (neg_le_neg hσ)

include hm in
theorem rayCharacter_allIdealSeries_nonzero_somewhere :
    ∃ σ : ℝ, 1 < σ ∧
      (∑' I : Ideal (𝓞 F), η I * (Ideal.absNorm I : ℂ) ^ (-(σ : ℂ))) ≠ 0 := by
  obtain ⟨σ, hσ, hn⟩ := ((Filter.eventually_gt_atTop (1 : ℝ)).and ((rayCharacter_allIdealSeries_tendsto_one F m hm η).eventually_ne
    one_ne_zero)).exists
  exact ⟨σ, hσ, hn⟩

end

namespace Theta

theorem normalizedRayTheta_nonzero_somewhere
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (hnonprincipal : ¬ η.IsPrincipal)
    (D : RayThetaRepresentatives F m hm)
    (χ : RayCharacterData F m hm η) :
    ∃ t : ℝ, 0 < t ∧ normalizedRayTheta D χ.ψ t ≠ 0 := by
  classical
  by_contra h
  have hzero : ∀ t : ℝ, 0 < t → normalizedRayTheta D χ.ψ t = 0 := by
    intro t ht
    by_contra hn
    exact h ⟨t, ht, hn⟩
  obtain ⟨σ, hσ, hL⟩ := rayCharacter_allIdealSeries_nonzero_somewhere F m hm η
  have hs : 1 < (σ : ℂ).re := by exact hσ
  have hmellin : mellin (normalizedRayTheta D χ.ψ) (σ : ℂ) = 0 := by
    unfold mellin
    have heq := MeasureTheory.setIntegral_congr_fun (s := Set.Ioi (0 : ℝ))
      (μ := MeasureTheory.volume) measurableSet_Ioi
      (f := fun t : ℝ => (t : ℂ) ^ ((σ : ℂ) - 1) • normalizedRayTheta D χ.ψ t)
      (g := fun _ : ℝ => (0 : ℂ))
      (fun t ht => by simp only [hzero t ht, smul_zero])
    simpa using heq
  have hprod := ((normalizedRayTheta_mellin_calibration hF D χ hnonprincipal
    (σ : ℂ) hs).2).tsum_eq
  rw [tsum_mul_left, hmellin] at hprod
  exact (mul_ne_zero (completed_prefactor_ne_zero F m hm (σ : ℂ) hs) hL) hprod

end Theta

end DedekindZetaZeroFree.Hecke
