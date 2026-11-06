module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.SourceProfileMass
public import OAI.NumberTheory.DirichletL.Moments.FirstTailAggregate

@[expose] public section

namespace OAI


open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentAbsoluteEnergy
open ActualEisensteinCubic HeckeFamily CanonicalRowCompletion
open CenteredMomentHeckeExpansion CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open ConcreteTraceCRT EisensteinSchwartzPoisson QuadraticInitialBound


section
variable (η : Character) (m A z : ActualEisensteinCubic.O) (t : ℝ) (S : Finset (Ideal ActualEisensteinCubic.O)) (c : Ideal ActualEisensteinCubic.O → ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)

theorem rowWeight_norm_le_one_all      
     I  : ‖rowWeight η m A z t I‖ ≤ 1 := by
  by_cases hI : I=0
  · subst I
    rw [map_zero,norm_zero]
    norm_num
  · exact CenteredMomentFirstTailAggregate.rowWeight_norm_le_one η m A z t I hI

include hK in
theorem radial_norm_summable       :
    Summable (fun z : ActualEisensteinCubic.O => ‖Φ (‖eisEmbedding z‖^2/K)‖) := by
  simpa only [scaledRadialTest_apply] using
    actual_eisenstein_summable_norm (scaledRadialTest Φ K hK)

include hK in
theorem radial_weight_lattice_bound_all       :
    (∑' z : ActualEisensteinCubic.O, ‖Φ (‖eisEmbedding z‖^2/K)‖) ≤ diagonalControl Φ*max 1 K := by
  by_cases hlarge : 1≤K
  · simpa only [max_eq_right hlarge] using radial_weight_lattice_bound Φ K hlarge
  have hsmall : K≤1 := (not_le.mp hlarge).le
  let B := 4*(Finset.Iic (2,0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ
  have hB : 0≤B := by dsimp [B]; positivity
  have hp (z : ActualEisensteinCubic.O) : ‖Φ (‖eisEmbedding z‖^2/K)‖ ≤
      B*((1+1*‖eisEmbedding z‖^2)^2)⁻¹ := by
    have hq : 0≤‖eisEmbedding z‖^2/K := div_nonneg (sq_nonneg _) hK.le
    have hh := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (2,0)) (k := 2) (n := 0) le_rfl le_rfl Φ (‖eisEmbedding z‖^2/K)
    simp only [norm_iteratedFDeriv_zero,Real.norm_of_nonneg hq] at hh
    norm_num only [show (2:ℝ)^2=4 by norm_num] at hh
    change (1+‖eisEmbedding z‖^2/K)^2*‖Φ (‖eisEmbedding z‖^2/K)‖≤B at hh
    have hq' : ‖eisEmbedding z‖^2≤‖eisEmbedding z‖^2/K := by
      bound
    have hden : (1+1*‖eisEmbedding z‖^2)^2≤(1+‖eisEmbedding z‖^2/K)^2 := by
      simp only [one_mul]
      gcongr
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using (mul_le_mul_of_nonneg_right hden (norm_nonneg _)).trans hh
  have hb := (radial_norm_summable Φ K hK).tsum_le_tsum hp
    ((scaled_eisenstein_cauchy_summable 1 (by norm_num)).mul_left B)
  rw [tsum_mul_left] at hb
  have hc := scaled_eisenstein_cauchy_small 1 (by norm_num) (by norm_num)
  simp only [one_mul] at hc hb
  have ht := hb.trans (mul_le_mul_of_nonneg_left hc hB)
  rw [max_eq_left hsmall,mul_one]
  dsimp only [B] at ht
  unfold diagonalControl
  nlinarith

theorem finite_hecke_polynomial_norm      
        :
    ‖∑ I∈S,c I*rowWeight η m A z t I‖ ≤ ∑ I∈S,‖c I‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (rowWeight_norm_le_one_all η m A z t I)

include hK in
theorem finite_hecke_energy_summable      
              :
    Summable (fun z : ActualEisensteinCubic.O => ((‖∑ I∈S,c I*rowWeight η m A z t I‖^2:ℝ):ℂ)*
      Φ (‖eisEmbedding z‖^2/K)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (f := fun z : ActualEisensteinCubic.O => (∑ I∈S,‖c I‖)^2*‖Φ (‖eisEmbedding z‖^2/K)‖)
  · intro z
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (finite_hecke_polynomial_norm η m A z t S c) 2)
      (norm_nonneg _)
  · exact (radial_norm_summable Φ K hK).mul_left _

end

end SevenEighths.CenteredMomentAbsoluteEnergy



end OAI
