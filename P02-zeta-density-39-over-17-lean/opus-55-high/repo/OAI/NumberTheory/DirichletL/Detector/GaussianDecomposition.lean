module
public import OAI.NumberTheory.DirichletL.Detector.GaussianWindows
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

section
variable {α : Type*} (a : α→ℂ) (N : α→ℝ) (ha : Summable a) (hN : ∀p,a p≠0→1≤N p)
include α a N ha hN
lemma annular_reassembly_summable :
    Summable (fun q : α×ℕ=>gaussianAnnulus (N q.1/(2:ℝ)^q.2)*a q.1) := by
  have hs (p : α) : HasSum (fun j : ℕ=>‖gaussianAnnulus (N p/(2:ℝ)^j)*a p‖) ‖a p‖ := by
    by_cases hp : a p=0
    simp_all
    · simpa only [norm_mul,one_mul] using (gaussianAnnulus_partition_norm (N p) (hN p hp)).mul_right ‖a p‖
  apply Summable.of_norm
  pm_7792
  exact ⟨fun p=>(hs p).summable,by simpa only [fun p=>(hs p).tsum_eq] using ha.norm⟩

lemma annular_reassembly :
    (∑'j : ℕ,∑'p : α,gaussianAnnulus (N p/(2:ℝ)^j)*a p)=∑'p,a p := by
  rw [Summable.tsum_comm (f:=fun p : α=>fun j : ℕ=>gaussianAnnulus (N p/(2:ℝ)^j)*a p)
    (annular_reassembly_summable a N ha hN)]
  apply tsum_congr
  intro p
  by_cases hp : a p=0
  · simp [hp]
  · simpa only [one_mul] using ((gaussianAnnulus_partition (N p) (hN p hp)).mul_right (a p)).tsum_eq
end

section
variable (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
include S D Ψ
lemma gaussian_dyadic_correctedSummand
    (Z : ℝ) (hZ : 0<Z) (j : ℕ) (I J : Id) :
    correctedSummand S D Ψ (gaussianDyadicProfile Z j) ((2:ℝ)^j) I J =
      gaussianAnnulus ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)*
        correctedSummand S D Ψ gaussianCompletedProfile Z I J := by
  pm_1343 summand
  have hi : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : (0:ℝ)<Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hN := mul_pos hi (pow_pos hj 3)
  unfold correctedSummand markedSummand summand
  rw [gaussianDyadicProfile_Vstar _ _ _ (div_pos hN (by positivity)),
    gaussianCompleted_Vstar _ (div_pos hN hZ)]
  have he : (2:ℝ)^j*((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)/Z =
      (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/Z := by
    field_simp
  rw [he]
  ring

lemma gaussian_correctedSummand_norm_ge_one
    (Z : ℝ) (I J : Id)
    (h : correctedSummand S D Ψ gaussianCompletedProfile Z I J≠0) :
    1≤(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3 := by
  pm_6822 hI I
  pm_6822 hJ J
  have hi : 1≤Ideal.absNorm I := Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : 1≤Ideal.absNorm J := Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  exact_mod_cast one_le_mul_of_one_le_of_one_le hi (one_le_pow₀ hj)

theorem correctedGaussian_eq_tsum_dyadic
    (hΨ : ∀n,‖Ψ n‖≤1) (Z : ℝ) (hZ : 0<Z) :
    correctedCompletedT S D Ψ gaussianCompletedProfile Z =
      ∑'j : ℕ,correctedCompletedT S D Ψ (gaussianDyadicProfile Z j) ((2:ℝ)^j) := by
  unfold correctedCompletedT
  simp_rw [gaussian_dyadic_correctedSummand S D Ψ Z hZ]
  exact (annular_reassembly _ _ (gaussian_correctedSummand_summable S D Ψ hΨ Z hZ)
    (fun p=>gaussian_correctedSummand_norm_ge_one S D Ψ Z p.1 p.2)).symm
end

end SevenEighths.ProbePhysical
end

end OAI
