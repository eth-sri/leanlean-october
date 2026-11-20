module

public import DedekindZetaZeroFree.Arithmetic.Kummer.FrequencyClassesAndCharacterRigidity

@[expose] public section

open scoped NumberField
open IsDedekindDomain UniqueFactorizationMonoid

namespace DedekindZetaZeroFree.Detector.Conductor.NormFactorization

theorem norm_le_exterior_prime_product
    (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (b : HeightOneSpectrum (𝓞 F) → ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
        (T : Finset (HeightOneSpectrum (𝓞 F))),
        (∀ v ∈ S, (normalizedFactors I).count v.asIdeal ≤ b v) →
        (∀ v ∉ S, (normalizedFactors I).count v.asIdeal ≤ 1) →
        (∀ v, v ∉ S → I ≤ v.asIdeal → v ∈ T) →
        (Ideal.absNorm I : ℝ) ≤
          C * (∏ v ∈ T, (Ideal.absNorm v.asIdeal : ℝ)) := by
  classical
  let U := hS.toFinset
  let M :=
    U.val.bind (fun v => Multiset.replicate (b v) v.asIdeal)
  have hM : M.prod ≠ ⊥ := by
    apply Multiset.prod_ne_zero
    intro hJ
    obtain ⟨v, hv, hvJ⟩ := Multiset.mem_bind.mp hJ
    exact v.ne_bot (Multiset.eq_of_mem_replicate hvJ).symm
  have hnormM := Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp hM)
  refine ⟨(Ideal.absNorm M.prod : ℝ), by positivity, ?_⟩
  intro I hI T hin hout hT
  let N := T.val.map HeightOneSpectrum.asIdeal
  have hsub : normalizedFactors I ≤ M + N := by
    apply Multiset.le_iff_count.mpr
    intro J
    by_cases hJ : J ∈ normalizedFactors I
    · let v := HeightOneSpectrum.ofPrime (prime_of_normalized_factor J hJ)
      have hvJ : v.asIdeal = J := rfl
      by_cases hvS : v ∈ S
      · have hrepl : Multiset.replicate (b v) J ≤ M := by
          simpa [M, hvJ] using (Multiset.le_bind U.val (by simpa [U] using hvS) :
            Multiset.replicate (b v) v.asIdeal ≤ M)
        have hcount := Multiset.le_iff_count.mp hrepl J
        simp only [Multiset.count_replicate_self] at hcount
        exact le_trans (hin v hvS) (le_trans hcount (by simp))
      · have hJN := Multiset.mem_map.mpr ⟨v, (hT v hvS ((Ideal.mem_normalizedFactors_iff hI).mp hJ).2), hvJ⟩
        have hcount : 1 ≤ N.count J := Multiset.one_le_count_iff_mem.mpr hJN
        exact le_trans (hout v hvS) (le_trans hcount (by simp))
    · simp [Multiset.count_eq_zero.mpr hJ]
  have hdvd : I ∣ M.prod * N.prod := by
    rw [← Ideal.prod_normalizedFactors_eq_self hI, ← Multiset.prod_add]
    exact Multiset.prod_dvd_prod_of_le hsub
  have hN : N.prod ≠ ⊥ := by
    apply Multiset.prod_ne_zero
    intro hJ
    obtain ⟨v, hv, heq⟩ := Multiset.mem_map.mp hJ
    exact v.ne_bot heq
  have hnorm : Ideal.absNorm I ≤ Ideal.absNorm M.prod * Ideal.absNorm N.prod := by
    apply Nat.le_of_dvd (Nat.mul_pos hnormM ?_) (by simpa using map_dvd Ideal.absNorm hdvd)
    exact Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp hN)
  have heq : (Ideal.absNorm N.prod : ℝ) = ∏ v ∈ T, (Ideal.absNorm v.asIdeal : ℝ) := by
    simp [N, ← map_multiset_prod, Multiset.map_map, Finset.prod_map_val]
  exact_mod_cast heq ▸ (show (Ideal.absNorm I : ℝ) ≤
      (Ideal.absNorm M.prod : ℝ) * (Ideal.absNorm N.prod : ℝ) by exact_mod_cast hnorm)

end DedekindZetaZeroFree.Detector.Conductor.NormFactorization
