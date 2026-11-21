module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.NormalizedProbeArithmeticData
public import DedekindZetaZeroFree.LFunctions.Hecke.DirichletSeriesRightEdgeBounds
public import DedekindZetaZeroFree.LFunctions.Hecke.EulerLogarithm
public import DedekindZetaZeroFree.LFunctions.Hecke.PrincipalIncompleteEulerNonvanishing

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalNumerator
noncomputable section
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

private theorem prime_log_pos (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    0 < Real.log (idealNorm v.asIdeal) := by
  apply Real.log_pos
  dsimp [idealNorm]
  exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v

private theorem prime_term_norm_le (R : PrincipalMellin.ActualRecipe S η)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {a : ℝ} {s : ℂ} (hs : a ≤ s.re) :
    ‖R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s)‖ ≤
      Real.exp (-a * Real.log (idealNorm v.asIdeal)) := by
  rw [norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) (RayUnitary.ray_character_norm_le_one F
    R.A.modulus R.A.modulus_ne_zero R.target v.asIdeal)).trans ?_
  rw [MellinZeroFree.norm_comparisonRealPower, Complex.neg_re]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hs) (prime_log_pos v).le)

theorem finiteDeletion_mask_norm_le (R : PrincipalMellin.ActualRecipe S η) {s : ℂ}
    (hs : 0 ≤ s.re) :
    ‖∏ v ∈ R.A.Sf, (1 - R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))‖ ≤
      (2 : ℝ) ^ R.A.Sf.card := by
  rw [norm_prod, ← Finset.prod_const]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro v _
  have h := prime_term_norm_le R v hs
  simp only [neg_zero, zero_mul, Real.exp_zero] at h
  exact (norm_sub_le _ _).trans (by rw [norm_one]; linarith)

theorem rightHalfPlane_bound (R : PrincipalMellin.ActualRecipe S η)
    (a : ℝ) (ha : 1 < a) :
    ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ, a ≤ s.re → ‖R.L s‖ ≤ B := by
  let C := idealAbsoluteSum F a
  have hC : 0 ≤ C := by
    unfold C idealAbsoluteSum
    exact tsum_nonneg (fun I => by unfold idealAbsoluteWeight; split_ifs <;> positivity)
  refine ⟨(C + 1) * 2 ^ R.A.Sf.card, by positivity, ?_⟩
  intro s hs
  have hfull : ‖R.continuation.L s‖ ≤ C :=
    heckeDirichlet_hasSum_norm_le F a ha R.A.modulus R.A.modulus_ne_zero
      R.target s hs _ (R.continuation.series s (ha.trans_le hs))
  change ‖R.continuation.L s * ∏ v ∈ R.A.Sf,
    (1 - R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul (hfull.trans (by dsimp [C]; linarith))
    (finiteDeletion_mask_norm_le R (by linarith)) (norm_nonneg _) (by positivity)

theorem rightHalfPlane_reciprocal_bound
    (R : PrincipalMellin.ActualRecipe S η) (a : ℝ) (ha : 1 < a) :
    ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ, a ≤ s.re → ‖(R.L s)⁻¹‖ ≤ B := by
  let coeff : ExteriorIdeal (⊤ : Ideal (NumberField.RingOfIntegers F)) → ℂ :=
    fun I => R.target I.val
  let M : ℝ := Real.exp ((3 / 2 : ℝ) *
    ∑' I : NonzeroIdeal F, (idealNorm I.val) ^ (-a))
  have hM : 0 < M := Real.exp_pos _
  have hfull : ∀ s : ℂ, a ≤ s.re → ‖(R.continuation.L s)⁻¹‖ ≤ M := by
    intro s hs
    have hexp : Complex.exp (HeckeLogProof.eulerLog coeff s) = R.continuation.L s := by
      rw [HeckeLogProof.exp_eulerLog _
        (HeckeLogProof.ray_isCoefficient R.A.modulus R.A.modulus_ne_zero R.target)
        s (ha.trans_le hs)]
      have hsupport : Function.support (fun I : Ideal (NumberField.RingOfIntegers F) =>
          R.target I * (Ideal.absNorm I : ℂ) ^ (-s)) ⊆
          {I : Ideal (NumberField.RingOfIntegers F) | I ≠ ⊥ ∧ I ⊔ ⊤ = ⊤} := by
        intro I hI
        simp only [Function.mem_support] at hI
        refine ⟨?_, by simp⟩
        intro hzero
        have hη : R.target I = 0 := (R.target.eq_zero_iff' I).mpr (Or.inl hzero)
        exact hI (by simpa only [hη, zero_mul])
      exact ((hasSum_subtype_iff_of_support_subset hsupport).mpr
        (R.continuation.series s (ha.trans_le hs))).tsum_eq
    rw [← hexp, ← Complex.exp_neg, Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have h := HeckeLogProof.eulerLog_norm_le coeff
      (HeckeLogProof.ray_isCoefficient R.A.modulus R.A.modulus_ne_zero R.target)
      a ha s hs
    rw [Complex.neg_re]
    exact ((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans h
  let B (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :=
    1 - Real.exp (-a * Real.log (idealNorm v.asIdeal))
  have hB (v) : 0 < B v := sub_pos.mpr (Real.exp_lt_one_iff.mpr
    (mul_neg_of_neg_of_pos (by linarith) (prime_log_pos v)))
  refine ⟨M * ∏ v ∈ R.A.Sf, (B v)⁻¹,
    mul_pos hM (Finset.prod_pos (fun v _ => inv_pos.mpr (hB v))), ?_⟩
  intro s hs
  have hlocal (v) : ‖(1 - R.target v.asIdeal *
      comparisonRealPower (idealNorm v.asIdeal) (-s))⁻¹‖ ≤ (B v)⁻¹ := by
    rw [norm_inv]
    apply inv_anti₀ (hB v)
    have h := norm_sub_norm_le (1 : ℂ)
      (R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))
    rw [norm_one] at h
    dsimp [B]
    linarith [prime_term_norm_le R v hs]
  change ‖(R.continuation.L s * ∏ v ∈ R.A.Sf,
    (1 - R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s)))⁻¹‖ ≤ _
  rw [mul_inv_rev, norm_mul]
  calc
    _ ≤ (∏ v ∈ R.A.Sf, (B v)⁻¹) * M := by
      apply mul_le_mul
      · rw [← Finset.prod_inv_distrib, norm_prod]
        exact Finset.prod_le_prod₀ (fun v hv => norm_nonneg _) (fun v hv => hlocal v)
      · exact hfull s hs
      · exact norm_nonneg _
      · exact (Finset.prod_pos (fun v _ => inv_pos.mpr (hB v))).le
    _ = _ := mul_comm _ _

end
end DedekindZetaZeroFree.PrincipalNumerator
