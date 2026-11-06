module

public import OAI.NumberTheory.DirichletL.Detector.HighRowsRegion

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePrimePower
open CompletedGauss ConcretePrimeRowBridge CubicEisenstein ConcreteTraceCRT

lemma primeGauss_norm_le (p : ActualEisensteinCubic.O) (hp : p≠0)
    (χ : MulChar (ActualEisensteinCubic.O ⧸ Ideal.span {p}) ℂ) (h : ActualEisensteinCubic.O) :
    ‖primeGauss p hp χ h‖≤(Ideal.absNorm (Ideal.span {p}):ℝ) := by
  let := finite_quotient_span hp
  let : Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  rw [primeGauss,tsum_fintype]
  calc
    _ ≤ ∑ x : ActualEisensteinCubic.O ⧸ Ideal.span {p},‖χ x*quotientTrace p hp (Ideal.Quotient.mk _ h*x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : ActualEisensteinCubic.O ⧸ Ideal.span {p},(1:ℝ) := Finset.sum_le_sum fun x _=>by
      rw [norm_mul,(quotientTrace p hp).norm_apply,mul_one]
      exact QuadraticInitialBound.norm_finite_character_le_one χ x
    _ = _ := by simp [Ideal.absNorm_apply, Submodule.cardQuot_apply]

lemma primeGauss_actual_norm (p : ActualEisensteinCubic.O) (hp : p≠0) [(Ideal.span {p}:Ideal ActualEisensteinCubic.O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p})≠2) :
    ‖primeGauss p hp (actualSextic (Ideal.span {p}) hg) 1‖=
      Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ) := by
  let : Field (ActualEisensteinCubic.O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hn := localGamma_norm_one p hp hg hc 1 (by decide) (by decide)
  rw [localGamma,ProbePhase.normalizedTraceGauss_eq_normalizedGauss] at hn
  simp only [pow_one,ProbeGauss.normalizedGauss,norm_div,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] at hn
  have hQ : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp))
  have hcard : (Fintype.card (ActualEisensteinCubic.O ⧸ Ideal.span {p}):ℝ)=Ideal.absNorm (Ideal.span {p}) := by
    rw [←Nat.card_eq_fintype_card];rfl
  rw [hcard] at hn
  have hn' := (div_eq_one_iff_eq (Real.sqrt_pos.mpr hQ).ne').mp hn
  simpa only [primeGauss,tsum_fintype,gaussSum,map_one,one_mul] using hn'

lemma gaussValuationTable_norm_le (Q : ℝ) (hQ : 1≤Q) (G : ℂ) (hG : ‖G‖≤Q)
    (r n j : ℕ) : ‖gaussValuationTable (Q:ℂ) G r n j‖≤2*Q^(n+1) := by
  have hQ0 : 0≤Q := by linarith
  have hn : Q^n≤Q^(n+1) := by simpa only [pow_succ] using
    (le_mul_of_one_le_right (by positivity) hQ)
  have hpow (a : ℕ) : ‖(Q:ℂ)^a‖=Q^a := by simp [abs_of_nonneg hQ0]
  have hi (a : ℕ) : ‖(if a≤j then (Q:ℂ)^a else 0)‖≤Q^a := by
    split_ifs
    · simp_all
    · simp_all
  unfold gaussValuationTable
  by_cases hr : 6∣r
  · rw [ite_eq_left hr]
    exact (norm_sub_le _ _).trans (by grind)
  · rw [ite_eq_right hr]
    by_cases hj : j=n
    · rw [ite_eq_left hj,norm_mul,hpow]
      calc
        _ ≤ Q^n*Q := mul_le_mul_of_nonneg_left hG (by positivity)
        _ ≤ 2*Q^(n+1) := by rw [←pow_succ];nlinarith [pow_nonneg hQ0 (n+1)]
    simp_all

lemma positiveScalar_norm_le (p : ActualEisensteinCubic.O) (hp : Prime p) [(Ideal.span {p}:Ideal ActualEisensteinCubic.O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p})≠2)
    (n k j : ℕ) (hk : k≤1) :
    ‖positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k j‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)*
        (Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ))^k := by
  have hP := Ideal.prime_span_singleton_iff.mpr hp
  have hQ : (1:ℝ)≤Ideal.absNorm (Ideal.span {p}) := by
    have hh := SmoothMobiusCorrection.prime_norm_two_le ⟨_,hP⟩
    change 2≤Ideal.absNorm (Ideal.span {p}) at hh
    exact_mod_cast (by omega)
  have ht (r j : ℕ) := gaussValuationTable_norm_le (Ideal.absNorm (Ideal.span {p}):ℝ) hQ
    (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg^r) 1)
    (primeGauss_norm_le p hp.ne_zero _ _) r n j
  have ho :=
    Complex.norm_eq_one_of_pow_eq_one (actualSextic_neg_one_sq _ hg) (by decide)
  rw [positiveScalar_actual_table p hp hg hc]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
  · simpa only [ite_true,pow_zero,mul_one,Complex.ofReal_natCast] using ht (n+1) j
  · simp only [Nat.one_ne_zero,ite_false,true_and]
    split_ifs
    · rw [norm_mul,norm_mul,norm_inv,ho,inv_one,one_mul,primeGauss_actual_norm p hp.ne_zero hg hc]
      simpa only [pow_one,mul_comm,Complex.ofReal_natCast] using
        mul_le_mul_of_nonneg_left (ht n (j-1)) (Real.sqrt_nonneg (Ideal.absNorm (Ideal.span {p}):ℝ))
    · simp only [norm_zero,pow_one]
      positivity

end SevenEighths.ProbePrimePower
end

end OAI
