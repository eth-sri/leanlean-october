module

public import OAI.NumberTheory.DirichletL.Detector.HighRowsHolomorphic

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePrimePower
open CompletedGauss ConcretePrimeRowBridge
variable (p : ActualEisensteinCubic.O) (hp : Prime p) [(Ideal.span {p}:Ideal ActualEisensteinCubic.O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p})≠2)

include hc in
lemma primeGauss_actual_pow_norm (r : ℕ) (hr : r≠0) (hr6 : r<6) :
    ‖primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg^r) 1‖=
      Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ) := by
  let : Field (ActualEisensteinCubic.O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hn := localGamma_norm_one p hp.ne_zero hg hc r hr hr6
  rw [localGamma,ProbePhase.normalizedTraceGauss_eq_normalizedGauss] at hn
  simp only [ProbeGauss.normalizedGauss,norm_div,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] at hn
  have hQ : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hcard : (Fintype.card (ActualEisensteinCubic.O ⧸ Ideal.span {p}):ℝ)=Ideal.absNorm (Ideal.span {p}) := by
    rw [←Nat.card_eq_fintype_card];rfl
  rw [hcard] at hn
  have hn' := (div_eq_one_iff_eq (Real.sqrt_pos.mpr hQ).ne').mp hn
  simpa only [primeGauss,tsum_fintype,gaussSum,map_one,one_mul] using hn'

include hc in
lemma nonprincipal_kzero_norm (n j : ℕ) (hn : n<5) :
    ‖positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n 0 j‖≤
      (Ideal.absNorm (Ideal.span {p}):ℝ)^n*Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ) := by
  rw [positiveScalar_kzero,actualSextic_primePowerGauss_at_pow p hp hg hc,
    ite_eq_right (by omega)]
  split_ifs
  · rw [norm_mul,norm_pow,Complex.norm_natCast,primeGauss_actual_pow_norm p hp hg hc (n+1) (by omega) (by omega)]
  · simp only [norm_zero]
    positivity

include hc in
lemma nonprincipal_kone_norm (n j : ℕ) (hn : 0<n) (hn6 : n<6) :
    ‖positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n 1 j‖≤
      (Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1) := by
  rw [positiveScalar_actual_table p hp hg hc,ite_eq_right (by positivity)]
  by_cases hj : 1≤j
  · rw [ite_eq_left (by omega),gaussValuationTable,ite_eq_right (by omega)]
    split_ifs
    · rw [norm_mul,norm_mul,norm_inv,
        Complex.norm_eq_one_of_pow_eq_one (actualSextic_neg_one_sq _ hg) (by decide),inv_one,one_mul,
        primeGauss_actual_norm p hp.ne_zero hg hc,norm_mul,norm_pow,Complex.norm_natCast,
        primeGauss_actual_pow_norm p hp hg hc n (by omega) hn6]
      grind
    simp
  simp_all

include hc in
lemma even_base_kzero_norm (m j : ℕ) (hj : j<6) :
    ‖positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 5 0 (j+6*m)‖≤
      if m=0 then (Ideal.absNorm (Ideal.span {p}):ℝ)^5 else (Ideal.absNorm (Ideal.span {p}):ℝ)^6 := by
  have he := row_even_kzero p hp hg hc 0 m j hj
  norm_num only at he
  rw [he]
  by_cases hm : m=0
  · subst m
    norm_num only [ite_false, ite_true, and_true]
    split_ifs <;> simp
  · rw [ite_eq_left (by omega),ite_eq_right hm,norm_mul,norm_pow,Complex.norm_natCast]
    have hQ1 : (1:ℝ)≤Ideal.absNorm (Ideal.span {p}) := by
      have hh := SmoothMobiusCorrection.prime_norm_two_le
        ⟨Ideal.span {p},Ideal.prime_span_singleton_iff.mpr hp⟩
      change 2≤Ideal.absNorm (Ideal.span {p}) at hh
      exact_mod_cast (by omega)
    have hsub : ‖(Ideal.absNorm (Ideal.span {p}):ℂ)-1‖=(Ideal.absNorm (Ideal.span {p}):ℝ)-1 := by
      rw [←Complex.ofReal_natCast,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg (by linarith)]
    rw [hsub,show (Ideal.absNorm (Ideal.span {p}):ℝ)^6=(Ideal.absNorm (Ideal.span {p}):ℝ)^5*(Ideal.absNorm (Ideal.span {p}):ℝ) by ring]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

include hc in
lemma even_base_kone_zero (j : ℕ) (hj : j<6) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 5 1 j=0 := by
  rw [positiveScalar_actual_table p hp hg hc,ite_eq_right (by positivity)]
  by_cases hj1 : 1≤j
  · rw [ite_eq_left (by omega),gaussValuationTable,ite_eq_right (by omega),
      ite_eq_right (by omega),mul_zero]
  simp_all

end SevenEighths.ProbePrimePower
end

end OAI
