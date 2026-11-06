module

public import OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedTerms

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open CompletedGauss ConcretePrimeRowBridge ProbePrimePower
variable (p : ActualEisensteinCubic.O) (hp : Prime p) [(Ideal.span {p}:Ideal ActualEisensteinCubic.O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p})≠2)

include hc in
theorem sourceRowTerm_central_nonstrict (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j e l k m : ℕ) (hj : j<6) (hk : k≤1)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1))
    (hstrict : ¬(e=1 ∧ l=0 ∧ k=1 ∧ m=0)) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1/2-x.re) := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ : 0<Q := by
    dsimp only [Q]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hm0 : (0:ℝ)≤m := Nat.cast_nonneg m
  have hzpos : 0<z.re := by rw [hz];norm_num
  have hzm : 0≤6*z.re*(m:ℝ) := by positivity
  have hzm1 (hm : m≠0) : 6*z.re≤6*z.re*(m:ℝ) := by
    have hm1 : (1:ℝ)≤m := by exact_mod_cast (by omega)
    nlinarith
  have hrelax (v : ℝ) : Q^v≤2*Q^v := by nlinarith [Real.rpow_nonneg hQ.le v]
  have hz0 (t k : ℕ) (ht : t≠0) : sourceScalar p hp hg t k (j+6*m)=
      positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (t-1) k (j+6*m) := by
    rw [sourceScalar,ite_eq_right ht]
  rcases hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · by_cases hm : m=0
      · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 2 0 m 5 (1/2-x.re)
        · have hs := even_base_kzero_norm p hp hg hc m j hj
          rw [ite_eq_left hm] at hs
          simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 6 0 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
            hs.trans (show Q^5≤2*Q^5 by simp_all)
        linarith
      · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 2 0 m 6 (1/2-x.re)
        · have hs := even_base_kzero_norm p hp hg hc m j hj
          rw [ite_eq_right hm] at hs
          simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 6 0 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
            hs.trans (show Q^6≤2*Q^6 by simp_all)
        grind
    · by_cases hm : m=0
      · subst m
        simp only [sourceRowTerm, sourceScalar, Nat.reduceMul, Nat.reduceEqDiff, ite_false, add_zero, even_base_kone_zero p hp hg hc j hj, sourceWeightedScalar, zero_mul, mul_zero, norm_zero]
        positivity
      · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 2 1 m 6 (1/2-x.re)
        · have hs := nonprincipal_kone_norm p hp hg hc 5 (j+6*m) (by decide) (by decide)
          simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 6 1 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
            hs.trans (show Q^6≤2*Q^6 by simp_all)
        grind
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 0 0 m (1/2) (1/2-x.re)
      · have hs := nonprincipal_kzero_norm p hp hg hc 0 (j+6*m) (by decide)
        simp only [pow_zero,one_mul,Real.sqrt_eq_rpow] at hs
        grind
      linarith
    · have hm : m≠0 := by intro hm;exact by omega
      apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 0 1 m (3/2) (1/2-x.re)
      · have hs := positiveScalar_norm_le p hp hg hc 0 1 (j+6*m) (by decide)
        simp only [Nat.zero_add,pow_one] at hs
        have he : 2*Q*Real.sqrt Q=2*Q^(3/2:ℝ) := by
          have ht := pow_mul_sqrt Q hQ 1
          norm_num at ht
          rw [mul_assoc,ht]
        grind
      grind
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 1 0 m (5/2) (1/2-x.re)
      · have hs := nonprincipal_kzero_norm p hp hg hc 2 (j+6*m) (by decide)
        rw [pow_mul_sqrt _ hQ] at hs
        grind
      linarith
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 1 1 m 3 (1/2-x.re)
      · have hs := nonprincipal_kone_norm p hp hg hc 2 (j+6*m) (by decide) (by decide)
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 3 1 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
          hs.trans (show Q^3≤2*Q^3 by simp_all)
      linarith
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 1 0 m (7/2) (1/2-x.re)
      · have hs := nonprincipal_kzero_norm p hp hg hc 3 (j+6*m) (by decide)
        rw [pow_mul_sqrt _ hQ] at hs
        grind
      linarith
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 1 1 m 4 (1/2-x.re)
      · have hs := nonprincipal_kone_norm p hp hg hc 3 (j+6*m) (by decide) (by decide)
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 4 1 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
          hs.trans (show Q^4≤2*Q^4 by simp_all)
      linarith

end SevenEighths.ProbeEuler
end

end OAI
