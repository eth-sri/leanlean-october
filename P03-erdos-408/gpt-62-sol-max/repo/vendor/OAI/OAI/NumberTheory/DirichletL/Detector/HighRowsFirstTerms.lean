module

public import OAI.IdealNorm
public import OAI.NumberTheory.DirichletL.Detector.HighRowsSharpScalar

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

lemma pow_mul_sqrt (Q : ℝ) (hQ : 0<Q) (n : ℕ) : Q^n*Real.sqrt Q=Q^((n:ℝ)+1/2) := by
  rw [Real.rpow_add hQ,Real.rpow_natCast,Real.sqrt_eq_rpow]

include hc in
lemma sourceRowTerm_norm_from_scalar_power (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (j e l k m : ℕ) (nu B : ℝ)
    (hs : ‖sourceScalar p hp hg (e+3*l) k (j+6*m)‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^nu)
    (he : nu-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ)≤B) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^B := by
  have hP : Prime (Ideal.span {p}:Ideal O) := Ideal.prime_span_singleton_iff.mpr hp
  have hQ2 : (2:ℝ)≤Ideal.absNorm (Ideal.span {p}) := by exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le ⟨_,hP⟩
  have hQ : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by linarith
  have hrho := Complex.norm_eq_one_of_pow_eq_one hρ (by decide : (6:ℕ)≠0)
  rw [sourceRowTerm,norm_mul,norm_div,norm_pow,norm_pow,hrho,one_pow,one_pow,div_self (by norm_num : (1:ℝ)≠0),one_mul]
  apply (sourceWeightedScalar_norm_le _ hQ eta a _ _ _ x w z _ heta ha
    (localGamma_norm_one p hp.ne_zero hg hc 1 (by decide) (by decide))
    (by rw [norm_star];exact localGamma_norm_one p hp.ne_zero hg hc 3 (by decide) (by decide))
    (Complex.norm_eq_one_of_pow_eq_one (actualSextic_neg_one_sq _ hg) (by decide)) e l k m).trans
  calc
    _ ≤ (2*(Ideal.absNorm (Ideal.span {p}):ℝ)^nu)*
      (Ideal.absNorm (Ideal.span {p}):ℝ)^(-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ)) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ = 2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(nu-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ)) := by
      rw [mul_assoc,←Real.rpow_add hQ]
      congr 2
      ring
    _ ≤ 2*(Ideal.absNorm (Ideal.span {p}):ℝ)^B := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.rpow_le_rpow_of_exponent_le (show (1:ℝ)≤Ideal.absNorm (Ideal.span {p}) by linarith) he

/-- The Gauss bound for the base term depends only on the scalar index `t`,
the marked bit `k`, and whether the height index `m` is zero. -/
def baseScalarExponent (t k m : ℕ) : ℝ :=
  if t = 6 then if m = 0 then 5 else 6
  else if k = 0 then (t : ℝ) - 1/2
  else if t = 1 then 3/2 else (t : ℝ)

include hc in
private lemma sourceScalar_base_norm (j t k m : ℕ) (hj : j < 6) (hk : k ≤ 1)
    (ht : t = 1 ∨ t = 3 ∨ t = 4 ∨ t = 6) :
    ‖sourceScalar p hp hg t k (j + 6*m)‖ ≤
      2 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ baseScalarExponent t k m := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ : 0 < Q := by
    dsimp only [Q]
    exact_mod_cast Ideal.absNorm_pos_of_ne_bot (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  have hrelax (v : ℝ) : Q^v ≤ 2*Q^v := by linarith [Real.rpow_nonneg hQ.le v]
  rw [sourceScalar,ite_eq_right (by omega : t ≠ 0)]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl | rfl
  · by_cases h6 : t = 6
    · subst t
      have hs := even_base_kzero_norm p hp hg hc m j hj
      apply le_trans _ (hrelax _)
      by_cases hm : m = 0 <;> simpa [Q,hm,baseScalarExponent,Real.rpow_ofNat] using hs
    · have hs := nonprincipal_kzero_norm p hp hg hc (t-1) (j+6*m) (by omega)
      rw [pow_mul_sqrt _ hQ, Nat.cast_sub (by omega : 1 ≤ t), Nat.cast_one,
        show (t:ℝ)-1+1/2=(t:ℝ)-1/2 by ring] at hs
      simpa [Q,baseScalarExponent,h6] using hs.trans (hrelax _)
  · by_cases h6 : t = 6
    · subst t
      by_cases hm : m = 0
      · subst m
        rw [show j+6*0=j by simp, even_base_kone_zero p hp hg hc j hj, norm_zero]
        positivity
      · have hs := nonprincipal_kone_norm p hp hg hc 5 (j+6*m) (by decide) (by decide)
        apply le_trans _ (hrelax _)
        simpa [Q,hm,baseScalarExponent,Real.rpow_ofNat] using hs
    · by_cases h1 : t = 1
      · subst t
        have hs := positiveScalar_norm_le p hp hg hc 0 1 (j+6*m) (by decide)
        have hpow : Q*Real.sqrt Q = Q^(3/2:ℝ) := by
          convert pow_mul_sqrt Q hQ 1 using 1 <;> norm_num
        simp only [Nat.zero_add, pow_one, mul_assoc] at hs
        change _ ≤ 2 * Q ^ baseScalarExponent 1 1 m
        rw [show baseScalarExponent 1 1 m = 3/2 by simp [baseScalarExponent], ← hpow]
        exact hs
      · have hs := nonprincipal_kone_norm p hp hg hc (t-1) (j+6*m) (by omega) (by omega)
        apply le_trans _ (hrelax _)
        simpa only [baseScalarExponent,ite_eq_right h6,ite_eq_right h1,ite_eq_right (by decide : (1:ℕ) ≠ 0),
          Real.rpow_natCast,Nat.sub_add_cancel (by omega : 1 ≤ t)] using hs

include hc in
lemma sourceRowTerm_base_bound (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (j e l k m : ℕ) (hj : j<6) (hk : k≤1)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1))
    (B : ℝ)
    (he : baseScalarExponent (e+3*l) k m-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-
      w.re*(k:ℝ)-6*z.re*(m:ℝ) ≤ B) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖ ≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^B :=
  sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j e l k m _ B
    (sourceScalar_base_norm p hp hg hc j _ k m hj hk (by omega)) he

include hc in
theorem sourceRowTerm_first_base (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1≤x.re+w.re) (j e l k m : ℕ) (hj : j<6) (hk : k≤1)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1)) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2 := by
  suffices h : ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖ ≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(0:ℝ) by simpa using h
  apply sourceRowTerm_base_bound p hp hg hc eta a rho x w z heta ha hρ j e l k m hj hk hf
  have hz0 : 0 ≤ z.re := by linarith
  have hzm : 0 ≤ 6*z.re*(m:ℝ) := by positivity
  have hzm1 (hm : m ≠ 0) : 6*z.re ≤ 6*z.re*(m:ℝ) := by
    simpa only [mul_one] using (mul_le_mul_of_nonneg_left
      (show (1:ℝ) ≤ m by exact_mod_cast (by omega : 1 ≤ m)) (show 0 ≤ 6*z.re by positivity))
  rcases hf with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl | rfl <;>
    by_cases hm : m = 0
  all_goals first | (subst m; norm_num [baseScalarExponent] <;> nlinarith) |
    (norm_num [baseScalarExponent,hm] <;> nlinarith [hzm1 hm])

end SevenEighths.ProbeEuler
end

end OAI
