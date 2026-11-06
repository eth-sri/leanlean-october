module

public import OAI.NumberTheory.DirichletL.Detector.GramJointMean

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeGramCommon
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

lemma common_radical_norm_le (C : ActualEisensteinCubic.O) (hC : C≠0) (P : ι→Id) (c : ι→ℕ)
    (hc : ∀i,1≤c i) (he : Ideal.span {C}=∏i,P i^c i) :
    Ideal.absNorm (∏i,P i)≤Ideal.absNorm (Ideal.span {C}) := by
  apply Nat.le_of_dvd (Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hC)))
  apply map_dvd Ideal.absNorm
  rw [he]
  exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _=>dvd_pow_self _ (by grind))

lemma jointPeriod_norm_bound (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (C k : ActualEisensteinCubic.O) (hC : C≠0) (hk0 : k≠0) (u : ActualEisensteinCubic.Oˣ) (a b : ℕ) (r : ActualEisensteinCubic.O)
    (hk : k=u.val*ConcretePrimeRowBridge.goodLambda^a*(2:ActualEisensteinCubic.O)^b*r) (P : ι→Id) (c : ι→ℕ)
    (hc : ∀i,1≤c i) (he : Ideal.span {C}=∏i,P i^c i) :
    Ideal.absNorm (jointPeriod S hS P r)≤
      Ideal.absNorm (jointFixedModulus S hS)*Ideal.absNorm (Ideal.span {C})*Ideal.absNorm (Ideal.span {k}) := by
  rw [jointPeriod,map_mul,map_mul]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (common_radical_norm_le C hC P c hc he))
    (numerator_good_norm_le u a b r k hk hk0)

lemma jointPeriod_nonzero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (C : ActualEisensteinCubic.O) (hC : C≠0) (P : ι→Id) (c : ι→ℕ)
    (hc : ∀i,1≤c i) (he : Ideal.span {C}=∏i,P i^c i) (r : ActualEisensteinCubic.O) (hr : r≠0) :
    jointPeriod S hS P r≠0 := by
  have hp : ∏i,P i≠(0:Id) := by
    intro hz
    have hd : (∏i,P i)∣Ideal.span {C} := by
      rw [he]
      exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _=>dvd_pow_self _ (by grind))
    rw [hz,zero_dvd_iff] at hd
    exact hC (Ideal.span_singleton_eq_bot.mp hd)
  exact mul_ne_zero (mul_ne_zero (jointFixedModulus_nonzero S hS) hp)
    (Ideal.span_singleton_eq_bot.not.mpr hr)

end SevenEighths.ProbeGramCommon
end

end OAI
