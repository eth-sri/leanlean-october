module

public import OAI.NumberTheory.DirichletL.Detector.HighRowsFirstRamified

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in
theorem sourceRowTerm_selected_base (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (j e l k m : ℕ) (hj : j<6) (hk : k≤1)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1)) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by
  apply sourceRowTerm_base_bound p hp hg hc eta a rho x w z heta ha hρ j e l k m hj hk hf
  have hb0 := le_max_right (1-w.re) (0:ℝ)
  have hb1 := le_max_left (1-w.re) (0:ℝ)
  generalize hB : max (1-w.re) 0 = B at *
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
