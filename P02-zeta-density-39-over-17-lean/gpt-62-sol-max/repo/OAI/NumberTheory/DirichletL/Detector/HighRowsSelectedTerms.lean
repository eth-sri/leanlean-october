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
    (hx : (7/8:ℝ)≤x.re) (_hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (j e l k m : ℕ) (hj : j<6) (hk : k≤1)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1)) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by
  have hz0 : 0 ≤ z.re := by linarith
  have hB₀ := le_max_right (1-w.re) 0
  have hB₁ := le_max_left (1-w.re) 0
  have hzm : 0 ≤ 6*z.re*(m:ℝ) := by positivity
  have hzm1 (hm : m≠0) : 6*z.re ≤ 6*z.re*(m:ℝ) := by
    have : (1:ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    nlinarith
  exact sourceRowTerm_base_of_budgets p hp hg hc eta a rho x w z _ heta ha hρ j e l k m hj hk hf
    (by linarith) (fun hm => by linarith [hzm1 hm]) (fun hm => by linarith [hzm1 hm])
    (by linarith) (fun _ _ _ => by linarith) (by linarith) (by linarith) (by linarith) (by linarith)

end SevenEighths.ProbeEuler
end

end OAI
