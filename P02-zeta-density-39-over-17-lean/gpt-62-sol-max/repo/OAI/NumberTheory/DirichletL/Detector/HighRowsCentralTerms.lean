module
public import OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedTerms

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
theorem sourceRowTerm_central_nonstrict (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j e l k m : ℕ) (hj : j<6) (hk : k≤1)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1))
    (hstrict : ¬(e=1 ∧ l=0 ∧ k=1 ∧ m=0)) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1/2-x.re) := by
  have hz0 : 0 ≤ z.re := by linarith
  have hzm : 0 ≤ 6*z.re*(m:ℝ) := by positivity
  have hzm1 (hm : m≠0) : 6*z.re ≤ 6*z.re*(m:ℝ) := by
    have : (1:ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    nlinarith
  exact sourceRowTerm_base_of_budgets p hp hg hc eta a rho x w z _ heta ha hρ j e l k m hj hk hf
    (by linarith) (fun hm => by linarith [hzm1 hm]) (fun hm => by linarith [hzm1 hm])
    (by linarith) (fun he hl hk => by linarith [hzm1 (fun hm => hstrict ⟨he,hl,hk,hm⟩)])
    (by linarith) (by linarith) (by linarith) (by linarith)

end SevenEighths.ProbeEuler
end

end OAI
