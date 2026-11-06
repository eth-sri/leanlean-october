module
public import OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedTerms
import WeylPort.Analytic.RealLaplace

public section

namespace OAI

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
  pb_820
  have hzpos : 0<z.re := by rw [hz];norm_num
  pb_118
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · by_cases hm : m=0
      · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 2 0 m 5 (1/2-x.re)
        pm_3856
      · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 2 0 m 6 (1/2-x.re)
        pm_3855
    · by_cases hm : m=0
      · subst m
        pm_3862
        positivity
      · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 2 1 m 6 (1/2-x.re)
        pm_3854
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 0 0 m (1/2) (1/2-x.re)
      pm_3861
      pm_3852
    · have hm : m≠0 := by intro hm;exact hstrict ⟨rfl,rfl,rfl,hm⟩
      apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 0 1 m (3/2) (1/2-x.re)
      pm_3853
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        nlinarith [hzm1 hm]
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 1 0 m (5/2) (1/2-x.re)
      pm_3859
      pm_3852
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 1 1 m 3 (1/2-x.re)
      pm_3857
      pm_3852
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 1 0 m (7/2) (1/2-x.re)
      pm_3860
      pm_3852
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 1 1 m 4 (1/2-x.re)
      pm_3858
      pm_3852

end SevenEighths.ProbeEuler

end OAI
