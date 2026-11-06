module
public import OAI.NumberTheory.DirichletL.Detector.HighRowsFirstRamified
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
lemma sourceRowTerm_norm_from_scalar_power (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (j e l k m : ℕ) (nu B : ℝ)
    (hs : ‖sourceScalar p hp hg (e+3*l) k (j+6*m)‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^nu)
    (he : nu-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ)≤B) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^B := by
  have hP : Prime (Ideal.span {p}:Ideal O) := Ideal.prime_span_singleton_iff.mpr hp
  pm_3851
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

include hc in
theorem sourceRowTerm_selected_base (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤x.re) (_hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (j e l k m : ℕ) (hj : j<6) (hk : k≤1)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1)) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by
  pb_820
  have hb0 : (0:ℝ)≤ max (1-w.re) 0 := le_max_right _ _
  have hb1 : 1-w.re≤ max (1-w.re) 0 := le_max_left _ _
  pb_118
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · by_cases hm : m=0
      · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 2 0 m 5 (-x.re+max (1-w.re) 0)
        pm_3856
      · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 2 0 m 6 (-x.re+max (1-w.re) 0)
        pm_3855
    · by_cases hm : m=0
      · subst m
        pm_3862
        positivity
      · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 2 1 m 6 (-x.re+max (1-w.re) 0)
        pm_3854
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 0 0 m (1/2) (-x.re+max (1-w.re) 0)
      pm_3861
      pm_3852
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 0 1 m (3/2) (-x.re+max (1-w.re) 0)
      pm_3853
      pm_3852
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 1 0 m (5/2) (-x.re+max (1-w.re) 0)
      pm_3859
      pm_3852
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 1 1 m 3 (-x.re+max (1-w.re) 0)
      pm_3857
      pm_3852
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 1 0 m (7/2) (-x.re+max (1-w.re) 0)
      pm_3860
      pm_3852
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 1 1 m 4 (-x.re+max (1-w.re) 0)
      pm_3858
      pm_3852

end SevenEighths.ProbeEuler

end OAI
