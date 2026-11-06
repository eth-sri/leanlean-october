module
public import OAI.NumberTheory.DirichletL.Detector.HighRowsSharpScalar
import WeylPort.Analytic.RealLaplace

public section

namespace OAI

open scoped Classical
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

lemma pow_mul_sqrt (Q : ℝ) (hQ : 0<Q) (n : ℕ) : Q^n*Real.sqrt Q=Q^((n:ℝ)+1/2) := by
  rw [Real.rpow_add hQ,Real.rpow_natCast,Real.sqrt_eq_rpow]

include hc in
include hc in
lemma sourceRowTerm_norm_from_scalar (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (j e l k m : ℕ) (nu : ℝ)
    (hs : ‖sourceScalar p hp hg (e+3*l) k (j+6*m)‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^nu)
    (he : nu-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ)≤0) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2 := by
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
    _ ≤ 2 := by
      have hh := Real.rpow_le_one_of_one_le_of_nonpos (show (1:ℝ)≤Ideal.absNorm (Ideal.span {p}) by linarith) he
      linarith

include hc in
set_option hygiene false in
macro "pb_118" : tactic => `(tactic| (
  have hzm : 0≤6*z.re*(m:ℝ) := by positivity
  have hzm1 (hm : m≠0) : 6*z.re≤6*z.re*(m:ℝ) := by
    have hm1 : (1:ℝ)≤ m := by exact_mod_cast (by omega : 1≤ m)
    nlinarith
  have hrelax (v : ℝ) : Q^v≤2*Q^v := by nlinarith [Real.rpow_nonneg hQ.le v]
  have hz0 (t k : ℕ) (ht : t≠0) : sourceScalar p hp hg t k (j+6*m)=
      positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (t-1) k (j+6*m) := by
    rw [sourceScalar,ite_eq_right ht]
  rcases hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩))
include hc in
include hc in
include hc in
include hc in
include hc in
include hc in
include hc in
include hc in
include hc in
include hc in
include hc in
include hc in
set_option hygiene false in
macro "pb_820" : tactic => `(tactic| (
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ : 0<Q := by
    dsimp only [Q]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hm0 : (0:ℝ)≤ m := Nat.cast_nonneg m))
include hc in
include hc in
include hc in
include hc in
include hc in
include hc in
include hc in
include hc in
include hc in
include hc in
include hc in
include hc in
include hc in
include hc in
theorem sourceRowTerm_first_base (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (51/100:ℝ)≤x.re) (_hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1≤x.re+w.re) (j e l k m : ℕ) (hj : j<6) (hk : k≤1)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1)) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2 := by
  pb_820
  pb_118
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · by_cases hm : m=0
      · apply sourceRowTerm_norm_from_scalar p hp hg hc eta a rho x w z heta ha hρ j 0 2 0 m 5
        pm_3856
      · apply sourceRowTerm_norm_from_scalar p hp hg hc eta a rho x w z heta ha hρ j 0 2 0 m 6
        pm_3855
    · by_cases hm : m=0
      · subst m
        pm_3862
        norm_num
      · apply sourceRowTerm_norm_from_scalar p hp hg hc eta a rho x w z heta ha hρ j 0 2 1 m 6
        pm_3854
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar p hp hg hc eta a rho x w z heta ha hρ j 1 0 0 m (1/2)
      pm_3861
      pm_3852
    · apply sourceRowTerm_norm_from_scalar p hp hg hc eta a rho x w z heta ha hρ j 1 0 1 m (3/2)
      pm_3853
      pm_3852
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar p hp hg hc eta a rho x w z heta ha hρ j 0 1 0 m (5/2)
      pm_3859
      pm_3852
    · apply sourceRowTerm_norm_from_scalar p hp hg hc eta a rho x w z heta ha hρ j 0 1 1 m 3
      pm_3857
      pm_3852
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar p hp hg hc eta a rho x w z heta ha hρ j 1 1 0 m (7/2)
      pm_3860
      pm_3852
    · apply sourceRowTerm_norm_from_scalar p hp hg hc eta a rho x w z heta ha hρ j 1 1 1 m 4
      pm_3858
      pm_3852

end SevenEighths.ProbeEuler

end OAI
