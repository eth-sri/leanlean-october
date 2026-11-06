module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.UnramifiedScalar

@[expose] public section

namespace OAI


open scoped Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
include hc

section
variable (r m j : ℕ) (hj : j<6)
include r m j hj

theorem row_even_kzero     :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r+5) 0 (j+6*m) =
      if r+1≤m then
        (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+5)*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)
      else if j=5 ∧ m=r then -(Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+5) else 0 := by
  rw [positiveScalar_kzero,actualSextic_primePowerGauss_at_pow p hp hg hc,
    ite_eq_left (by omega : 6∣6*r+5+1)]
  by_cases hm : r+1≤m
  · rw [ite_eq_left hm,ite_eq_left (by omega),ite_eq_left (by omega),pow_succ]
    ring
  grind

theorem row_squarefree_kone     :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r) 1 (j+6*m) =
      ((actualSextic (Ideal.span {p}) hg (-1))⁻¹ *
        primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1) *
        (if 6*r+1<j+6*m then
          (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r)*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)
        else if j=1 ∧ m=r then -(Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r) else 0) := by
  rw [positiveScalar_actual_table p hp hg hc,ite_eq_right (by decide : (1:ℕ)≠0)]
  by_cases hpos : 1≤j+6*m
  · rw [ite_eq_left ⟨rfl,hpos⟩,gaussValuationTable,ite_eq_left (by omega : 6∣6*r)]
    congr 1
    grind
  · rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega),mul_zero]

end

end SevenEighths.ProbePrimePower


end OAI
