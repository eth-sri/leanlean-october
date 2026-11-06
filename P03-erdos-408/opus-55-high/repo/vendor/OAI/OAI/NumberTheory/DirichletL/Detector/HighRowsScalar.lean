module

public import OAI.NumberTheory.DirichletL.Detector.UnramifiedScalar

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePrimePower
open CompletedGauss ConcretePrimeRowBridge
variable (p : ActualEisensteinCubic.O) (hp : Prime p) [(Ideal.span {p} : Ideal ActualEisensteinCubic.O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p}) ≠ 2)
include hc

theorem row_even_kzero (r m j : ℕ) (hj : j<6) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r+5) 0 (j+6*m) =
      if r+1≤m then
        (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+5)*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)
      else if j=5 ∧ m=r then -(Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+5) else 0 := by
  rw [positiveScalar_kzero,actualSextic_primePowerGauss_at_pow p hp hg hc,
    ite_eq_left (by omega)]
  by_cases hm : r+1≤m
  · rw [ite_eq_left hm,ite_eq_left (by omega),ite_eq_left (by omega),pow_succ]
    ring
  grind

theorem row_squarefree_kone (r m j : ℕ) (hj : j<6) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r) 1 (j+6*m) =
      ((actualSextic (Ideal.span {p}) hg (-1))⁻¹ *
        primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1) *
        (if 6*r+1<j+6*m then
          (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r)*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)
        else if j=1 ∧ m=r then -(Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r) else 0) := by
  rw [positiveScalar_actual_table p hp hg hc,ite_eq_right (by positivity)]
  by_cases hpos : 1≤j+6*m
  · rw [ite_eq_left (by omega),gaussValuationTable,ite_eq_left (by omega)]
    congr 1
    grind
  simp_all

end SevenEighths.ProbePrimePower
end

end OAI
