module
public import OAI.NumberTheory.DirichletL.Eisenstein.LocalCutoffs

@[expose] public section

namespace OAI

noncomputable section

open MulChar AddChar Filter Asymptotics MeasureTheory Real Finset Complex ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Set
open scoped BigOperators Topology FourierTransform SchwartzMap Classical LSeries.notation ArithmeticFunction.Moebius ContDiff
namespace CompletedGauss

section


theorem two_pow_clog_le_double (n : ℕ) (hn : 1≤n) : 2^Nat.clog 2 n≤2*n := by
  by_cases h : n=1
  · simp [h]
  have hn1 := lt_of_le_of_ne hn (Ne.symm h)
  calc
    _ = 2^(Nat.clog 2 n).pred*2 := by rw [←(Nat.succ_pred_eq_of_pos (Nat.clog_pos (by norm_num) hn1)),pow_succ]; rfl
    _ ≤ n*2 := Nat.mul_le_mul_right 2 (Nat.pow_pred_clog_lt_self (by norm_num : 1<2) hn1).le
    _ = _ := Nat.mul_comm _ _

open CanonicalQuadraticSieve

end
section

open CompletedDyadic

def completedRamifiedStep : ℝ := (3:ℝ)^(1/3:ℝ)

theorem completedRamifiedStep_gt_one : 1<completedRamifiedStep := Real.one_lt_rpow (by norm_num) (by norm_num)

theorem cusp_coefficient_normalization (m n b : ℝ) (hn : 0<n) (hb : 0<b) :
    (3:ℝ)^(m/6)*Real.sqrt b/Real.sqrt ((3:ℝ)^m*n*b^3)=
      1/((3:ℝ)^(m/3)*Real.sqrt n*b) := by
  have hroot : Real.sqrt (3^m)=3^(m/6)*3^(m/3) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul (by norm_num),←Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hbroot : Real.sqrt (b^3)=b*Real.sqrt b := by
    rw [show b^3=b^2*b by ring,Real.sqrt_mul (sq_nonneg b),Real.sqrt_sq hb.le]
  rw [Real.sqrt_mul (mul_nonneg (by positivity) hn.le),Real.sqrt_mul (by positivity),hroot,hbroot]
  field_simp

end

open CanonicalQuadraticSieve

end CompletedGauss

namespace InitialMeanSquare

section
open SecondPassArithmetic
open CanonicalQuadraticSieve (Admissible)

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end

open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm columnLog)

end InitialMeanSquare

namespace InitialMeanSquare
open SecondPassArithmetic SecondPassIntegration JointLogSeparation FirstPassCubeLabels

end InitialMeanSquare

end

end OAI
