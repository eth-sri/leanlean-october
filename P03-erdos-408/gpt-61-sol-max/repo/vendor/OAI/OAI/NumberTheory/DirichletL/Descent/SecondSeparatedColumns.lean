module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Descent.ActualSecondUniform
public import OAI.NumberTheory.DirichletL.Descent.FreshWindows

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open FourierBridge JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section


def secondOuterPhase (h y : Fin 6 → ℝ)  :=
  logPhase (h 0) (y 0) * logPhase (h 1) (y 1) *
    logPhase (h 2) (y 2) * logPhase (h 3) (y 3)

def childLogTest (ω : ℝ → ℂ) (h : ℝ) (y : ℝ)  :=
  ω y * logPhase h (Real.log y)

lemma second_mode_split  y   t   u  :
    pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y t u =
      secondOuterPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope t u) y *
        logPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope t u 4) (y 4) *
        logPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope t u 5) (y 5) := by
  rw [pureProfileMode_height]
  simp only [Fin.prod_univ_succ, secondOuterPhase]
  simp only [Fin.succ,  Fin.val_mk]
  norm_num
  ring

lemma secondOuterPhase_norm  h y  : ‖secondOuterPhase h y‖ = 1 := by
  simp only [secondOuterPhase,norm_mul,logPhase_norm,mul_one]

lemma second_fresh_scale {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O)
    (hp : ∀ i, p i ≠ 0)  V N  (hVN : Disjoint V N)  X  :
    primeProductNorm p (V ∪ N)/(primeProductNorm p V*X) = primeProductNorm p N/X := by
  rw [primeProductNorm_union p V N hVN]
  field_simp [(primeProductNorm_pos p hp V).ne']

theorem actual_second_columns_separated {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F : Finset ι) (x : SecondProfileData ι) (slots₁ slots₂ : Finset σ)
     lists₁ lists₂   a₁ a₂ 
     ω₁ ω₂   X   h₁ h₂  :
    (∑ N ∈ (F \ x.overlap).powerset, ∑ M ∈ (F \ x.overlap).powerset,
      secondActualCoefficient p hp hcop hg x slots₁ slots₂ lists₁ lists₂ a₁ a₂ N M *
        (star (ω₁ (primeProductNorm p N/X)) * ω₂ (primeProductNorm p M/X)) *
        logPhase h₁ (Real.log (primeProductNorm p N/X)) *
        logPhase h₂ (Real.log (primeProductNorm p M/X))) =
    star (canonicalMarkedSplit p hp hcop hg F x.overlap x.extractedLeft x.rayLeft
      x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor x.frequency
      slots₁ lists₁ a₁ (childLogTest ω₁ (-h₁)) (primeProductNorm p x.overlap*X)) *
      canonicalMarkedSplit p hp hcop hg F x.overlap x.extractedRight x.rayRight
      x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor (-x.frequency)
      slots₂ lists₂ a₂ (childLogTest ω₂ h₂) (primeProductNorm p x.overlap*X) := by
  rw [← secondChildKernelPair_separated_marked]
  unfold secondChildKernelPair
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  have hVN : Disjoint x.overlap N := by
    apply Finset.disjoint_left.mpr
    grind
  have hVM : Disjoint x.overlap M := by
    apply Finset.disjoint_left.mpr
    grind
  dsimp only
  rw [second_fresh_scale p hp x.overlap N hVN,second_fresh_scale p hp x.overlap M hVM]
  simp only [secondActualCoefficient,childLogTest,secondChildColumn,
    star_mul,SecondPassIntegration.logPhase_conjugate,neg_neg,mul_one]
  ring

end
end SevenEighths.InverseMoment

end OAI
