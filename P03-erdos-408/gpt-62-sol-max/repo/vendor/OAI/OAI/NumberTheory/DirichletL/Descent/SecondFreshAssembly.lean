module

public import OAI.NumberTheory.DirichletL.Descent.SecondSeparatedColumns
public import OAI.NumberTheory.DirichletL.Descent.SecondFreshMeasure

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory FourierBridge JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondSeparatedPair (F : Finset ι) (x : SecondProfileData ι)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G₀ E₀ V₀ K₀ X₀ : ℝ) (v : Frequency × (Fin 6 → ℝ)) : ℂ :=
  let h := profileHeight secondLeftSlope secondRightSlope secondKernelSlope v.1 v.2
  secondOuterPhase h
    (secondRelativeLog (secondActualNorms p x ∅ ∅) G₀ E₀ V₀ K₀ X₀) *
  star (canonicalMarkedSplit p hp hcop hg F x.overlap x.extractedLeft x.rayLeft
    x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor x.frequency
    slots₁ lists₁ a₁ (childLogTest ω₁ (-h 4)) (primeProductNorm p x.overlap*X₀)) *
  canonicalMarkedSplit p hp hcop hg F x.overlap x.extractedRight x.rayRight
    x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor (-x.frequency)
    slots₂ lists₂ a₂ (childLogTest ω₂ (h 5)) (primeProductNorm p x.overlap*X₀)

theorem actual_second_full_mode_columns (F : Finset ι) (x : SecondProfileData ι)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G₀ E₀ V₀ K₀ X₀ : ℝ) (v : Frequency × (Fin 6 → ℝ)) :
    (∑ N ∈ (F \ x.overlap).powerset, ∑ M ∈ (F \ x.overlap).powerset,
      secondActualCoefficient p hp hcop hg x slots₁ slots₂ lists₁ lists₂ a₁ a₂ N M *
        (star (ω₁ (primeProductNorm p N/X₀)) * ω₂ (primeProductNorm p M/X₀)) *
        pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
          (secondRelativeLog (secondActualNorms p x N M) G₀ E₀ V₀ K₀ X₀) v.1 v.2) =
      secondSeparatedPair p hp hcop hg F x slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v := by
  let h := profileHeight secondLeftSlope secondRightSlope secondKernelSlope v.1 v.2
  let O := secondOuterPhase h (secondRelativeLog (secondActualNorms p x ∅ ∅) G₀ E₀ V₀ K₀ X₀)
  calc
    _ = O * (∑ N ∈ (F \ x.overlap).powerset, ∑ M ∈ (F \ x.overlap).powerset,
        secondActualCoefficient p hp hcop hg x slots₁ slots₂ lists₁ lists₂ a₁ a₂ N M *
          (star (ω₁ (primeProductNorm p N/X₀)) * ω₂ (primeProductNorm p M/X₀)) *
          logPhase (h 4) (Real.log (primeProductNorm p N/X₀)) *
          logPhase (h 5) (Real.log (primeProductNorm p M/X₀))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro N hN
      apply Finset.sum_congr rfl
      intro M hM
      have hm : pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
          (secondRelativeLog (secondActualNorms p x N M) G₀ E₀ V₀ K₀ X₀) v.1 v.2 =
          O * logPhase (h 4) (Real.log (primeProductNorm p N/X₀)) *
            logPhase (h 5) (Real.log (primeProductNorm p M/X₀)) := by
        rw [second_mode_split]
        simp [secondOuterPhase,secondRelativeLog,secondRelativeNorm,secondActualNorms,O,h]
      rw [hm]
      ring
    _ = _ := by
      rw [actual_second_columns_separated]
      simp only [secondSeparatedPair,h,O,mul_assoc]

end
end SevenEighths.InverseMoment

end OAI
