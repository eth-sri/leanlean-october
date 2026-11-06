module
public import OAI.NumberTheory.DirichletL.Descent.FirstCommonMeasure

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
open scoped EisensteinEis
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstCommonColumn (F D : Finset ι) (C : Finset ι → ℂ) (negative : Bool)
    (χ : RayCharacter) (ω : ℝ → ℂ) (X t : ℝ) (h : Eis) : ℂ :=
  supportConjugateSum (fun i => Ideal.span {p i}) hg (F\D)
    (fun U => (if negative then star (supportRay p χ (D∪U)) else supportRay p χ (D∪U)) *
      C (D∪U) * (if negative then star (ω (primeProductNorm p U/X)*
        logPhase t (Real.log (primeProductNorm p U/X))) else
        ω (primeProductNorm p U/X)*logPhase t (Real.log (primeProductNorm p U/X)))) h

theorem firstCommonColumn_pair (F D : Finset ι) (C₁ C₂ : Finset ι → ℂ)
    (r : RayCharacter × RayCharacter) (ω₁ ω₂ : ℝ → ℂ) (X₁ X₂ t₁ t₂ : ℝ) (h : Eis) :
    (∑ U ∈ (F\D).powerset, ∑ V ∈ (F\D).powerset,
      firstCommonCoefficient p hg C₁ C₂ r D U V h *
        (ω₁ (primeProductNorm p U/X₁)*ω₂ (primeProductNorm p V/X₂)) *
        logPhase t₁ (Real.log (primeProductNorm p U/X₁)) *
        logPhase t₂ (Real.log (primeProductNorm p V/X₂))) =
    star (firstCommonColumn p hg F D C₁ true r.1 ω₁ X₁ t₁ h) *
      firstCommonColumn p hg F D C₂ false r.2 ω₂ X₂ t₂ h := by
  simp only [firstCommonColumn,supportConjugateSum,star_sum,Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  simp only [firstCommonCoefficient,Bool.false_eq_true,ite_false,ite_true,star_mul,star_star]
  ring

def firstCommonOuterLog (A₁ A₂ C R : ℝ) (d h : Eis) (D : Finset ι) (s : Fin 9 → ℝ) : Fin 7 → ℝ :=
  ![Real.log (A₁/s 0),Real.log (A₂/s 1),Real.log (C/s 2),Real.log (‖eisEmbedding d‖^2/s 3),
    Real.log (R/s 4),Real.log (primeProductNorm p D/s 5),Real.log (‖eisEmbedding h‖^2/s 6)]

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem first_common_source_mode (A₁ A₂ C R : ℝ) (d h : Eis) (s : Fin 9 → ℝ)
    (j : FirstCommonIndex ι) (z : Frequency × (Fin 9 → ℝ)) :
    pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
      (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s) z.1 z.2 =
    firstOuterPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2)
      (firstCommonOuterLog p A₁ A₂ C R d h j.2.1 s) *
    logPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
      (Real.log (primeProductNorm p j.2.2.1/s 7)) *
    logPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
      (Real.log (primeProductNorm p j.2.2.2/s 8)) := by
  have hy : firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s =
      firstCoordinates (firstCommonOuterLog p A₁ A₂ C R d h j.2.1 s)
        (Real.log (primeProductNorm p j.2.2.1/s 7))
        (Real.log (primeProductNorm p j.2.2.2/s 8)) := by
    funext i
    fin_cases i <;> rfl
  rw [hy,first_mode_split]





