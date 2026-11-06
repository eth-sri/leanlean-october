module

public import OAI.NumberTheory.DirichletL.Descent.FirstProfileIdentity
public import OAI.NumberTheory.DirichletL.Descent.ProfileIntegral

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped Classical
open FourierBridge JointLogSeparation
noncomputable section

def firstCoordinates (a : Fin 7 → ℝ) (x y : ℝ) : Fin 9 → ℝ :=
  ![a 0,a 1,a 2,a 3,a 4,a 5,a 6,x,y]

def firstOuterPhase (h : Fin 9 → ℝ) (a : Fin 7 → ℝ) : ℂ :=
  ∏ i : Fin 7, logPhase (h ⟨i.val, by omega⟩) (a i)

theorem first_mode_split (a : Fin 7 → ℝ) (x y : ℝ)
    (v : Frequency × (Fin 9 → ℝ)) :
    pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope (firstCoordinates a x y) v.1 v.2 =
      firstOuterPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope v.1 v.2) a *
      logPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope v.1 v.2 7) x *
      logPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope v.1 v.2 8) y := by
  rw [pureProfileMode_height]
  simp [Fin.prod_univ_succ,firstCoordinates,firstOuterPhase]
  ring

variable {ι : Type*} [DecidableEq ι]
  (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

end
end SevenEighths.InverseMoment

end OAI
