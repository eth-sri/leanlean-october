module

public import OAI.NumberTheory.DirichletL.Descent.SecondDensityAssembly
public import OAI.NumberTheory.DirichletL.Inversion.SecondProfileUniform

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic



theorem balanced_density_integrable  g   g₁ g₂ b₃ 
     ρ   c₁ c₂ θ₁ θ₂ L  :
    Integrable (InverseSecondProfileUniform.density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L) := (full_density_integrable _ _ _ _).const_mul _

variable {κ ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})


end SevenEighths.InverseMoment

end OAI
