module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.Kernel

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.LowRowKernelDefinitions

noncomputable section

open DedekindZetaZeroFree

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def Iz (u : D.Row) (ξ w : ℂ) (v Z : ℝ) : ℂ :=
  comparisonVerticalIntegral v (fun z => PoissonKernel.K D u ξ w z Z)

def Iwz (u : D.Row) (ξ : ℂ) (y v Z : ℝ) : ℂ :=
  comparisonVerticalIntegral y (fun w => Iz D u ξ w v Z)







end

end DedekindZetaZeroFree.Quantitative.LowRowKernelDefinitions
