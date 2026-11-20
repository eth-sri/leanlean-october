module
public import OAI.NumberTheory.DirichletL.Arithmetic.PrincipalIdealFamily
public import OAI.NumberTheory.DirichletL.Descent.CanonicalChildSupport
public import OAI.NumberTheory.DirichletL.Descent.FirstLabelCellStep

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CanonicalQuadraticSieve InverseInitialClippedColumns InverseSecondFibers InverseSecondSourceBlocks CanonicalCoefficientClass InverseMomentFirstLabelCell InverseMomentFirstChildWindows InverseFirstGlobalCaps
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]
variable (p:ι→O)(hp:∀i,p i≠0)[OAI.PrincipalIdealFamily.Maximal p]
variable (hcop:OAI.PrincipalIdealFamily.PairwiseCoprime p)
variable (hg:OAI.PrincipalIdealFamily.Avoids p ConcretePrimeRowBridge.goodLambda)

end SevenEighths.InverseMoment

end

end OAI
