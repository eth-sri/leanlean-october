module

public import DedekindZetaZeroFree.Adeles.Approximation.IntegralLocalCongruences
public import DedekindZetaZeroFree.Adeles.Approximation.IntegralCompletionCRT
public import ClassFieldTheory.All

@[expose] public section

noncomputable section
open scoped NumberField
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.TraceBaseChange

variable (F : Type*) [Field F] [NumberField F]

alias integralProduct_dense := DedekindZetaZeroFree.integralCompletion_dense

end DedekindZetaZeroFree.TraceBaseChange

end
