module

public import Mathlib
public import DedekindZetaZeroFree.Adeles.Approximation.IntegralProductCRTDensity

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open NumberField IsDedekindDomain

variable (F : Type*) [Field F] [NumberField F]

abbrev finiteIntegralAdeles :=
  (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletionIntegers F

def integralDiagonal :
    𝓞 F →+* finiteIntegralAdeles F :=
  Pi.ringHom (fun v => algebraMap (𝓞 F) (v.adicCompletionIntegers F))

theorem integralCompletion_dense :
    DenseRange (integralDiagonal F) := denseRange_ringOfIntegers_integralDiagonal F

end
end DedekindZetaZeroFree
