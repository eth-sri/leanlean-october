module

public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceCanonicalData
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceWindow
public import OAI.NumberTheory.DirichletL.Moments.ConjugateWindow

@[expose] public section

namespace OAI

section
open scoped Classical BigOperators ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentGaussEnergy CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentSecondSectorColumns CenteredMomentConjugateWindow
open CenteredMomentSecondHeightFamily CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentFirstColumns CenteredMomentChildAssembly CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentCommonSupport RayFourExpansion IdealMobiusDivisorSum
open FourierBridge

variable {ι:Type*}[Fintype ι]


lemma element_norm  Q C  hC  S  I :
    ‖eisEmbedding (element Q C hC S I)‖^2=(Ideal.absNorm (I:Ideal ActualEisensteinCubic.O):ℝ):=by
  rw [eisEmbedding_norm_sq_eq_absNorm_span,element_span]

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
