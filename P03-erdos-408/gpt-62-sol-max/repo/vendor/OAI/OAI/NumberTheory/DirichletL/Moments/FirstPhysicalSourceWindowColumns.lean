module

public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceOriginalColumn
public import OAI.NumberTheory.DirichletL.Moments.HeckeWindowEnergy
public import OAI.NumberTheory.DirichletL.Moments.ConjugateWindow

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentGaussEnergy CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentSecondSectorColumns CenteredMomentConjugateWindow CenteredMomentSecondHeightFamily
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentFirstColumns
open CenteredMomentChildAssembly CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentCommonSupport RayFourExpansion IdealMobiusDivisorSum FourierBridge
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]

lemma element_norm (Q C:Ideal O)(hC:C≠0)(S:Finset (Ideal O))(I:columns Q C hC S):
    ‖eisEmbedding (element Q C hC S I)‖^2=(Ideal.absNorm (I:Ideal O):ℝ):=by
  rw [eisEmbedding_norm_sq_eq_absNorm_span,element_span]

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
