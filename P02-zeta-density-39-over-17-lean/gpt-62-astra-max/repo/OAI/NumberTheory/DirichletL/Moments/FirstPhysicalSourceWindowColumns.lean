module
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceCanonicalData
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceWindow
public import OAI.NumberTheory.DirichletL.Moments.ConjugateWindow

@[expose] public section

namespace OAI

noncomputable section
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
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance firstWindowColumnsDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma element_norm (Q C:Ideal O)(hC:C≠0)(S:Finset (Ideal O))(I:columns Q C hC S):
    ‖eisEmbedding (element Q C hC S I)‖^2=(Ideal.absNorm (I:Ideal O):ℝ):=by
  rw [eisEmbedding_norm_sq_eq_absNorm_span,element_span]

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
