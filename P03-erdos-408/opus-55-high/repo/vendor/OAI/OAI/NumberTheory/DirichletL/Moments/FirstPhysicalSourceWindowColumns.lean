module

public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceCanonicalData
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceWindow
public import OAI.NumberTheory.DirichletL.Moments.ConjugateWindow

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance firstWindowColumnsDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma element_norm (Q C:Ideal ActualEisensteinCubic.O)(hC:C≠0)(S:Finset (Ideal ActualEisensteinCubic.O))(I:columns Q C hC S):
    ‖eisEmbedding (element Q C hC S I)‖^2=(Ideal.absNorm (I:Ideal ActualEisensteinCubic.O):ℝ):=by
  rw [eisEmbedding_norm_sq_eq_absNorm_span,element_span]

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
