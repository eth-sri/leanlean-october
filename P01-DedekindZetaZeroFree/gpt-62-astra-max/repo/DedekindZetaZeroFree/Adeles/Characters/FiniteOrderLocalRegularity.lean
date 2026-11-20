module

public import DedekindZetaZeroFree.Adeles.Characters.RayCharacterCorrectionFactors

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.SArithmeticData.CorrectionTopology
noncomputable section
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y]

variable {F : Type} [Field F] [NumberField F]

lemma infinite_embedding_continuous (w : InfinitePlace F) :
    Continuous (NumberField.IdeleClassGroup.ofCompletion (𝓞 F) F w) := by
  apply continuous_quot_mk.comp
  apply Continuous.units_map
  apply Continuous.prodMk _ continuous_const
  change Continuous (fun z : w.Completion => Pi.mulSingle w z)
  fun_prop

alias finite_embedding_continuous := DedekindZetaZeroFree.SArithmeticData.GaussCorrection.LocalArithmeticLaws.continuous_ideleClassGroup_ofAdicCompletion

end
end DedekindZetaZeroFree.SArithmeticData.CorrectionTopology
