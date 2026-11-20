module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspFrames.CoherentLevelsAndNormInvariance
public import DedekindZetaZeroFree.Eisenstein.Induction.Cubic.SphericalFlatFamilies

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ResidualBoundaryRelevel
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
def meetLevel (U J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ :=
  ⟨U.toOpenSubgroup ⊓ J.toOpenSubgroup, U.isCompact.inter_right J.toOpenSubgroup.isClosed⟩
section

variable (U V : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (v : KPContActualSphericalFlatStage.Stage F ζ hζ U)

def restrictStage :
    KPContActualSphericalFlatStage.Stage F ζ hζ V :=
  ⟨v.val, by
    refine ⟨?_, v.property.2⟩
    intro g u
    exact v.property.1 g ⟨u.val, Subgroup.map_mono h u.property⟩⟩
@[simp] theorem restrictStage_val :
    (restrictStage F ζ hζ U V h v).val = v.val := rfl

end
theorem level_idempotent (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    KPShift81CoherentLevel.level F ζ hζ (KPShift81CoherentLevel.level F ζ hζ U) =
      KPShift81CoherentLevel.level F ζ hζ U := by
  unfold KPShift81CoherentLevel.level
  simp
end DedekindZetaZeroFree.FourierContinuation.ResidualBoundaryRelevel

end
