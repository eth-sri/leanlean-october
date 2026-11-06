module

public import DedekindZetaZeroFree.Eisenstein.Induction.FiniteLocalSectionContinuity

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology Matrix.Norms.Elementwise
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.EisensteinReferenceSections.SourceContinuity
open KPAdelicCoverRestrictedProduct KPGlobalTorusFiniteStages
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)

 theorem principal_continuous (s : ℝ) (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s) :
    Continuous (fun g : KPCplxCharacterHaar.ComplexGL2 => f g) := by
  have hf := ((KPCplxPrincipalSeriesCharts.principalSeries_mem_iff s f).mp f.property).2.continuousOn
  have hm : Continuous (fun g : KPCplxCharacterHaar.ComplexGL2 =>
      (g : Matrix (Fin 2) (Fin 2) ℂ)) := Units.continuous_val
  have hd : ∀ g : KPCplxCharacterHaar.ComplexGL2, (g : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
    intro g
    exact Matrix.GeneralLinearGroup.det_ne_zero g
  have hc := hf.comp_continuous hm hd
  convert hc using 1
  funext g
  dsimp only [Function.comp_def, KPCplxPrincipalSeriesCharts.matrixFunction]
  rw [dif_pos (hd g)]
  exact congrArg (fun g : KPCplxCharacterHaar.ComplexGL2 => f g) (Units.ext rfl)
















































end DedekindZetaZeroFree.EisensteinReferenceSections.SourceContinuity

end
