module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightTranslation
public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.FlatFiniteSum

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 theorem finite_level_exists :
    Nonempty (KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) := by apply DedekindZetaZeroFree.FiniteWhittakerProjectors.FlatFiniteSum.level_exists <;> assumption

 theorem smooth_zero (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    Smooth F ζ hζ (0 : Functions F ζ hζ) := by
  refine ⟨continuous_const, ?_, U, ?_⟩
  · intro g
    exact contDiffOn_const
  · intro g u hu
    rfl

 theorem smooth_add (v w : Functions F ζ hζ)
    (hv : Smooth F ζ hζ v) (hw : Smooth F ζ hζ w) :
    Smooth F ζ hζ (v + w) := by apply DedekindZetaZeroFree.FiniteWhittakerProjectors.FlatFiniteSum.smooth_add <;> assumption

 theorem smooth_smul (c : ℂ) (v : Functions F ζ hζ)
    (hv : Smooth F ζ hζ v) : Smooth F ζ hζ (c • v) := by apply DedekindZetaZeroFree.FiniteWhittakerProjectors.FlatFiniteSum.smooth_smul <;> assumption

end DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy

end
