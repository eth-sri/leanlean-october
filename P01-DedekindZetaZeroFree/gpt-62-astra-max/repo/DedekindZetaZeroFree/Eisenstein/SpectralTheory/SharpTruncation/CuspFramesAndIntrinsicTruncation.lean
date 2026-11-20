module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspFrames.Definitions

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.KPMsGreenFlux.ActualFrames
open KPMsGreenFlux
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

private theorem archProjection_compare (g : Cover F ζ hζ) (w : NumberField.InfinitePlace F) :
    PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g w =
      Matrix.ProjGenLinGroup.map
        (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom
        (KPCuspGenuineMonodromy.archProjection F ζ hζ g w) := by apply @DedekindZetaZeroFree.KPMsFixedHaar.archProjection_compare <;> assumption

private alias projective_equiv_injective := DedekindZetaZeroFree.KPMsFixedHaar.SphericalProjection.projective_equiv_injective

private theorem complex_kernel_mem {g : Cover F ζ hζ}
    (hg : PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g = 1) :
    g ∈ KPFiniteCuspAtlas.FiniteCover F ζ hζ := by apply @DedekindZetaZeroFree.KPMsFixedHaar.SphericalProjection.complex_kernel_mem <;> assumption

 theorem finiteSubgroup_eq :
    PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ = KPFiniteCuspAtlas.FiniteCover F ζ hζ := by apply @DedekindZetaZeroFree.KPActualComponentHaarSources.PartialRationalTiling.actual_finiteSubgroup_eq <;> assumption

end DedekindZetaZeroFree.KPMsGreenFlux.ActualFrames

end
