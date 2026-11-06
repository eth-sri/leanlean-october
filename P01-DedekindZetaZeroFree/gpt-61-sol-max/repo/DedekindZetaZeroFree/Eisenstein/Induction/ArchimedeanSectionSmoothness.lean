module

public import DedekindZetaZeroFree.Eisenstein.Induction.SectionContinuity
public import DedekindZetaZeroFree.Eisenstein.Induction.RationalCovariance
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.TranslatedBigCellCoordinates

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology Matrix.Norms.Elementwise
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
namespace DedekindZetaZeroFree.EisensteinReferenceSections.SourceSmooth
open KPAdelicCoverRestrictedProduct KPGlobalTorusFiniteStages KPLiteralChamber
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)
open _root_.DedekindZetaZeroFree.KPLiteralChamber renaming sectionTuple_right → sectionTuple_right

 theorem complexMatrix_section (w : InfinitePlace F) (M : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    LocalCovariance.complexMatrix F ζ hζ w (sectionTuple F ζ hζ (fun _ => M) (Sum.inl w)) = M := by
  unfold LocalCovariance.complexMatrix sectionTuple
  change Matrix.GeneralLinearGroup.map _ (Matrix.GeneralLinearGroup.map _ M) = M
  apply Units.ext
  ext i j
  simp [Matrix.GeneralLinearGroup.map]















































































end DedekindZetaZeroFree.EisensteinReferenceSections.SourceSmooth

end
