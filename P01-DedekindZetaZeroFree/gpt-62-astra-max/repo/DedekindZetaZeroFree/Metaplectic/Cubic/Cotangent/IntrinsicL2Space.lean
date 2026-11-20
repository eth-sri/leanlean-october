module

public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.ChartZeroExtension

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorCotangentL2

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualCotangentCountableShrinking
open KPContActualCotangentMeasurableFamilies
open KPContActualCotangentIntrinsicHilbertIntegral
open KPContActualCotangentChartRestriction
open KPContActualCotangentChartZeroExtension
open KPContCotangentActualGenuineTwistIsotropy KPContCotangentActualOverlap
open KPContCotangentOverlapRationalBranches

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

def chosenCover : CountableCover F ζ hζ U R P H :=
  Classical.choice (kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H).2

abbrev V := IntrinsicHilbert (chosenCover F ζ hζ U R P H)

abbrev muU := KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U

abbrev intrinsicClass : V F ζ hζ U R P H ≃ₗ[ℂ] CotangentAeQuotient (U := U) (H := H) :=
  KPContActualCotangentIntrinsicHilbertIntegral.intrinsicClass (chosenCover F ζ hζ U R P H)

def ofFamily : SquareFiniteFamily (U := U) (H := H) →ₗ[ℂ] V F ζ hζ U R P H :=
  (intrinsicClass F ζ hζ U R P H).symm.toLinearMap.comp toAeQuotient

theorem ofFamily_surjective : Function.Surjective (ofFamily F ζ hζ U R P H) := (intrinsicClass F ζ hζ U R P H).symm.surjective.comp toAeQuotient_surjective

theorem ofFamily_eq_iff (r s : SquareFiniteFamily (U := U) (H := H)) :
    ofFamily F ζ hζ U R P H r = ofFamily F ζ hζ U R P H s ↔
      AeEquivalent r.val s.val := by
  change (intrinsicClass F ζ hζ U R P H).symm (toAeQuotient r) =
    (intrinsicClass F ζ hζ U R P H).symm (toAeQuotient s) ↔ _
  rw [(intrinsicClass F ζ hζ U R P H).symm.injective.eq_iff]
  exact toAeQuotient_eq_iff r s

variable (a : ShrunkChart F ζ hζ U R P H)

def restriction :
    V F ζ hζ U R P H →L[ℂ] EuclideanQ a :=
  resEuclidean (chosenCover F ζ hζ U R P H) a

def zeroExtension :
    EuclideanQ a →ₗᵢ[ℂ] V F ζ hζ U R P H :=
  (ext (chosenCover F ζ hζ U R P H) a).comp (reindexQ a).symm.toLinearIsometry

end DedekindZetaZeroFree.KPContActualSectorCotangentL2

end
