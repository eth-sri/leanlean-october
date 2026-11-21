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
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

def chosenCover : CountableCover F ζ hζ U R P H :=
  Classical.choice (kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H).2

abbrev V := IntrinsicHilbert (chosenCover F ζ hζ U R P H)

abbrev muU := KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U

abbrev intrinsicClass : V F ζ hζ U R P H ≃ₗ[ℂ] CotangentAeQuotient (U := U) (H := H) :=
  KPContActualCotangentIntrinsicHilbertIntegral.intrinsicClass (chosenCover F ζ hζ U R P H)

def ofFamily : SquareFiniteFamily (U := U) (H := H) →ₗ[ℂ] V F ζ hζ U R P H :=
  (intrinsicClass F ζ hζ U R P H).symm.toLinearMap.comp toAeQuotient

theorem ofFamily_surjective : Function.Surjective (ofFamily F ζ hζ U R P H) := by
  exact (intrinsicClass F ζ hζ U R P H).symm.surjective.comp toAeQuotient_surjective

theorem ofFamily_eq_iff (r s : SquareFiniteFamily (U := U) (H := H)) :
    ofFamily F ζ hζ U R P H r = ofFamily F ζ hζ U R P H s ↔
      AeEquivalent r.val s.val := by
  change (intrinsicClass F ζ hζ U R P H).symm (toAeQuotient r) =
    (intrinsicClass F ζ hζ U R P H).symm (toAeQuotient s) ↔ _
  rw [(intrinsicClass F ζ hζ U R P H).symm.injective.eq_iff]
  exact toAeQuotient_eq_iff r s

def restriction (a : ShrunkChart F ζ hζ U R P H) :
    V F ζ hζ U R P H →L[ℂ] EuclideanQ a :=
  resEuclidean (chosenCover F ζ hζ U R P H) a

def zeroExtension (a : ShrunkChart F ζ hζ U R P H) :
    EuclideanQ a →ₗᵢ[ℂ] V F ζ hζ U R P H :=
  (ext (chosenCover F ζ hζ U R P H) a).comp (reindexQ a).symm.toLinearIsometry

structure Properties : Prop where
  inner_integral : ∀ (v w : V F ζ hζ U R P H)
      (r s : SquareFiniteFamily (U := U) (H := H)),
    ofFamily F ζ hζ U R P H r = v → ofFamily F ζ hζ U R P H s = w →
      inner ℂ v w = ∫ x, pair r.val s.val x ∂muU F ζ hζ U R P
  norm_integral : ∀ (v : V F ζ hζ U R P H)
      (r : SquareFiniteFamily (U := U) (H := H)),
    ofFamily F ζ hζ U R P H r = v →
      ‖v‖ ^ 2 = ∫ x, (normSquare r.val x : ℝ) ∂muU F ζ hζ U R P
  restriction_represented : ∀ (a : ShrunkChart F ζ hζ U R P H)
      (v : V F ζ hζ U R P H) (r : SquareFiniteFamily (U := U) (H := H)),
    ofFamily F ζ hζ U R P H r = v →
      (fun y => (restriction F ζ hζ U R P H a v :
        Lp (EuclideanSpace ℂ (Fin (3 * d F))) 2 a.liftedMeasure) y) =ᵐ[a.liftedMeasure]
          (fun y => coefficientReindex (F := F) (localCoefficient a r.val y))

end DedekindZetaZeroFree.KPContActualSectorCotangentL2

namespace DedekindZetaZeroFree

theorem kp_cont_actual_sector_cotangent_l2
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H) :
    KPContActualSectorCotangentL2.Properties F ζ hζ U R P H := by
  let cover := KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H
  have hI := kp_cont_actual_cotangent_intrinsic_hilbert_integral
    F ζ hζ μG hμG U R hR P H cover
  exact ⟨fun v w r s hr hs => hI.inner_integral v w r s hr hs,
    fun v r hr => hI.norm_integral v r hr,
    KPContActualCotangentChartRestriction.resEuclidean_represented cover⟩

end DedekindZetaZeroFree

end
