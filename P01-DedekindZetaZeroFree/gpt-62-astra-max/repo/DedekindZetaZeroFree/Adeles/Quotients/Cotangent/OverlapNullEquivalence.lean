module

public import DedekindZetaZeroFree.Metaplectic.Cubic.OrbifoldCharts.OverlapMeasureNonsingularity

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology
namespace DedekindZetaZeroFree.KPContCotangentCorrectedNullEquivalence
open KPContActualCotangentCountableShrinking KPContCotangentActualOverlap
open KPContCotangentOverlapRationalBranches KPContCotangentOverlapNullEquivalence
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
    {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
    {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
    {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
    {a b : ShrunkChart F ζ hζ U R P H}
structure NullEquivalence2 (e : Branch a b) (he : e.Properties) : Prop where
  forward_quasiMeasurePreserving : Measure.QuasiMeasurePreserving (forward e)
    (Measure.comap (Subtype.val : e.domain → M F) ((liftedMeasure a).restrict e.domain))
    (Measure.comap (Subtype.val : e.targetDomain → M F) ((liftedMeasure b).restrict e.targetDomain))
  backward_quasiMeasurePreserving : Measure.QuasiMeasurePreserving (backward e he)
    (Measure.comap (Subtype.val : e.targetDomain → M F) ((liftedMeasure b).restrict e.targetDomain))
    (Measure.comap (Subtype.val : e.domain → M F) ((liftedMeasure a).restrict e.domain))
  image_null_iff : ∀ S : Set (M F), S ⊆ e.domain →
    (((liftedMeasure a).restrict e.domain) S = 0 ↔
      ((liftedMeasure b).restrict e.targetDomain) (e.psi '' S) = 0)
  preimage_null_iff : ∀ Z : Set (M F), Z ⊆ e.targetDomain →
    (((liftedMeasure b).restrict e.targetDomain) Z = 0 ↔
      ((liftedMeasure a).restrict e.domain) (e.psi ⁻¹' Z) = 0)
theorem actual_nullEquivalence2 (e : Branch a b) (he : e.Properties) : NullEquivalence2 e he := by
  obtain ⟨hf,hb,hi,hp⟩ := actual_nonsingularity e he
  exact ⟨hf,hb,hi,hp⟩
structure NonsingularEnumeration2 (a b : ShrunkChart F ζ hζ U R P H)
    extends Enumeration a b where
def withNonsingularity2 (e : Enumeration a b) : NonsingularEnumeration2 a b where
  toEnumeration := e
end DedekindZetaZeroFree.KPContCotangentCorrectedNullEquivalence

end
