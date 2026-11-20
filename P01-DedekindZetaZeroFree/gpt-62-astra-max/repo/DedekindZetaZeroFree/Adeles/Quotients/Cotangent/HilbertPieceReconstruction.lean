module

public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.GluingExtractionIdentities

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal BigOperators
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCotangentPieceReconstruction

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualCotangentCountableShrinking KPContActualCotangentBorelRefinement
open KPContActualCotangentExactMeasurableGluing KPContActualCotangentMeasurableFamilies
open KPContActualCotangentPieceHilbertSum KPContActualCotangentPieceExtraction
open KPContActualCotangentGluedPieceIntegral KPContActualCotangentPieceAeTransport
open KPContCotangentActualOverlap KPContCotangentOverlapRationalBranches
open KPContCotangentActualGenuineTwistIsotropy

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
    {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
    {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
    {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
    (cover : CountableCover F ζ hζ U R P H)

def originalPoint (a : ShrunkChart F ζ hζ U R P H) (x : omega a) : a.domain :=
  ⟨labeledA (placeEquiv F ζ hζ) x.val, x.property⟩

def selectedFields (u : PieceHilbert cover) : SequenceFields cover := fun n x =>
  KPMeasurableLocalL2.representative (localData (cover.chart n))
    (supportedPiece cover n) (u n) (originalPoint (cover.chart n) x)

 section

variable (a : ShrunkChart F ζ hζ U R P H)

theorem originalPoint_coordinates
    (y : a.domain) : originalPoint a (coordinates a y) = y := by
  apply Subtype.ext
  funext k
  simp [originalPoint, coordinates, labeledA, labeledAInv]

 theorem coordinates_originalPoint
    (x : omega a) : coordinates a (originalPoint a x) = x := by
  apply Subtype.ext
  simp [originalPoint, coordinates, labeledA, labeledAInv]

end

private theorem selectedFields_zero_off (u : PieceHilbert cover) (n : ℕ)
    (y : omega (cover.chart n)) (hy : q (cover.chart n) y.val ∉ basePiece cover n) :
    selectedFields cover u n y = 0 := by
  refine ((KPMeasurableLocalL2.representative_spec (localData (cover.chart n))
    (supportedPiece cover n) (u n)).2.2.1) _ ?_
  intro hmem
  refine hy ?_
  have htb : (cover.chart n).toBase (originalPoint (cover.chart n) y) =
      q (cover.chart n) y.val := rfl
  have hmem' : (cover.chart n).toBase (originalPoint (cover.chart n) y) ∈ basePiece cover n := hmem
  rw [htb] at hmem'
  exact hmem'

private alias continuous_labeledA := DedekindZetaZeroFree.KPContActualCotangentExactMeasurableGluing.continuous_labeledA_placeEquiv

 theorem continuous_originalPoint (a : ShrunkChart F ζ hζ U R P H) :
    Continuous (originalPoint a) :=
  Continuous.subtype_mk (continuous_labeledA.comp continuous_subtype_val) fun x => x.property

private theorem selectedFields_measurable (u : PieceHilbert cover) (n : ℕ) :
    Measurable (selectedFields cover u n) :=
  ((KPMeasurableLocalL2.representative_spec (localData (cover.chart n))
    (supportedPiece cover n) (u n)).1).comp (continuous_originalPoint (cover.chart n)).measurable

section

variable (a : ShrunkChart F ζ hζ U R P H) (γ : Gamma a) (y : M F) (hy : y ∈ omega a)

private theorem labeledA_psi :
    labeledA (placeEquiv F ζ hζ) ((isotropyArrow a γ).psi y) =
      (actualActionEquiv a γ (originalPoint a ⟨y, hy⟩)).val := by
  let actualActionEquiv₀ := actualActionEquiv a γ (originalPoint a ⟨y, hy⟩)
  have h3 : labeledAInv (placeEquiv F ζ hζ)
      (actualActionEquiv₀).val = (isotropyArrow a γ).psi y := by
    have hc := coordinates_action a γ (originalPoint a ⟨y, hy⟩)
    rw [coordinates_originalPoint a ⟨y, hy⟩] at hc
    simpa [coordinates] using hc
  calc _
      = labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ)
          (actualActionEquiv₀).val) := by rw [h3]
    _ = (actualActionEquiv₀).val := by
        funext k; simp [labeledA, labeledAInv]

private theorem actualTensor_originalPoint :
    actualTensor a γ (originalPoint a ⟨y, hy⟩) =
      T (isotropyArrow a γ) y
        (KPContActualCotangentMeasurableFamilies.omega_subset_larger a hy) := by
  simp only [actualTensor, coordinates_originalPoint a ⟨y, hy⟩]

end

private alias ambientSequence_of_mem := DedekindZetaZeroFree.KPContActualCotangentGluingInverseIdentities.GluingExtractionIdentities.ambientSequence_apply

section

variable (u : PieceHilbert cover)

private theorem selectedFields_equivariant (n : ℕ)
    (γ : Gamma (cover.chart n)) (y : M F) (hy : y ∈ omega (cover.chart n)) :
    ambientSequence cover (selectedFields cover u) n
        ((isotropyArrow (cover.chart n) γ).psi y) =
      T (isotropyArrow (cover.chart n) γ) y
        (KPContActualCotangentMeasurableFamilies.omega_subset_larger (cover.chart n) hy)
        (ambientSequence cover (selectedFields cover u) n y) := by
  have hy' :=
    KPContActualCotangentMeasurableFamilies.isotropy_mem (cover.chart n) γ y hy
  rw [ambientSequence_of_mem cover _ n _ hy', ambientSequence_of_mem cover _ n _ hy]
  simp only [selectedFields]
  let originalPoint₀ := originalPoint (cover.chart n) ⟨y, hy⟩
  have hspec := (KPMeasurableLocalL2.representative_spec (localData (cover.chart n))
    (supportedPiece cover n) (u n)).2.2.2 γ (originalPoint₀)
  have harg : originalPoint (cover.chart n) ⟨(isotropyArrow (cover.chart n) γ).psi y, hy'⟩ =
      actualActionEquiv (cover.chart n) γ (originalPoint₀) := by
    apply Subtype.ext
    exact labeledA_psi (cover.chart n) γ y hy
  rw [harg]
  simp only [localData] at hspec ⊢
  rw [hspec]
  exact congrArg (fun e => e (KPMeasurableLocalL2.representative (localData (cover.chart n))
    (supportedPiece cover n) (u n) (originalPoint₀)))
    (actualTensor_originalPoint (cover.chart n) γ y hy)

theorem selectedFields_isPieceSequence :
    IsPieceSequence cover (selectedFields cover u) := by
  refine ⟨selectedFields_measurable cover u, fun n y hy => selectedFields_zero_off cover u n y hy, ?_⟩
  intro n γ y hy
  exact selectedFields_equivariant cover u n γ y hy

def selectedSequence : PieceSequence cover :=
  ⟨selectedFields cover u, selectedFields_isPieceSequence cover u⟩

theorem selectedSequence_represents :
    RepresentsComponents cover (selectedSequence cover u) u := by
  intro n
  filter_upwards [(KPMeasurableLocalL2.representative_spec (localData (cover.chart n))
    (supportedPiece cover n) (u n)).2.1] with y hy
  simp only [selectedSequence, selectedFields, pieceCoefficient]
  rw [originalPoint_coordinates]
  exact hy

def reconstructFamily : Family (U := U) (H := H) :=
  G cover (selectedSequence cover u)

theorem reconstructFamily_squareFinite :
    squareFinite (reconstructFamily cover u) :=
  (kp_cont_actual_cotangent_glued_piece_integral F ζ hζ R.adelicHaar R.adelic_isHaar U R rfl P H
    cover).gluing_squareFinite (selectedSequence cover u) u (selectedSequence_represents cover u)

def reconstruct : SquareFiniteFamily (U := U) (H := H) :=
  ⟨reconstructFamily cover u, reconstructFamily_squareFinite cover u⟩

end

private alias measurable_omega' := DedekindZetaZeroFree.KPContActualCotangentPieceAeTransport.AlmostEverywherePieceTransport.measurable_omega

 def coordinatesMeasurableEquiv (a : ShrunkChart F ζ hζ U R P H) :
    a.domain ≃ᵐ omega a where
  toFun := coordinates a
  invFun := originalPoint a
  left_inv := originalPoint_coordinates a
  right_inv := coordinates_originalPoint a
  measurable_toFun := (coordinates_continuous a).measurable
  measurable_invFun := (continuous_originalPoint a).measurable

private alias chartMeasure_eq_map_coordinates := DedekindZetaZeroFree.KPContActualCotangentGluingInverseIdentities.GluingExtractionIdentities.chartMeasure_eq_map

private alias q_coordinates' := DedekindZetaZeroFree.KPContActualCotangentGluingInverseIdentities.GluingExtractionIdentities.q_coordinates

alias HilbertPieceReconstruction.q_coordinates' := q_coordinates'

section

variable (cover : CountableCover F ζ hζ U R P H)

private theorem coordinates_preimage_coordinatePiece
    (n : ℕ) :
    coordinates (cover.chart n) ⁻¹' coordinatePiece cover n = liftedPiece cover n := by
  ext y
  rw [Set.mem_preimage, coordinatePiece, Set.mem_preimage, liftedPiece, Set.mem_preimage,
    q_coordinates']

 theorem ae_on_piece_of_ae_liftedMeasure
    (n : ℕ) (f g : omega (cover.chart n) → E F)
    (h : (fun y : (cover.chart n).domain => f (coordinates (cover.chart n) y))
      =ᵐ[(cover.chart n).liftedMeasure]
      (fun y : (cover.chart n).domain => g (coordinates (cover.chart n) y))) :
    f =ᵐ[(chartMeasure (cover.chart n)).restrict (coordinatePiece cover n)] g := by
  have hcoord : MeasurableEmbedding (coordinates (cover.chart n)) :=
    (coordinatesMeasurableEquiv (cover.chart n)).measurableEmbedding
  have hrestr : (chartMeasure (cover.chart n)).restrict (coordinatePiece cover n)
      = Measure.map (coordinates (cover.chart n))
          (((cover.chart n).liftedMeasure).restrict (liftedPiece cover n)) := by
    rw [chartMeasure_eq_map_coordinates, hcoord.restrict_map,
      coordinates_preimage_coordinatePiece]
  rw [hrestr]
  exact (hcoord.ae_map_iff).2 (ae_restrict_of_ae h)

 theorem selectedFields_ae
    (u : PieceHilbert cover) (n : ℕ) :
    (fun y : (cover.chart n).domain =>
        selectedFields cover u n (coordinates (cover.chart n) y))
      =ᵐ[(cover.chart n).liftedMeasure] ((u n).val : (cover.chart n).domain → E F) := by
  filter_upwards [((KPMeasurableLocalL2.representative_spec (localData (cover.chart n))
    (supportedPiece cover n) (u n)).2.1)] with y hy
  rw [selectedFields, originalPoint_coordinates]
  exact hy

end

def Rec : PieceHilbert cover →ₗ[ℂ] CotangentAeQuotient (U := U) (H := H) where
  toFun := fun u => toAeQuotient (reconstruct cover u)
  map_add' := by
    intro u v
    show toAeQuotient (reconstruct cover (u + v)) =
      toAeQuotient (reconstruct cover u) + toAeQuotient (reconstruct cover v)
    rw [← toAeQuotient_add, toAeQuotient_eq_iff]
    show AeEquivalent (G cover (selectedSequence cover (u + v)))
      (G cover (selectedSequence cover u) + G cover (selectedSequence cover v))
    rw [← (kp_cont_actual_cotangent_exact_measurable_gluing F ζ hζ R.adelicHaar
      R.adelic_isHaar U R rfl P H cover).add (selectedSequence cover u)
      (selectedSequence cover v)]
    refine (kp_cont_actual_cotangent_piece_ae_transport F ζ hζ R.adelicHaar
      R.adelic_isHaar U R rfl P H cover).intrinsic (selectedSequence cover (u + v))
      (selectedSequence cover u + selectedSequence cover v) ?_
    intro n
    refine ae_on_piece_of_ae_liftedMeasure cover n _ _ ?_
    have h2 : (fun y : (cover.chart n).domain => ((u + v) n).val y)
        =ᵐ[(cover.chart n).liftedMeasure]
        (fun y => (u n).val y + (v n).val y) := by
      rw [(congrFun (lp.coeFn_add u v) n)]
      exact Lp.coeFn_add _ _
    exact (selectedFields_ae cover (u + v) n).trans (h2.trans
      ((selectedFields_ae cover u n).symm.add (selectedFields_ae cover v n).symm))
  map_smul' := by
    intro c u
    show toAeQuotient (reconstruct cover (c • u)) = c • toAeQuotient (reconstruct cover u)
    rw [← toAeQuotient_smul, toAeQuotient_eq_iff]
    show AeEquivalent (G cover (selectedSequence cover (c • u)))
      (c • G cover (selectedSequence cover u))
    rw [← (kp_cont_actual_cotangent_exact_measurable_gluing F ζ hζ R.adelicHaar
      R.adelic_isHaar U R rfl P H cover).smul c (selectedSequence cover u)]
    refine (kp_cont_actual_cotangent_piece_ae_transport F ζ hζ R.adelicHaar
      R.adelic_isHaar U R rfl P H cover).intrinsic (selectedSequence cover (c • u))
      (c • selectedSequence cover u) ?_
    intro n
    refine ae_on_piece_of_ae_liftedMeasure cover n _ _ ?_
    have h2 : (fun y : (cover.chart n).domain => ((c • u) n).val y)
        =ᵐ[(cover.chart n).liftedMeasure]
        (fun y => c • (u n).val y) := by
      rw [(congrFun (lp.coeFn_smul c u) n)]
      exact Lp.coeFn_smul _ _
    exact (selectedFields_ae cover (c • u) n).trans (h2.trans
      ((selectedFields_ae cover u n).symm.const_smul c))

theorem extraction_reconstruction (u : PieceHilbert cover) :
    Ext cover (Rec cover u) = u := by
  rw [show Rec cover u = toAeQuotient (KPContActualCotangentGluingInverseIdentities.gluedFamily R.adelicHaar R.adelic_isHaar rfl cover u
      (selectedSequence cover u) (selectedSequence_represents cover u)) from
    congrArg toAeQuotient (Subtype.ext rfl)]
  exact (kp_cont_actual_cotangent_gluing_inverse_identities F ζ hζ R.adelicHaar
    R.adelic_isHaar U R rfl P H cover).extraction_gluing u (selectedSequence cover u)
    (selectedSequence_represents cover u)

theorem reconstruction_extraction (v : CotangentAeQuotient (U := U) (H := H)) :
    Rec cover (Ext cover v) = v := by
  obtain ⟨v₀, hv₀⟩ := toAeQuotient_surjective v
  let selectedSequence₀ := selectedSequence cover (Ext cover v)
  have hrep : RepresentsComponents cover (selectedSequence₀)
      (Ext cover (toAeQuotient v₀)) := by
    rw [hv₀]
    exact selectedSequence_represents cover (Ext cover v)
  rw [show Rec cover (Ext cover v) = toAeQuotient (KPContActualCotangentGluingInverseIdentities.gluedFamily R.adelicHaar R.adelic_isHaar rfl
      cover (Ext cover v) (selectedSequence₀)
      (selectedSequence_represents cover (Ext cover v))) from congrArg toAeQuotient (Subtype.ext rfl)]
  rw [show toAeQuotient (KPContActualCotangentGluingInverseIdentities.gluedFamily R.adelicHaar R.adelic_isHaar rfl
      cover (Ext cover v) (selectedSequence₀)
      (selectedSequence_represents cover (Ext cover v))) = toAeQuotient (KPContActualCotangentGluingInverseIdentities.gluedFamily R.adelicHaar
      R.adelic_isHaar rfl cover (Ext cover (toAeQuotient v₀))
      (selectedSequence₀) hrep) from congrArg toAeQuotient (Subtype.ext rfl)]
  rw [((kp_cont_actual_cotangent_gluing_inverse_identities F ζ hζ R.adelicHaar
    R.adelic_isHaar U R rfl P H cover).arbitrary_gluing_quotient v₀
    (selectedSequence₀) hrep), hv₀]

def equiv : PieceHilbert cover ≃ₗ[ℂ] CotangentAeQuotient (U := U) (H := H) where
  toFun := Rec cover
  invFun := Ext cover
  left_inv := extraction_reconstruction cover
  right_inv := reconstruction_extraction cover
  map_add' := (Rec cover).map_add
  map_smul' := (Rec cover).map_smul

end DedekindZetaZeroFree.KPContActualCotangentPieceReconstruction

namespace DedekindZetaZeroFree

open KPContActualCotangentCountableShrinking KPContActualCotangentBorelRefinement
open KPContActualCotangentExactMeasurableGluing KPContActualCotangentMeasurableFamilies
open KPContActualCotangentPieceHilbertSum KPContActualCotangentPieceExtraction
open KPContActualCotangentGluedPieceIntegral KPContActualCotangentPieceAeTransport
open KPContCotangentActualOverlap KPContCotangentOverlapRationalBranches
open KPContCotangentActualGenuineTwistIsotropy
open KPContActualCotangentGluingInverseIdentities
open KPContActualCotangentPieceReconstruction

end DedekindZetaZeroFree

end
