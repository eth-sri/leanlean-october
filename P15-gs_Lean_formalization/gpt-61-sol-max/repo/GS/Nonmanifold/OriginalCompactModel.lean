
import GS.Nonmanifold.OriginalModelCoordinates
import GS.Continuation.PointedCompactImage
open GS.MatrixBase




/-!
# Linking the new independent-coordinate model to the unchanged original f/g

This integrates the model-side results with the inherited exponential-chart
and same-fibres theorems. The resulting homeomorphism is still for the selected
compact f-image. It is NOT promoted to a neighbourhood of the full GS family:
OriginalLocalCoverageGoal and parametrization membership must be proved first.
-/
open GS.Extensions GS.GlobalGeometry
namespace GS.Nonmanifold

/-- The original g, with its already proved membership in the unbounded model. -/
def originalGAsModel {η : ℝ} (p : ↥(originalK q η)) : OriginalModel q :=
  ⟨originalG p.val, originalG_image_subset_model q η ⟨p.val,p.property,rfl⟩⟩

def independentG {η : ℝ} (p : ↥(originalK q η)) : ModelCoordinates q :=
  encodeModel (originalGAsModel p)

theorem independentG_eq_iff {η : ℝ} (p p' : ↥(originalK q η)) :
    independentG p = independentG p' ↔ originalG p.val = originalG p'.val := by
  change encodeModel (originalGAsModel p) = encodeModel (originalGAsModel p') ↔ _
  rw [(Function.LeftInverse.injective (@decode_encodeModel q)).eq_iff]
  exact Subtype.ext_iff

/-- Zero in the independent coordinates, including the rank-cone subtype. -/
def modelCoordinatesZero (q : ℕ) : ModelCoordinates q :=
  (0,0,0,⟨0,by simp⟩)

theorem decode_modelCoordinatesZero (q : ℕ) :
    (decodeModel (modelCoordinatesZero q)).val = (0,0,0,0) := by
  ext <;> simp_all [modelCoordinatesZero, decodeModel, unpackRight, unpackRows, unpackSkew]

/-- The original distinguished parameter maps to the zero coordinate tuple. -/
theorem independentG_basepoint (q : ℕ) (η : ℝ) (hη : 0 ≤ η) :
    independentG (⟨originalBaseParameters q, originalBaseParameters_mem q hη⟩ :
      ↥(originalK q η)) = modelCoordinatesZero q := by
  let p : ↥(originalK q η) := ⟨originalBaseParameters q, originalBaseParameters_mem q hη⟩
  have he : originalGAsModel p = decodeModel (modelCoordinatesZero q) := by
    apply Subtype.ext
    exact (originalG_basePoint q).trans (decode_modelCoordinatesZero q).symm
  change encodeModel (originalGAsModel p) = modelCoordinatesZero q
  rw [he,encode_decodeModel]

/-- The model-coordinate image contains an open neighbourhood of its zero point. -/
theorem independentG_contains_neighbourhood (q : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ U : Set (ModelCoordinates q), IsOpen U ∧ modelCoordinatesZero q ∈ U ∧
      U ⊆ Set.range (@independentG q η) := by
  let U : Set (ModelCoordinates q) :=
    {x | modelRadiusSq (decodeModel x).val < η^2}
  have hc :=
    (continuous_modelRadiusSq q).comp
      (continuous_subtype_val.comp (continuous_decodeModel q))
  refine ⟨U,isOpen_lt hc continuous_const,?_,?_⟩
  · change modelRadiusSq (decodeModel (modelCoordinatesZero q)).val < η^2
    rw [decode_modelCoordinatesZero]
    have hz : modelRadiusSq ((0,0,0,0) : OriginalImageCoordinates q) = 0 := by
      simp [modelRadiusSq,cFrobSq]
    rw [hz]
    exact sq_pos_of_pos hη
  · intro x hx
    obtain ⟨p,hp,he⟩ := small_modelRadius_mem_originalG hη
      (decodeModel x).val (decodeModel x).property hx
    refine ⟨⟨p,hp⟩,?_⟩
    have hh : originalGAsModel (⟨p,hp⟩ : ↥(originalK q η)) = decodeModel x :=
      Subtype.ext he
    change encodeModel (originalGAsModel ⟨p,hp⟩) = x
    rw [hh,encode_decodeModel]


end GS.Nonmanifold
