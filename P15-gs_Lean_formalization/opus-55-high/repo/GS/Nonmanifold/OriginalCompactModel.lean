module

public import GS.Nonmanifold.OriginalModelCoordinates
public import GS.Continuation.PointedCompactImage

@[expose] public section


/-!
# Linking the new independent-coordinate model to the unchanged original f/g

This integrates the model-side results with the inherited exponential-chart
and same-fibres theorems. The resulting homeomorphism is still for the selected
compact f-image. It is NOT promoted to a neighbourhood of the full GS family:
OriginalLocalCoverageGoal and parametrization membership must be proved first.
-/
noncomputable section
open Matrix GS GS.Extensions GS.Continuation GS.GlobalGeometry
namespace GS.Nonmanifold

section
variable {q : ℕ} {η : ℝ} (p : ↥(originalK q η))
/-- The original g, with its already proved membership in the unbounded model. -/
def originalGAsModel : OriginalModel q :=
  ⟨originalG p.val, originalG_image_subset_model q η (by grind)⟩

def independentG : ModelCoordinates q :=
  encodeModel (originalGAsModel p)

end

section
variable (q : ℕ)
/-- Zero in the independent coordinates, including the rank-cone subtype. -/
def modelCoordinatesZero : ModelCoordinates q :=
  (0,0,0,⟨0,by simp⟩)

theorem decode_modelCoordinatesZero :
    (decodeModel (modelCoordinatesZero q)).val = (0,0,0,0) := by
  simp [decodeModel,modelCoordinatesZero,unpackRight,unpackSkew,unpackRows,Prod.ext_iff,funext_iff,← Matrix.ext_iff]

/-- The original distinguished parameter maps to the zero coordinate tuple. -/
theorem independentG_basepoint (η : ℝ) (hη : 0 ≤ η) :
    independentG (⟨originalBaseParameters q, originalBaseParameters_mem q hη⟩ :
      ↥(originalK q η)) = modelCoordinatesZero q := by
  rw [independentG, ← encode_decodeModel (modelCoordinatesZero q)]
  exact congrArg encodeModel (Subtype.ext ((originalG_basePoint q).trans (decode_modelCoordinatesZero q).symm))

end

/-- A constructed compact-image homeomorphism to independent skew coordinates.
There is no supplied same-fibres or chart-injectivity assumption. -/
theorem exists_original_compact_model_homeomorphism {q : ℕ} (hq : 0 < q)
    (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀) (hentries : ∀ i j, Q₀ i j ≠ 0) :
    ∃ (η : ℝ) (hη : 0 < η),
      ∃ h : OriginalFImage Q₀ η ≃ₜ Set.range (@independentG q η),
        (∀ p : ↥(originalK q η),
          h ⟨originalF Q₀ p.val,⟨p,rfl⟩⟩ = ⟨independentG p,⟨p,rfl⟩⟩) ∧
        ∃ U : Set (ModelCoordinates q), IsOpen U ∧ modelCoordinatesZero q ∈ U ∧
          U ⊆ Set.range (@independentG q η) := by
  obtain ⟨η,hη,hfib⟩ := original_same_fibres hq Q₀ hQ₀ hentries
  letI : CompactSpace ↥(originalK q η) := isCompact_iff_compactSpace.mp (isCompact_originalK q η)
  obtain ⟨h,he⟩ := exists_homeomorph_ranges_of_same_fibres
    (fun p : ↥(originalK q η) => originalF Q₀ p.val) (@independentG q η)
    ((continuous_originalF Q₀).comp continuous_subtype_val)
    ((continuous_encodeModel q).comp (((continuous_originalG q).comp continuous_subtype_val).subtype_mk _))
    fun p p' => by simp [hfib _ p.2 _ p'.2, independentG, (Function.LeftInverse.injective decode_encodeModel).eq_iff, Subtype.ext_iff, originalGAsModel]
  refine ⟨η,hη,h,he,{x | modelRadiusSq (decodeModel x).val < η^2}, isOpen_lt ((continuous_modelRadiusSq q).comp
      (continuous_subtype_val.comp (continuous_decodeModel q))) continuous_const, ?_, fun x hx => ?_⟩
  · simp [decode_modelCoordinatesZero, modelRadiusSq, frobSq, frobInner, hη]
  obtain ⟨p,hp,he⟩ := small_modelRadius_mem_originalG hη _ (by simp) hx
  exact ⟨⟨p,hp⟩, (congrArg encodeModel (Subtype.ext he : originalGAsModel ⟨p,hp⟩ = _)).trans (encode_decodeModel x)⟩

end GS.Nonmanifold
