
import GS.NonmanifoldCompletion.FullFibreCoverage
import GS.Nonmanifold.OriginalCompactModel




/-!
# A pointed homeomorphism of neighbourhoods of the FULL GS family

The source contains a neighbourhood in localFamily itself. The target contains a neighbourhood in
the independent skew-coordinate cone model. Both neighbourhood claims are
proved using full-fibre coverage and estimates for the g map.

Neighbourhoods are not asserted to be open: the source and target may be the
compact images. A homeomorphism of these neighbourhoods is an equivalence of
the pointed local topological spaces. A final EuclideanAtSubset contradiction
still needs the topological cone obstruction and a restriction/transport lemma.

-/
open GS.Extensions GS.Continuation GS.Nonmanifold
open scoped Topology
namespace GS.NonmanifoldCompletion

/-- Explicit pointed homeomorphism between neighbourhood subsets. -/
structure PointedNeighbourhoodModel (X Y : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] (x : X) (y : Y) where
  source : Set X
  target : Set Y
  source_nhds : source ∈ 𝓝 x
  target_nhds : target ∈ 𝓝 y
  chart : ↥source ≃ₜ ↥target
  map_point : ∀ hx : x∈source, (chart ⟨x,hx⟩).val = y

variable (Q₀ : Mat q)

def familyBase  (hQ₀ : Orthogonal Q₀) : ↥(localFamily q) :=
  ⟨basePoint Q₀,basePoint_mem_localFamily Q₀ hQ₀⟩

def compactSourceInFamily  (η : ℝ) : Set ↥(localFamily q) :=
  {M | M.val ∈ OriginalFImage Q₀ η}

/-- The two presentations of the same F-image have the same induced topology. -/
def compactSourceHomeomorph  (hQ₀ : Orthogonal Q₀) (η : ℝ) :
    ↥(compactSourceInFamily Q₀ η) ≃ₜ OriginalFImage Q₀ η where
  toFun M := ⟨M.val.val,M.property⟩
  invFun M := ⟨⟨M.val,by grind [originalF_mem_of_mem_K]⟩,M.property⟩
  left_inv M := rfl
  right_inv M := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The selected F-image is now a neighbourhood in the FULL family subtype. -/
theorem compactSource_mem_nhds (hq : 0<q) (Q₀ : Mat q)
    (hQ₀ : Orthogonal Q₀) (hentries : ∀ i j, Q₀ i j≠0) (η : ℝ) (hη : 0<η) :
    compactSourceInFamily Q₀ η ∈ 𝓝 (familyBase Q₀ hQ₀) := by
  letI := isCompact_iff_compactSpace.mp (isCompact_smallFactorSet q)
  have hn := ((continuous_smallFactorMap q).comp continuous_subtype_val).isClosedMap.eventually_nhds_fiber
    (p := fun p : ↥(smallFactorSet q) => smallFactorMap p.val ∈ originalF Q₀ '' originalK q η)
    (basePoint Q₀) (by
      intro p hp
      obtain ⟨N,hN,hpN,hmap⟩ := factor_neighbourhood_in_original_image hq Q₀ hQ₀ hentries η hη
        p.val p.property hp
      exact Filter.mem_of_superset ((hN.preimage continuous_subtype_val).mem_nhds hpN)
        (fun p' hp' => hmap p'.val hp' p'.property))
  filter_upwards [(continuous_subtype_val.tendsto (familyBase Q₀ hQ₀)).eventually hn] with M hM
  have hi : M.val ∈ smallFactorMap '' smallFactorSet q := by simp_all [image_smallFactorMap]
  obtain ⟨p,hp,he⟩ := hi
  obtain ⟨p',hp',he'⟩ := hM ⟨p,hp⟩ he
  exact ⟨⟨p',hp'⟩,he'.trans he⟩

/-- The complete local model, with neither side's neighbourhood claim assumed.
It is still NOT the topological nonmanifold theorem. -/
theorem original_pointed_neighbourhood_model (hq : 0<q)
    (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀) (hentries : ∀ i j, Q₀ i j≠0) :
    Nonempty (PointedNeighbourhoodModel ↥(localFamily q) (ModelCoordinates q)
      (familyBase Q₀ hQ₀) (modelCoordinatesZero q)) := by
  obtain ⟨e,he,hzero⟩ := exists_matrixExpChart q
  have hi : Set.InjOn (originalPsi Q₀) e.source := by
    intro A hA B hB hab
    apply e.injOn hA hB
    rw [he]
    exact (_root_.Unitary.mul_right_inj ⟨Q₀,hQ₀⟩).mp hab
  obtain ⟨η,hη,hn⟩ := exists_uniform_normalized_original Q₀ hentries e.source e.open_source hzero
  letI := isCompact_iff_compactSpace.mp (isCompact_originalK q η)
  have hh : ∀ p p' : ↥(originalK q η),
      originalF Q₀ p.val = originalF Q₀ p'.val ↔ independentG p = independentG p' := by grind [original_same_fibres_normalized,independentG_eq_iff]
  obtain ⟨h,he⟩ := exists_homeomorph_ranges_of_same_fibres
    (fun p : ↥(originalK q η) => originalF Q₀ p.val) (@independentG q η)
    ((continuous_originalF Q₀).comp continuous_subtype_val)
    ((continuous_encodeModel q).comp
      (((continuous_originalG q).comp continuous_subtype_val).subtype_mk _)) hh
  have hpoint  := by
    simpa only [originalF_basePoint, originalFImageBase] using
      (congrArg Subtype.val (he ⟨originalBaseParameters q, originalBaseParameters_mem q hη.le⟩)).trans
        (independentG_basepoint q η hη.le)
  obtain ⟨U,hU,hzero,hsub⟩ := independentG_contains_neighbourhood q η hη
  refine ⟨{
    source := compactSourceInFamily Q₀ η
    target := Set.range (@independentG q η)
    source_nhds := compactSource_mem_nhds hq Q₀ hQ₀ hentries η hη
    target_nhds := Filter.mem_of_superset (hU.mem_nhds hzero) hsub
    chart := (compactSourceHomeomorph Q₀ hQ₀ η).trans h
    map_point := ?_ }⟩
  intro hx
  exact hpoint

end GS.NonmanifoldCompletion
