module

public import GS.NonmanifoldCompletion.FullFibreCoverage
public import GS.Nonmanifold.OriginalCompactModel

@[expose] public section


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
noncomputable section
open Matrix Filter GS GS.Extensions GS.Continuation GS.Nonmanifold
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

def familyBase {q : ℕ} (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀) : ↥(localFamily q) :=
  ⟨basePoint Q₀,basePoint_mem_localFamily Q₀ hQ₀⟩

/-- The complete local model, with neither side's neighbourhood claim assumed.
It is still NOT the topological nonmanifold theorem. -/
theorem original_pointed_neighbourhood_model {q : ℕ} (hq : 0<q)
    (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀) (hentries : ∀ i j, Q₀ i j≠0) :
    Nonempty (PointedNeighbourhoodModel ↥(localFamily q) (ModelCoordinates q)
      (familyBase Q₀ hQ₀) (modelCoordinatesZero q)) := by
  obtain ⟨η,hη,h,hcomm,U,hU,hzero,hsub⟩ :=
    exists_original_compact_model_homeomorphism hq Q₀ hQ₀ hentries
  obtain ⟨W,hW,hbase,hcover⟩ := exists_open_original_local_coverage hq Q₀ hQ₀ hentries η hη
  refine ⟨{
    source := {M | M.val ∈ OriginalFImage Q₀ η}
    target := Set.range (@independentG q η)
    source_nhds := Filter.mem_of_superset ((hW.preimage continuous_subtype_val).mem_nhds hbase) fun M hM => by
      obtain ⟨p,hp,he⟩ := hcover M.val M.property hM
      tauto
    target_nhds := Filter.mem_of_superset (hU.mem_nhds hzero) hsub
    chart := ({ toFun M := ⟨M.val.val,M.property⟩
                invFun M := ⟨⟨M.val, M.2.elim fun p he => he ▸ originalF_mem_of_mem_K Q₀ hQ₀ p.2⟩, M.2⟩
                left_inv M := rfl
                right_inv M := rfl } : _ ≃ₜ OriginalFImage Q₀ η).trans h
    map_point := ?_ }⟩
  have := congrArg Subtype.val (hcomm ⟨originalBaseParameters q, originalBaseParameters_mem q hη.le⟩)
  simp only [originalF_basePoint] at this
  exact fun _ => this.trans (independentG_basepoint q η hη.le)

end GS.NonmanifoldCompletion
