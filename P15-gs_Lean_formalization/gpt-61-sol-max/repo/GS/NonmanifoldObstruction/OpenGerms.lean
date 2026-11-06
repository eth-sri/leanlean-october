
import GS.NonmanifoldCompletion.NeighbourhoodModel



/-!
# Restrict the compact neighbourhood model to OPEN pointed neighbourhoods

The old compact images contain neighbourhoods but are not themselves open.
This file carries out the restriction rather than silently identifying these
notions. All subtype topologies remain induced. It does not supply the
homological obstruction or assert the final NonManifoldGoal.

-/
open GS.NonmanifoldCompletion Filter
namespace GS.NonmanifoldObstruction

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

variable (S : Set X)

/-- A nested subtype flattened onto its actual image. No openness is needed. -/
def flattenImage  (A : Set S) : A ≃ₜ (Subtype.val '' A : Set X) where
  toFun a := ⟨a.val.val, ⟨a.val,a.property,rfl⟩⟩
  invFun x := ⟨⟨x.val, by aesop⟩, by grind⟩
  left_inv a := rfl
  right_inv x := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop


/-- A relatively open subset contained in the interior is ambient-open. -/
theorem isOpen_flatten_of_subset_interior  (A : Set S)
    (hA : IsOpen A) (hinside : ∀ a∈A, a.val ∈ interior S) :
    IsOpen (Subtype.val '' A : Set X) := by grind [image_mem_map,map_nhds_subtype_val,isOpen_iff_mem_nhds,mem_interior_iff_mem_nhds,nhdsWithin_eq_nhds]

structure PointedOpenModel (X Y : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] (x : X) (y : Y) where
  source : Set X
  target : Set Y
  source_open : IsOpen source
  target_open : IsOpen target
  source_point : x ∈ source
  target_point : y ∈ target
  chart : source ≃ₜ target
  map_point : ∀ hx : x∈source, (chart ⟨x,hx⟩).val = y

/-- Choose a relatively open part on which BOTH ambient interiors are reached. -/
def interiorBridge {x : X} {y : Y} (g : PointedNeighbourhoodModel X Y x y) := {a | a.val ∈ interior g.source ∧ (g.chart a).val ∈ interior g.target}



/-- No compactness or manifold hypothesis is required by this germ restriction. -/
def pointedOpenModel {x : X} {y : Y} (g : PointedNeighbourhoodModel X Y x y) :
    PointedOpenModel X Y x y := by
  let A := interiorBridge g
  let B := g.chart '' A
  let U := Subtype.val '' A
  let V := Subtype.val '' B
  have hA : IsOpen A := (isOpen_interior.preimage continuous_subtype_val).inter
    (isOpen_interior.preimage (continuous_subtype_val.comp g.chart.continuous))
  have hB := g.chart.isOpenMap A hA
  have hU := isOpen_flatten_of_subset_interior g.source A hA
    (fun a ha => ha.1)
  have hV := isOpen_flatten_of_subset_interior g.target B hB (by
    rintro b ⟨a,ha,rfl⟩
    exact ha.2)
  have hxS := mem_of_mem_nhds g.source_nhds
  have hxI := mem_interior_iff_mem_nhds.mpr g.source_nhds
  have hyI := mem_interior_iff_mem_nhds.mpr g.target_nhds
  have hpointA : (⟨x,hxS⟩ : g.source) ∈ A := by
    refine ⟨hxI,?_⟩
    rw [g.map_point hxS]
    exact hyI
  have hxU : x ∈ U := ⟨⟨x,hxS⟩,hpointA,rfl⟩
  have hyV : y ∈ V :=
    ⟨g.chart ⟨x,hxS⟩,⟨⟨x,hxS⟩,hpointA,rfl⟩,g.map_point hxS⟩
  let h := ((flattenImage g.source A).symm.trans
    (g.chart.image A)).trans (flattenImage g.target B)
  refine ⟨U,V,hU,hV,hxU,hyV,h,?_⟩
  intro hx
  
  exact g.map_point hxS



end GS.NonmanifoldObstruction
