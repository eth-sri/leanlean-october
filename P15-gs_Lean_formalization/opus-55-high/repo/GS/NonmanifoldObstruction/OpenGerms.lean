module

public import GS.NonmanifoldCompletion.NeighbourhoodModel

@[expose] public section


/-!
# Restrict the compact neighbourhood model to OPEN pointed neighbourhoods

The old compact images contain neighbourhoods but are not themselves open.
This file carries out the restriction rather than silently identifying these
notions. All subtype topologies remain induced. It does not supply the
homological obstruction or assert the final NonManifoldGoal.

-/
noncomputable section
open GS GS.Nonmanifold GS.NonmanifoldCompletion Filter
namespace GS.NonmanifoldObstruction

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A nested subtype flattened onto its actual image. No openness is needed. -/
def flattenImage (S : Set X) (A : Set S) : A ≃ₜ (Subtype.val '' A : Set X) where
  toFun a := ⟨a.val.val, by simp⟩
  invFun x := ⟨⟨x.val, by grind⟩, by grind⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- A relatively open subset contained in the interior is ambient-open. -/
theorem isOpen_flatten_of_subset_interior (S : Set X) (A : Set S)
    (hA : IsOpen A) (hinside : ∀ a∈A, a.val ∈ interior S) :
    IsOpen (Subtype.val '' A : Set X) := by
  obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.mp hA
  convert isOpen_interior.inter hW using 1
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨hinside a ha, ha⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨x, interior_subset h1⟩, h2, rfl⟩

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

section
variable {x : X} {y : Y} (g : PointedNeighbourhoodModel X Y x y)
/-- Choose a relatively open part on which BOTH ambient interiors are reached. -/
def interiorBridge :
    Set g.source :=
  {a | a.val ∈ interior g.source ∧ (g.chart a).val ∈ interior g.target}

theorem interiorBridge_open : IsOpen (interiorBridge g) :=
  (isOpen_interior.preimage continuous_subtype_val).inter
    (isOpen_interior.preimage (continuous_subtype_val.comp g.chart.continuous))

/-- No compactness or manifold hypothesis is required by this germ restriction. -/
def pointedOpenModel :
    PointedOpenModel X Y x y := by
  let A : Set g.source := interiorBridge g
  have hxS : x ∈ g.source := mem_of_mem_nhds g.source_nhds
  have hA : (⟨x,hxS⟩ : g.source) ∈ A := ⟨mem_interior_iff_mem_nhds.mpr g.source_nhds, by
    rw [g.map_point hxS]; exact mem_interior_iff_mem_nhds.mpr g.target_nhds⟩
  exact ⟨_, _, isOpen_flatten_of_subset_interior g.source A (interiorBridge_open g) (fun a ha => ha.1),
    isOpen_flatten_of_subset_interior g.target (g.chart '' A) (g.chart.isOpenMap _ (interiorBridge_open g))
      (by rintro b ⟨a,ha,rfl⟩; exact ha.2),
    ⟨_, hA, rfl⟩, ⟨g.chart ⟨x,hxS⟩, ⟨_, hA, rfl⟩, g.map_point hxS⟩,
    ((flattenImage g.source A).symm.trans (g.chart.image A)).trans (flattenImage g.target _), fun _ => g.map_point hxS⟩

end

/-- The full-family model gives open local charts on each
side, still without presupposing either side to be a manifold. -/
theorem original_pointed_open_model {q : ℕ} (hq : 0<q)
    (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀) (hentries : ∀ i j, Q₀ i j≠0) :
    Nonempty (PointedOpenModel ↥(localFamily q) (ModelCoordinates q)
      (familyBase Q₀ hQ₀) (modelCoordinatesZero q)) := by
  obtain ⟨g⟩ := original_pointed_neighbourhood_model hq Q₀ hQ₀ hentries
  exact ⟨pointedOpenModel g⟩

end GS.NonmanifoldObstruction
