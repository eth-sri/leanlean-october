module

public import GS.NonmanifoldObstruction.OpenGerms

@[expose] public section



/-!
# Exact transport of the original local Euclidean property

The auxiliary intrinsic definition is proved equivalent to EuclideanAtSubset,
not silently substituted for it. All transfer lemmas are elementary topology;
none assert invariance of dimension or a homological computation.
-/
noncomputable section
open GS GS.NonmanifoldObstruction
namespace GS.NonmanifoldFinal

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Local Euclidean charts stated directly on a topological space. -/
def EuclideanAt (x : X) : Prop :=
  ∃ (U : Set X), IsOpen U ∧ x ∈ U ∧
    ∃ (n : ℕ) (V : Set (EuclideanSpace ℝ (Fin n))), IsOpen V ∧
      Nonempty (U ≃ₜ V)

/-- Flatten an ambient-open restriction of a subtype. -/
def subtypeOpenIntersection (S U : Set X) :
    ↥(Subtype.val ⁻¹' U : Set S) ≃ₜ ↥(S ∩ U) where
  toFun a := ⟨a.val.val,a.val.property,a.property⟩
  invFun a := ⟨⟨a.val,a.property.1⟩,a.property.2⟩
  left_inv a := rfl
  right_inv a := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The old ambient-subset definition and intrinsic subtype charts agree. -/
theorem euclideanAtSubset_iff (S : Set X) (x : X) (hx : x ∈ S) :
    EuclideanAtSubset S x ↔ EuclideanAt (⟨x,hx⟩ : S) := by
  constructor
  · rintro ⟨_,U,hU,hxU,n,V,hV,⟨h⟩⟩
    exact ⟨Subtype.val ⁻¹' U, hU.preimage continuous_subtype_val, hxU,
      n,V,hV,⟨(subtypeOpenIntersection S U).trans h⟩⟩
  · rintro ⟨A,hA,hxA,n,V,hV,⟨h⟩⟩
    obtain ⟨U,hU,rfl⟩ := isOpen_induced_iff.mp hA
    exact ⟨hx,U,hU,hxA,n,V,hV,⟨(subtypeOpenIntersection S U).symm.trans h⟩⟩

section
variable (h : X ≃ₜ Y) (x : X)
/-- Transfer a chart along a global homeomorphism. -/
theorem euclideanAt_of_homeomorph (hx : EuclideanAt x) : EuclideanAt (h x) := by
  rcases hx with ⟨U,hU,ha,n,V,hV,⟨c⟩⟩
  exact ⟨h '' U,by simp_all,by grind,n,V,hV,
    ⟨(Homeomorph.image h U).symm.trans c⟩⟩

/-- Apply the preceding universe-polymorphic lemma in both directions. -/
theorem euclideanAt_homeomorph :
    EuclideanAt x ↔ EuclideanAt (h x) :=
  ⟨euclideanAt_of_homeomorph h x, fun hx => by simpa using euclideanAt_of_homeomorph h.symm _ hx⟩

end

/-- Passing to an open subspace neither creates nor destroys a chart at a point. -/
theorem euclideanAt_open_iff (S : Set X) (hS : IsOpen S) (x : S) :
    EuclideanAt x ↔ EuclideanAt x.val := by
  constructor
  · rintro ⟨A,hA,hx,n,V,hV,⟨c⟩⟩
    exact ⟨Subtype.val '' A,hS.isOpenMap_subtype_val A hA,
      by grind,n,V,hV,⟨(flattenImage S A).symm.trans c⟩⟩
  · rintro ⟨U,hU,hxU,n,V,hV,⟨c⟩⟩
    exact ⟨_, hU.preimage continuous_subtype_val, hxU, n, _, hV.isOpenMap_subtype_val _
      (c.isOpenMap _ (hS.preimage continuous_subtype_val)), ⟨((((subtypeOpenIntersection S U).trans
      (Homeomorph.setCongr (Set.inter_comm S U))).trans (subtypeOpenIntersection U S).symm).trans
      (Homeomorph.image c _)).trans (flattenImage V _)⟩⟩

section
variable {x : X} {y : Y}
/-- The pointed OPEN local model transports the exact chart property. -/
theorem euclideanAt_pointedOpenModel (g : PointedOpenModel X Y x y) : EuclideanAt x ↔ EuclideanAt y := by
  let a : g.source := ⟨x,g.source_point⟩
  calc
    EuclideanAt x ↔ EuclideanAt a :=
      (euclideanAt_open_iff g.source g.source_open a).symm
    _ ↔ EuclideanAt (g.chart a) := euclideanAt_homeomorph g.chart a
    _ ↔ EuclideanAt (g.chart a).val :=
      euclideanAt_open_iff g.target g.target_open (g.chart a)
    _ ↔ EuclideanAt y := by rw [g.map_point g.source_point]

end

end GS.NonmanifoldFinal
