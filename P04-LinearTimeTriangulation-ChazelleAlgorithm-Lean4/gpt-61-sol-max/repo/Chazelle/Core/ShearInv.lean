module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SpecBase

/-!
# Shear invariance (WP-A)

The shear `shearPt ε : (x, y) ↦ (x, y + ε x)` is a linear homeomorphism of the plane with
inverse `shearPt (-ε)` and determinant `1`.  Every notion of the specification is transported by
it: segments, edges, the boundary, common endpoints, simplicity, bounded sets, connected
components of the complement of the boundary, the filled region, triangles, interiors, and hence
triangulations.  Main result: `shearInvariance : ShearInvarianceSpec`.
-/

namespace Chazelle.Core

public section

open Set

section
variable (ε : ℝ)
/-- The shear by `-ε` undoes the shear by `ε`. -/
theorem shearPt_neg_shearPt (p : Point) : shearPt (-ε) (shearPt ε p) = p := by
  simp_all [shearPt] 

/-- The shear by `ε` undoes the shear by `-ε`. -/
theorem shearPt_shearPt_neg (p : Point) : shearPt ε (shearPt (-ε) p) = p := by
  simpa using shearPt_neg_shearPt (-ε) p

/-- The shear is injective. -/
theorem shearPt_injective : Function.Injective (shearPt ε) :=
  Function.LeftInverse.injective (shearPt_neg_shearPt ε)

/-- The shear is surjective. -/
theorem shearPt_surjective : Function.Surjective (shearPt ε) :=
  Function.RightInverse.surjective (shearPt_shearPt_neg ε)

/-- The shear is bijective. -/
theorem shearPt_bijective : Function.Bijective (shearPt ε) :=
  ⟨shearPt_injective ε, shearPt_surjective ε⟩

/-- Shearing back a sheared polygon gives the original polygon. -/
theorem shear_shear (P : Polygon) : shear (-ε) (shear ε P) = P := by
  cases P with
  | mk l =>
    simp only [shear, List.map_map]
    congr 1
    conv_rhs => rw [← List.map_id l]
    exact List.map_congr_left (fun p _ => shearPt_neg_shearPt ε p)

/-- The shear is a linear map. -/
theorem isLinearMap_shearPt : IsLinearMap ℝ (shearPt ε) where
  map_add p q := by
    grind [shearPt, Prod.snd_add, Prod.fst_add]
  map_smul c p := by
    grind [shearPt, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]

/-- The shear is continuous. -/
theorem continuous_shearPt : Continuous (shearPt ε) := by
  unfold shearPt
  fun_prop


end

/-- The shear as a homeomorphism of the plane. -/
@[expose] noncomputable def shearHomeo (ε : ℝ) : Point ≃ₜ Point where
  toFun := shearPt ε
  invFun := shearPt (-ε)
  left_inv := shearPt_neg_shearPt ε
  right_inv := shearPt_shearPt_neg ε
  continuous_toFun := continuous_shearPt ε
  continuous_invFun := continuous_shearPt (-ε)

theorem coe_shearHomeo (ε : ℝ) : ⇑(shearHomeo ε) = shearPt ε := rfl

section
variable {ε : ℝ}
/-- Membership in a sheared set: `p ∈ shear '' S ↔ unshear p ∈ S`. -/
theorem mem_image_shearPt {S : Set Point} {p : Point} :
    p ∈ shearPt ε '' S ↔ shearPt (-ε) p ∈ S := by
  constructor
  · grind [shearPt_neg_shearPt]
  · intro h
    exact ⟨_, h, shearPt_shearPt_neg ε p⟩

/-- `p` is a sheared point iff unshearing `p` gives the point. -/
theorem eq_shearPt_iff {p v : Point} : p = shearPt ε v ↔ shearPt (-ε) p = v := by
  constructor
  · rintro rfl
    exact shearPt_neg_shearPt ε v
  · rintro rfl
    exact (shearPt_shearPt_neg ε p).symm

/-- Sheared images of sets are equal iff the sets are. -/
theorem image_shearPt_inj {A B : Set Point} :
    shearPt ε '' A = shearPt ε '' B ↔ A = B :=
  (Set.image_injective.2 (shearPt_injective ε)).eq_iff


end

/-- **The shear maps segments onto segments.** -/
theorem image_shearPt_segment (ε : ℝ) (a b : Point) :
    shearPt ε '' segment a b = segment (shearPt ε a) (shearPt ε b) := by
  ext p
  constructor
  · rintro ⟨q, ⟨t, ht0, ht1, rfl⟩, rfl⟩
    refine ⟨t, ht0, ht1, ?_⟩
    grind [shearPt]
  · rintro ⟨t, ht0, ht1, hp⟩
    refine ⟨(a.1 + t * (b.1 - a.1), a.2 + t * (b.2 - a.2)), ⟨t, ht0, ht1, rfl⟩, ?_⟩
    grind [shearPt]

section
variable (ε : ℝ) (P : Polygon)
/-- The edges of the sheared polygon are the sheared edges. -/
theorem shear_edge (i : ℕ) :
    (shear ε P).edge i = shearPt ε '' P.edge i := by
  grind [Polygon.edge, shear_vtx, shear_n, image_shearPt_segment]

/-- The boundary of the sheared polygon is the sheared boundary. -/
theorem shear_boundary :
    (shear ε P).boundary = shearPt ε '' P.boundary := by
  ext p
  grind [Polygon.boundary, mem_ofPred_eq, shear_edge, shear_n, mem_image_shearPt]

/-- The common endpoints of two sheared edges are the sheared common endpoints. -/
theorem shear_commonEndpoints (i j : ℕ) :
    (shear ε P).commonEndpoints i j = shearPt ε '' P.commonEndpoints i j := by
  ext p
  simp only [Polygon.commonEndpoints, mem_ofPred_eq, shear_vtx, shear_n, mem_image_shearPt,
    eq_shearPt_iff]


end

/-- **The shear preserves simplicity.** -/
theorem shear_simple {ε : ℝ} {P : Polygon} (h : P.Simple) : (shear ε P).Simple := by
  refine ⟨by rw [shear_n]; exact h.1, fun i j hi hj hv => ?_, fun i j hi hj hij => ?_⟩
  · rw [shear_n] at hi hj
    rw [shear_vtx, shear_vtx] at hv
    exact h.2.1 i j hi hj (shearPt_injective ε hv)
  · rw [shear_n] at hi hj
    rw [shear_edge, shear_edge, shear_commonEndpoints, ← image_inter (shearPt_injective ε),
      h.2.2 i j hi hj hij]

section
variable {ε : ℝ} {S : Set Point}
/-- The shear of a bounded set is bounded. -/
theorem isBoundedSet_image_shearPt (h : IsBoundedSet S) :
    IsBoundedSet (shearPt ε '' S) := by
  obtain ⟨R, hR⟩ := h
  refine ⟨R + |ε| * R, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨h1, h2⟩ := hR q hq
  have hR0 : 0 ≤ R := (abs_nonneg _).trans h1
  refine ⟨?_, ?_⟩
  · simp only [shearPt]
    nlinarith [abs_nonneg ε]
  · simp only [shearPt]
    calc |q.2 + ε * q.1| ≤ |q.2| + |ε * q.1| := abs_add_le _ _
      _ = |q.2| + |ε| * |q.1| := by rw [abs_mul]
      _ ≤ R + |ε| * R := by gcongr

/-- A set is bounded iff its shear is. -/
theorem isBoundedSet_image_shearPt_iff :
    IsBoundedSet (shearPt ε '' S) ↔ IsBoundedSet S := by
  refine ⟨fun h => ?_, isBoundedSet_image_shearPt⟩
  have h2 := isBoundedSet_image_shearPt (ε := -ε) h
  rwa [image_image, show (fun p => shearPt (-ε) (shearPt ε p)) = id from
    funext (shearPt_neg_shearPt ε), image_id] at h2


end

section
variable (ε : ℝ)
/-- The shear maps the connected component in `U` of `q` onto the connected component in the
sheared `U` of the sheared `q`. -/
theorem connectedComponentIn_image_shearPt (U : Set Point) (q : Point) :
    connectedComponentIn (shearPt ε '' U) (shearPt ε q) =
      shearPt ε '' connectedComponentIn U q := by
  by_cases hq : q ∈ U
  · have := (shearHomeo ε).image_connectedComponentIn hq
    rw [coe_shearHomeo] at this
    simp_all
  · rw [connectedComponentIn_eq_empty hq, image_empty, connectedComponentIn_eq_empty]
    rwa [(shearPt_injective ε).mem_set_image]

/-- **The filled region of the sheared polygon is the sheared filled region.** -/
theorem shear_filled (P : Polygon) :
    (shear ε P).filled = shearPt ε '' P.filled := by
  ext p
  obtain ⟨q, rfl⟩ := shearPt_surjective ε p
  have hc : (shear ε P).boundaryᶜ = shearPt ε '' P.boundaryᶜ := by
    rw [shear_boundary, image_compl_eq (shearPt_bijective ε)]
  grind [Polygon.filled, shear_boundary, image_union, mem_union, mem_ofPred_eq, connectedComponentIn_image_shearPt, isBoundedSet_image_shearPt_iff]

/-- The vertices of a triangle of the sheared polygon are the sheared vertices. -/
theorem shear_triVertices (P : Polygon) (t : Polygon.Triangle) :
    (shear ε P).triVertices t = shearPt ε '' P.triVertices t := by
  grind [Polygon.triVertices, shear_vtx, image_insert_eq, image_singleton]

/-- The convex hull commutes with the shear. -/
theorem convexHull_image_shearPt (S : Set Point) :
    convexHull ℝ (shearPt ε '' S) = shearPt ε '' convexHull ℝ S :=
  ((isLinearMap_shearPt ε).image_convexHull S).symm

/-- A triangle of the sheared polygon is the sheared triangle. -/
theorem shear_triSet (P : Polygon) (t : Polygon.Triangle) :
    (shear ε P).triSet t = shearPt ε '' P.triSet t := by
  grind [Polygon.triSet, shear_triVertices, convexHull_image_shearPt]

/-- The interior commutes with the shear. -/
theorem interior_image_shearPt (S : Set Point) :
    interior (shearPt ε '' S) = shearPt ε '' interior S := by
  have := (shearHomeo ε).image_interior S
  grind [coe_shearHomeo]

/-- Validity of a triangle is shear invariant. -/
theorem shear_validTriangle_iff (P : Polygon) (t : Polygon.Triangle) :
    (shear ε P).validTriangle t ↔ P.validTriangle t := by
  core_grind [shear_n, shear_vtx, det_shearPt]

section
variable (P : Polygon) (T : List Polygon.Triangle)
include P T
/-- The union of the triangles of the sheared polygon is the sheared union. -/
theorem shear_union_triSet :
    {p | ∃ t ∈ T, p ∈ (shear ε P).triSet t} = shearPt ε '' {p | ∃ t ∈ T, p ∈ P.triSet t} := by
  ext p
  simp only [mem_ofPred_eq, shear_triSet, mem_image_shearPt]

/-- **The shear preserves triangulations** (both ways). -/
theorem shear_triangulates_iff :
    (shear ε P).Triangulates T ↔ P.Triangulates T := by
  unfold Polygon.Triangulates
  rw [shear_union_triSet, shear_filled, image_shearPt_inj, shear_n]
  simp only [shear_validTriangle_iff, shear_triSet, interior_image_shearPt,
    disjoint_image_iff (shearPt_injective ε), shear_triVertices,
    ← image_inter (shearPt_injective ε), convexHull_image_shearPt, image_shearPt_inj]



end

end

/-- **WP-A: shear invariance.** -/
theorem shearInvariance : ShearInvarianceSpec := fun _ _ =>
  ⟨shear_simple, fun T => shear_triangulates_iff _ _ T⟩

end

end Chazelle.Core
