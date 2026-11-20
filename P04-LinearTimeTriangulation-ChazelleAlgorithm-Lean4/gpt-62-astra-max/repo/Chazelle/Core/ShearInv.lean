module

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

/-- The shear by `-ε` undoes the shear by `ε`. -/
theorem shearPt_neg_shearPt (ε : ℝ) (p : Point) : shearPt (-ε) (shearPt ε p) = p := by
  refine Prod.ext rfl ?_
  simp only [shearPt]
  ring

/-- The shear by `ε` undoes the shear by `-ε`. -/
theorem shearPt_shearPt_neg (ε : ℝ) (p : Point) : shearPt ε (shearPt (-ε) p) = p := by
  simpa using shearPt_neg_shearPt (-ε) p

/-- The shear is injective. -/
theorem shearPt_injective (ε : ℝ) : Function.Injective (shearPt ε) :=
  Function.LeftInverse.injective (shearPt_neg_shearPt ε)

/-- The shear is surjective. -/
theorem shearPt_surjective (ε : ℝ) : Function.Surjective (shearPt ε) :=
  Function.RightInverse.surjective (shearPt_shearPt_neg ε)

/-- The shear is bijective. -/
theorem shearPt_bijective (ε : ℝ) : Function.Bijective (shearPt ε) :=
  ⟨shearPt_injective ε, shearPt_surjective ε⟩

/-- Shearing back a sheared polygon gives the original polygon. -/
theorem shear_shear (ε : ℝ) (P : Polygon) : shear (-ε) (shear ε P) = P := by
  cases P with
  | mk l =>
    simp only [shear, List.map_map]
    congr 1
    conv_rhs => rw [← List.map_id l]
    exact List.map_congr_left (fun p _ => shearPt_neg_shearPt ε p)

/-- The shear is a linear map. -/
theorem isLinearMap_shearPt (ε : ℝ) : IsLinearMap ℝ (shearPt ε) where
  map_add p q := by
    refine Prod.ext rfl ?_
    simp only [shearPt, Prod.snd_add, Prod.fst_add]
    ring
  map_smul c p := by
    refine Prod.ext rfl ?_
    simp only [shearPt, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring

/-- The shear is continuous. -/
theorem continuous_shearPt (ε : ℝ) : Continuous (shearPt ε) := by
  unfold shearPt
  fun_prop

/-- The shear as a homeomorphism of the plane. -/
@[expose] noncomputable def shearHomeo (ε : ℝ) : Point ≃ₜ Point where
  toFun := shearPt ε
  invFun := shearPt (-ε)
  left_inv := shearPt_neg_shearPt ε
  right_inv := shearPt_shearPt_neg ε
  continuous_toFun := continuous_shearPt ε
  continuous_invFun := continuous_shearPt (-ε)

theorem coe_shearHomeo (ε : ℝ) : ⇑(shearHomeo ε) = shearPt ε := rfl

/-- Membership in a sheared set: `p ∈ shear '' S ↔ unshear p ∈ S`. -/
theorem mem_image_shearPt {ε : ℝ} {S : Set Point} {p : Point} :
    p ∈ shearPt ε '' S ↔ shearPt (-ε) p ∈ S := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    rwa [shearPt_neg_shearPt]
  · intro h
    exact ⟨_, h, shearPt_shearPt_neg ε p⟩

/-- `p` is a sheared point iff unshearing `p` gives the point. -/
theorem eq_shearPt_iff {ε : ℝ} {p v : Point} : p = shearPt ε v ↔ shearPt (-ε) p = v := by
  constructor
  · rintro rfl
    exact shearPt_neg_shearPt ε v
  · rintro rfl
    exact (shearPt_shearPt_neg ε p).symm

/-- Sheared images of sets are equal iff the sets are. -/
theorem image_shearPt_inj {ε : ℝ} {A B : Set Point} :
    shearPt ε '' A = shearPt ε '' B ↔ A = B :=
  (Set.image_injective.2 (shearPt_injective ε)).eq_iff

/-- **The shear maps segments onto segments.** -/
theorem image_shearPt_segment (ε : ℝ) (a b : Point) :
    shearPt ε '' segment a b = segment (shearPt ε a) (shearPt ε b) := by
  ext p
  constructor
  · rintro ⟨q, ⟨t, ht0, ht1, rfl⟩, rfl⟩
    refine ⟨t, ht0, ht1, ?_⟩
    refine Prod.ext ?_ ?_ <;> simp only [shearPt]
    ring
  · rintro ⟨t, ht0, ht1, hp⟩
    refine ⟨(a.1 + t * (b.1 - a.1), a.2 + t * (b.2 - a.2)), ⟨t, ht0, ht1, rfl⟩, ?_⟩
    rw [hp]
    refine Prod.ext ?_ ?_ <;> simp only [shearPt]
    ring

/-- The edges of the sheared polygon are the sheared edges. -/
theorem shear_edge (ε : ℝ) (P : Polygon) (i : ℕ) :
    (shear ε P).edge i = shearPt ε '' P.edge i := by
  simp only [Polygon.edge, shear_vtx, shear_n, image_shearPt_segment]

/-- The boundary of the sheared polygon is the sheared boundary. -/
theorem shear_boundary (ε : ℝ) (P : Polygon) :
    (shear ε P).boundary = shearPt ε '' P.boundary := by
  ext p
  simp only [Polygon.boundary, mem_ofPred_eq, shear_edge, shear_n, mem_image_shearPt]

/-- The common endpoints of two sheared edges are the sheared common endpoints. -/
theorem shear_commonEndpoints (ε : ℝ) (P : Polygon) (i j : ℕ) :
    (shear ε P).commonEndpoints i j = shearPt ε '' P.commonEndpoints i j := by
  ext p
  simp only [Polygon.commonEndpoints, mem_ofPred_eq, shear_vtx, shear_n, mem_image_shearPt,
    eq_shearPt_iff]

/-- **The shear preserves simplicity.** -/
theorem shear_simple {ε : ℝ} {P : Polygon} (h : P.Simple) : (shear ε P).Simple := by
  refine ⟨by rw [shear_n]; exact h.1, fun i j hi hj hv => ?_, fun i j hi hj hij => ?_⟩
  · rw [shear_n] at hi hj
    rw [shear_vtx, shear_vtx] at hv
    exact h.2.1 i j hi hj (shearPt_injective ε hv)
  · rw [shear_n] at hi hj
    rw [shear_edge, shear_edge, shear_commonEndpoints, ← image_inter (shearPt_injective ε),
      h.2.2 i j hi hj hij]

/-- The shear of a bounded set is bounded. -/
theorem isBoundedSet_image_shearPt {ε : ℝ} {S : Set Point} (h : IsBoundedSet S) :
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
theorem isBoundedSet_image_shearPt_iff {ε : ℝ} {S : Set Point} :
    IsBoundedSet (shearPt ε '' S) ↔ IsBoundedSet S := by
  refine ⟨fun h => ?_, isBoundedSet_image_shearPt⟩
  have h2 := isBoundedSet_image_shearPt (ε := -ε) h
  rwa [image_image, show (fun p => shearPt (-ε) (shearPt ε p)) = id from
    funext (shearPt_neg_shearPt ε), image_id] at h2

/-- The shear maps the connected component in `U` of `q` onto the connected component in the
sheared `U` of the sheared `q`. -/
theorem connectedComponentIn_image_shearPt (ε : ℝ) (U : Set Point) (q : Point) :
    connectedComponentIn (shearPt ε '' U) (shearPt ε q) =
      shearPt ε '' connectedComponentIn U q := by
  by_cases hq : q ∈ U
  · have := (shearHomeo ε).image_connectedComponentIn hq
    rw [coe_shearHomeo] at this
    exact this.symm
  · rw [connectedComponentIn_eq_empty hq, image_empty, connectedComponentIn_eq_empty]
    rwa [(shearPt_injective ε).mem_set_image]

/-- **The filled region of the sheared polygon is the sheared filled region.** -/
theorem shear_filled (ε : ℝ) (P : Polygon) :
    (shear ε P).filled = shearPt ε '' P.filled := by
  ext p
  obtain ⟨q, rfl⟩ := shearPt_surjective ε p
  have hc : (shear ε P).boundaryᶜ = shearPt ε '' P.boundaryᶜ := by
    rw [shear_boundary, image_compl_eq (shearPt_bijective ε)]
  rw [Polygon.filled, Polygon.filled, hc, shear_boundary, image_union]
  simp only [mem_union, mem_ofPred_eq, connectedComponentIn_image_shearPt,
    isBoundedSet_image_shearPt_iff, (shearPt_injective ε).mem_set_image]

/-- The vertices of a triangle of the sheared polygon are the sheared vertices. -/
theorem shear_triVertices (ε : ℝ) (P : Polygon) (t : Polygon.Triangle) :
    (shear ε P).triVertices t = shearPt ε '' P.triVertices t := by
  simp only [Polygon.triVertices, shear_vtx, image_insert_eq, image_singleton]

/-- The convex hull commutes with the shear. -/
theorem convexHull_image_shearPt (ε : ℝ) (S : Set Point) :
    convexHull ℝ (shearPt ε '' S) = shearPt ε '' convexHull ℝ S :=
  ((isLinearMap_shearPt ε).image_convexHull S).symm

/-- A triangle of the sheared polygon is the sheared triangle. -/
theorem shear_triSet (ε : ℝ) (P : Polygon) (t : Polygon.Triangle) :
    (shear ε P).triSet t = shearPt ε '' P.triSet t := by
  rw [Polygon.triSet, Polygon.triSet, shear_triVertices, convexHull_image_shearPt]

/-- The interior commutes with the shear. -/
theorem interior_image_shearPt (ε : ℝ) (S : Set Point) :
    interior (shearPt ε '' S) = shearPt ε '' interior S := by
  have := (shearHomeo ε).image_interior S
  rw [coe_shearHomeo] at this
  exact this.symm

/-- Validity of a triangle is shear invariant. -/
theorem shear_validTriangle_iff (ε : ℝ) (P : Polygon) (t : Polygon.Triangle) :
    (shear ε P).validTriangle t ↔ P.validTriangle t := by
  simp only [Polygon.validTriangle, shear_n, shear_vtx, det_shearPt]

/-- The union of the triangles of the sheared polygon is the sheared union. -/
theorem shear_union_triSet (ε : ℝ) (P : Polygon) (T : List Polygon.Triangle) :
    {p | ∃ t ∈ T, p ∈ (shear ε P).triSet t} = shearPt ε '' {p | ∃ t ∈ T, p ∈ P.triSet t} := by
  ext p
  simp only [mem_ofPred_eq, shear_triSet, mem_image_shearPt]

/-- **The shear preserves triangulations** (both ways). -/
theorem shear_triangulates_iff (ε : ℝ) (P : Polygon) (T : List Polygon.Triangle) :
    (shear ε P).Triangulates T ↔ P.Triangulates T := by
  unfold Polygon.Triangulates
  rw [shear_union_triSet, shear_filled, image_shearPt_inj, shear_n]
  simp only [shear_validTriangle_iff, shear_triSet, interior_image_shearPt,
    disjoint_image_iff (shearPt_injective ε), shear_triVertices,
    ← image_inter (shearPt_injective ε), convexHull_image_shearPt, image_shearPt_inj]

/-- **WP-A: shear invariance.** -/
theorem shearInvariance : ShearInvarianceSpec := fun _ _ =>
  ⟨shear_simple, fun T => shear_triangulates_iff _ _ T⟩

end

end Chazelle.Core
