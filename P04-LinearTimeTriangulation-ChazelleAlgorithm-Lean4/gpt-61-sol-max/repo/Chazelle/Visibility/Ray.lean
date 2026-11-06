module

public import Chazelle.Jordan.Jordan
public import Chazelle.Programs.RayScanSpec
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Order.LeftRightNhds

/-!
# First hits of horizontal rays

Two tools for the horizontal visibility map.

## The transpose polygon

`transpose P` swaps the two coordinates of every vertex.  The map `Prod.swap` is a
homeomorphism of the plane, so `n`, `vtx`, `edge`, `boundary`, `commonEndpoints`, `Simple` and
`filled` all transfer (`transpose_boundary`, `transpose_simple`, `transpose_filled`, ...).  This
turns every statement of the Jordan development about *vertical* rays (`Chazelle.Jordan.crosses`,
`parity`) into a statement about *horizontal* rays: `parityH P z := parity (transpose P) z.swap`,
and `hitsRight_iff_crosses_swap` identifies the half-open horizontal ray test `HitsRight` of the
program specification with `crosses` on the transpose.  Consequence
(`exists_hitsRight_of_interior`): from an interior point the half-open scan always hits some edge.

## The Euclidean first hit

For a point `p` and a horizontal direction `σ ≠ 0`, `rayPt p σ t = (p.1 + σ * t, p.2)` and
`hitParam P p σ = sInf {t | 0 < t ∧ rayPt p σ t ∈ P.boundary}` is the parameter of the *first*
boundary point of the open ray.  The main lemma `hit_of_initial` needs only that an initial open
stretch of the ray is interior; then the hit exists, is at a positive parameter, lies on the
boundary, and everything before it is interior.  Specialised to an interior point `q`
(`rightHitParam`, `leftHitParam`) and, in `Chord.lean`, to a vertex.

Finally the Euclidean first hit is compared with the half-open scan's answer `FirstHitRight`:
the scan's hit is at or after the Euclidean one (`rightHitParam_le_of_firstHitRight`), and when
they differ the Euclidean hit point is a vertex or lies on a horizontal edge at the height of the
ray (`rightHit_vertex_or_horizontal_of_lt`).
-/

namespace Chazelle.Visibility

@[expose] public section

open Set Filter Topology
open Chazelle.Jordan

/-! ### The transpose polygon -/

/-- The polygon with the two coordinates of every vertex exchanged. -/
def transpose (P : Polygon) : Polygon := ⟨P.vertices.map Prod.swap⟩

section
variable (P : Polygon)
@[simp] theorem transpose_n : (transpose P).n = P.n := by
  simp [transpose, Polygon.n]

@[simp] theorem transpose_vtx (i : ℕ) : (transpose P).vtx i = (P.vtx i).swap := by
  grind [transpose, Polygon.vtx, List.getD_eq_getElem?_getD, List.getElem?_map]



end

/-- Swapping the coordinates of both endpoints transports a segment. -/
theorem segment_swap (a b : Point) :
    Chazelle.segment a.swap b.swap = Prod.swap ⁻¹' Chazelle.segment a b := by
  ext p
  simp only [Chazelle.segment, mem_ofPred_eq, mem_preimage, Prod.swap, Geometry.point_ext_iff]
  grind

section
variable (P : Polygon)
theorem transpose_edge (i : ℕ) :
    (transpose P).edge i = Prod.swap ⁻¹' P.edge i := by
  grind [Polygon.edge, transpose_n, transpose_vtx, segment_swap]

/-- The boundary of the transpose is the transposed boundary. -/
theorem transpose_boundary : (transpose P).boundary = Prod.swap ⁻¹' P.boundary := by
  ext p
  grind [Polygon.boundary, mem_ofPred_eq, mem_preimage, transpose_n, transpose_edge]

theorem transpose_commonEndpoints (i j : ℕ) :
    (transpose P).commonEndpoints i j = Prod.swap ⁻¹' P.commonEndpoints i j := by
  ext p
  simp only [Polygon.commonEndpoints, mem_ofPred_eq, mem_preimage, transpose_n, transpose_vtx]
  constructor
  · grind
  grind


end

/-- The transpose of a simple polygon is simple. -/
theorem transpose_simple {P : Polygon} (hP : P.Simple) : (transpose P).Simple := by
  obtain ⟨h3, hinj, hedge⟩ := hP
  refine ⟨by simpa using h3, ?_, ?_⟩
  · grind [transpose_n, transpose_vtx]
  grind [transpose_n, transpose_edge, transpose_commonEndpoints, preimage_inter]

/-- `Prod.swap` as a homeomorphism of the plane. -/
def swapHomeo : Point ≃ₜ Point := Homeomorph.prodComm ℝ ℝ


section
variable (S : Set Point)
theorem swap_image_eq_preimage : Prod.swap '' S = Prod.swap ⁻¹' S := by
  grind

/-- Connected components in a transposed set are the transposed components. -/
theorem connectedComponentIn_swap (z : Point) :
    connectedComponentIn (Prod.swap ⁻¹' S) z = Prod.swap ⁻¹' connectedComponentIn S z.swap := by
  by_cases hz : z ∈ Prod.swap ⁻¹' S
  · have := swapHomeo.image_connectedComponentIn hz
    have hcoe : ⇑swapHomeo = Prod.swap := rfl
    rw [hcoe, swap_image_eq_preimage, swap_image_eq_preimage, preimage_preimage] at this
    grind [Prod.swap_swap, preimage_id', preimage_preimage]
  · have hz' : z.swap ∉ S := hz
    rw [connectedComponentIn_eq_empty hz, connectedComponentIn_eq_empty hz']
    simp

/-- Boundedness is invariant under transposition. -/
theorem isBoundedSet_swap_iff : IsBoundedSet (Prod.swap ⁻¹' S) ↔ IsBoundedSet S := by
  constructor
  · rintro ⟨R, hR⟩
    refine ⟨R, fun p hp => ?_⟩
    grind
  · rintro ⟨R, hR⟩
    refine ⟨R, fun p hp => ?_⟩
    grind


end

section
variable (P : Polygon)
/-- The filled region of the transpose is the transposed filled region. -/
theorem transpose_filled : (transpose P).filled = Prod.swap ⁻¹' P.filled := by
  ext p
  simp only [Polygon.filled, transpose_boundary, mem_union, mem_preimage, mem_ofPred_eq]
  rw [← preimage_compl, connectedComponentIn_swap, isBoundedSet_swap_iff]

theorem mem_transpose_filled_iff (p : Point) :
    p ∈ (transpose P).filled ↔ p.swap ∈ P.filled := by
  grind [transpose_filled]

theorem mem_transpose_boundary_iff (p : Point) :
    p ∈ (transpose P).boundary ↔ p.swap ∈ P.boundary := by
  grind [transpose_boundary]

/-! ### Horizontal parity -/

/-! ### Horizontal rays and their first boundary hit -/


end

/-- The point at parameter `t` on the horizontal ray from `p` in direction `σ`. -/
def rayPt (p : Point) (σ t : ℝ) : Point := (p.1 + σ * t, p.2)

section
variable (p : Point)
@[simp] theorem rayPt_fst (σ t : ℝ) : (rayPt p σ t).1 = p.1 + σ * t := rfl
@[simp] theorem rayPt_snd (σ t : ℝ) : (rayPt p σ t).2 = p.2 := rfl
@[simp] theorem rayPt_zero (σ : ℝ) : rayPt p σ 0 = p := by
  simp [rayPt]

theorem continuous_rayPt (σ : ℝ) : Continuous (rayPt p σ) := by
  unfold rayPt; fun_prop

theorem rayPt_injective {σ : ℝ} (hσ : σ ≠ 0) : Function.Injective (rayPt p σ) := by
  intro s t h
  grind [rayPt_fst]


end

section
variable (P : Polygon) (p : Point) (σ : ℝ)
include P p σ
/-- The parameters `t > 0` at which the ray meets the boundary. -/
def hitSet : Set ℝ :=
  {t : ℝ | 0 < t ∧ rayPt p σ t ∈ P.boundary}

/-- The parameter of the first boundary point of the open ray (`sInf` of `hitSet`; `0` when the
ray never meets the boundary). -/
noncomputable def hitParam : ℝ := sInf (hitSet P p σ)

theorem hitSet_bddBelow : BddBelow (hitSet P p σ) :=
  ⟨0, fun _ ht => ht.1.le⟩


end

section
variable {P : Polygon} (hP : P.Simple) {p : Point} {σ : ℝ}
include hP
/-- A connected piece of a horizontal ray avoiding the boundary and containing an interior point
is interior. -/
theorem rayPt_mem_interior_of_isPreconnected
    {I : Set ℝ} (hI : IsPreconnected I) (hIb : ∀ t ∈ I, rayPt p σ t ∉ P.boundary)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) (hint : rayPt p σ t₀ ∈ P.filled \ P.boundary) :
    ∀ t ∈ I, rayPt p σ t ∈ P.filled \ P.boundary := by
  intro t ht
  have himg : IsPreconnected (rayPt p σ '' I) := hI.image _ (continuous_rayPt p σ).continuousOn
  have hsub : rayPt p σ '' I ⊆ P.boundaryᶜ := by
    grind
  have hpar := parity_eq_of_isPreconnected P himg hsub (mem_image_of_mem _ ht₀) (mem_image_of_mem _ ht)
  refine ⟨?_, hIb t ht⟩
  rw [mem_filled_iff hP (hIb t ht), ← hpar, ← mem_filled_iff hP hint.2]
  exact hint.1

section
variable (hσ : σ ≠ 0) {t₀ : ℝ} (ht₀ : 0 < t₀)
include hσ t₀ ht₀
/-- If the open ray never met the boundary it would be an unbounded connected subset of the
filled region: so the ray meets the boundary. -/
theorem hitSet_nonempty (hint : rayPt p σ t₀ ∈ P.filled \ P.boundary) :
    (hitSet P p σ).Nonempty := by
  by_contra hempty
  rw [not_nonempty_iff_eq_empty] at hempty
  have hIb : ∀ t ∈ Ioi (0 : ℝ), rayPt p σ t ∉ P.boundary := by
    intro t ht hmem
    have : t ∈ hitSet P p σ := ⟨ht, hmem⟩
    simp_all
  have hall := rayPt_mem_interior_of_isPreconnected hP isPreconnected_Ioi hIb ht₀ hint
  obtain ⟨R, hR⟩ := filled_bounded P
  -- a far point of the ray, beyond `t₀`, leaves the square of radius `R`
  obtain ⟨s, hs0, hRs⟩ := exists_abs_add_mul_gt hσ (p.1 + σ * t₀) R
  have hs : t₀ + s ∈ Ioi (0 : ℝ) := by grind
  grind [rayPt_fst]

/-- **The first hit.**  If an initial open stretch `(0, t₀)` of the ray is interior, then the
first-hit parameter is at least `t₀`, the first-hit point is on the boundary, and every point of
the ray strictly before it is interior. -/
theorem hit_of_initial (hint : ∀ t, 0 < t → t < t₀ → rayPt p σ t ∈ P.filled \ P.boundary) :
    t₀ ≤ hitParam P p σ ∧ rayPt p σ (hitParam P p σ) ∈ P.boundary ∧
      ∀ t, 0 < t → t < hitParam P p σ → rayPt p σ t ∈ P.filled \ P.boundary := by
  have hmid : rayPt p σ (t₀ / 2) ∈ P.filled \ P.boundary := hint _ (by linarith) (by linarith)
  have hne := hitSet_nonempty hP hσ (by linarith : 0 < t₀ / 2) hmid
  -- every hit parameter is `≥ t₀`
  have hge : ∀ t ∈ hitSet P p σ, t₀ ≤ t := by
    intro t ht
    by_contra h
    exact (hint t ht.1 (not_le.1 h)).2 ht.2
  have h1 : t₀ ≤ hitParam P p σ := le_csInf hne hge
  -- the hit set is the closed set `{t | t₀ ≤ t ∧ rayPt ∈ boundary}`
  have hset : hitSet P p σ = {t : ℝ | t₀ ≤ t ∧ rayPt p σ t ∈ P.boundary} := by
    ext t
    constructor
    · intro ht; exact ⟨hge t ht, ht.2⟩
    · intro ht; exact ⟨lt_of_lt_of_le ht₀ ht.1, ht.2⟩
  have hclosed : IsClosed (hitSet P p σ) := by
    rw [hset]
    exact (isClosed_Ici).inter ((isClosed_boundary P).preimage (continuous_rayPt p σ))
  have h2 : rayPt p σ (hitParam P p σ) ∈ P.boundary :=
    (hclosed.csInf_mem hne (hitSet_bddBelow P p σ)).2
  refine ⟨h1, h2, ?_⟩
  have hIb : ∀ t ∈ Ioo (0 : ℝ) (hitParam P p σ), rayPt p σ t ∉ P.boundary := by
    intro t ht hmem
    have : t ∈ hitSet P p σ := ⟨ht.1, hmem⟩
    exact absurd (csInf_le (hitSet_bddBelow P p σ) this) (not_le.2 ht.2)
  have hmid' : t₀ / 2 ∈ Ioo (0 : ℝ) (hitParam P p σ) := ⟨by linarith, by linarith⟩
  exact fun t ht1 ht2 =>
    rayPt_mem_interior_of_isPreconnected hP isPreconnected_Ioo hIb hmid' hmid t ⟨ht1, ht2⟩



end

end

section
variable (P : Polygon) (p : Point) (σ : ℝ) {t : ℝ} (ht : 0 < t) (hmem : rayPt p σ t ∈ P.boundary)
include ht hmem
/-- Every boundary point of the open ray is at or after the first hit. -/
theorem hitParam_le_of_mem_boundary : hitParam P p σ ≤ t :=
  csInf_le (hitSet_bddBelow P p σ) ⟨ht, hmem⟩

/-- **Uniqueness of the first hit.**  A boundary point of the open ray with no boundary point of
the ray strictly before it is the first hit. -/
theorem hitParam_eq_of_first (hfirst : ∀ s, 0 < s → s < t → rayPt p σ s ∉ P.boundary) :
    hitParam P p σ = t := by
  refine le_antisymm (hitParam_le_of_mem_boundary P p σ ht hmem) (le_csInf ⟨t, ht, hmem⟩ ?_)
  intro s hs
  by_contra h
  exact hfirst s hs.1 (not_le.1 h) hs.2


end

/-- An interior point has an interior initial stretch on every horizontal ray. -/
theorem exists_initial_interior {P : Polygon} (hP : P.Simple) {q : Point}
    (hq : q ∈ P.filled \ P.boundary) (σ : ℝ) :
    ∃ t₀ > 0, ∀ t, 0 < t → t < t₀ → rayPt q σ t ∈ P.filled \ P.boundary := by
  have hopen : IsOpen (P.filled \ P.boundary) := isOpen_filled_sdiff_boundary hP
  have hcont : ContinuousAt (rayPt q σ) 0 := (continuous_rayPt q σ).continuousAt
  have hmem : P.filled \ P.boundary ∈ 𝓝 (rayPt q σ 0) := by
    rw [rayPt_zero]; exact hopen.mem_nhds hq
  have := hcont.preimage_mem_nhds hmem
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 this
  refine ⟨ε, hε, fun t ht1 ht2 => hball ?_⟩
  grind [Metric.mem_ball, Real.dist_eq, sub_zero]

/-! ### The interior-point specialisations -/

section
variable (P : Polygon) (q : Point)
include P q
/-- The parameter of the first boundary point of the horizontal ray to the right of `q`. -/
noncomputable def rightHitParam : ℝ := hitParam P q 1

/-- The parameter of the first boundary point of the horizontal ray to the left of `q`. -/
noncomputable def leftHitParam : ℝ := hitParam P q (-1)


end

section
variable (q : Point) (t : ℝ)
theorem rayPt_one : rayPt q 1 t = (q.1 + t, q.2) := by
  simp [rayPt]

theorem rayPt_neg_one : rayPt q (-1) t = (q.1 - t, q.2) := by
  aesop


end

section
variable {P : Polygon} (hP : P.Simple) {q : Point} (hq : q ∈ P.filled \ P.boundary)
include hP hq
/-- The full first-hit package for the right ray from an interior point. -/
theorem rightHit_spec :
    0 < rightHitParam P q ∧ (q.1 + rightHitParam P q, q.2) ∈ P.boundary ∧
      ∀ t, 0 ≤ t → t < rightHitParam P q → (q.1 + t, q.2) ∈ P.filled \ P.boundary := by
  obtain ⟨t₀, ht₀, hint⟩ := exists_initial_interior hP hq 1
  obtain ⟨h1, h2, h3⟩ := hit_of_initial hP one_ne_zero ht₀ hint
  rw [rayPt_one] at h2
  refine ⟨lt_of_lt_of_le ht₀ h1, h2, fun t ht0 ht1 => ?_⟩
  rcases ht0.lt_or_eq with h | h
  · have := h3 t h ht1
    grind [rayPt_one]
  grind

/-- The right ray from an interior point meets the boundary at a positive parameter. -/
theorem rightHitParam_pos : 0 < rightHitParam P q :=
  (rightHit_spec hP hq).1

/-- The first hit point of the right ray lies on the boundary. -/
theorem rightHit_mem_boundary : (q.1 + rightHitParam P q, q.2) ∈ P.boundary :=
  (rightHit_spec hP hq).2.1

/-- The half-open ray segment from `q` to its first hit is interior. -/
theorem open_ray_subset_interior :
    ∀ t, 0 ≤ t → t < rightHitParam P q → (q.1 + t, q.2) ∈ P.filled \ P.boundary :=
  (rightHit_spec hP hq).2.2

/-- The full first-hit package for the left ray from an interior point. -/
theorem leftHit_spec :
    0 < leftHitParam P q ∧ (q.1 - leftHitParam P q, q.2) ∈ P.boundary ∧
      ∀ t, 0 ≤ t → t < leftHitParam P q → (q.1 - t, q.2) ∈ P.filled \ P.boundary := by
  obtain ⟨t₀, ht₀, hint⟩ := exists_initial_interior hP hq (-1)
  obtain ⟨h1, h2, h3⟩ := hit_of_initial hP (neg_ne_zero.2 one_ne_zero) ht₀ hint
  rw [rayPt_neg_one] at h2
  refine ⟨lt_of_lt_of_le ht₀ h1, h2, fun t ht0 ht1 => ?_⟩
  rcases ht0.lt_or_eq with h | h
  · have := h3 t h ht1
    grind [rayPt_neg_one]
  grind

theorem leftHitParam_pos : 0 < leftHitParam P q :=
  (leftHit_spec hP hq).1

theorem leftHit_mem_boundary : (q.1 - leftHitParam P q, q.2) ∈ P.boundary :=
  (leftHit_spec hP hq).2.1

theorem open_left_ray_subset_interior :
    ∀ t, 0 ≤ t → t < leftHitParam P q → (q.1 - t, q.2) ∈ P.filled \ P.boundary :=
  (leftHit_spec hP hq).2.2

/-! ### Comparison with the half-open scan -/


end

end

end Chazelle.Visibility
