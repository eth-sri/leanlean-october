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

@[simp] theorem transpose_n (P : Polygon) : (transpose P).n = P.n := by
  simp [transpose, Polygon.n]

@[simp] theorem transpose_vtx (P : Polygon) (i : ℕ) : (transpose P).vtx i = (P.vtx i).swap := by
  simp only [transpose, Polygon.vtx, List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases P.vertices[i]? with _ | p <;> rfl

@[simp] theorem transpose_transpose (P : Polygon) : transpose (transpose P) = P := by
  simp [transpose, List.map_map]

/-- Swapping the coordinates of both endpoints transports a segment. -/
theorem segment_swap (a b : Point) :
    Chazelle.segment a.swap b.swap = Prod.swap ⁻¹' Chazelle.segment a b := by
  ext p
  simp only [Chazelle.segment, mem_ofPred_eq, mem_preimage, Prod.swap, Geometry.point_ext_iff]
  constructor
  · rintro ⟨t, h0, h1, h⟩
    exact ⟨t, h0, h1, h.2, h.1⟩
  · rintro ⟨t, h0, h1, h⟩
    exact ⟨t, h0, h1, h.2, h.1⟩

theorem transpose_edge (P : Polygon) (i : ℕ) :
    (transpose P).edge i = Prod.swap ⁻¹' P.edge i := by
  simp only [Polygon.edge, transpose_n, transpose_vtx, segment_swap]

/-- The boundary of the transpose is the transposed boundary. -/
theorem transpose_boundary (P : Polygon) : (transpose P).boundary = Prod.swap ⁻¹' P.boundary := by
  ext p
  simp only [Polygon.boundary, mem_ofPred_eq, mem_preimage, transpose_n, transpose_edge]

theorem transpose_commonEndpoints (P : Polygon) (i j : ℕ) :
    (transpose P).commonEndpoints i j = Prod.swap ⁻¹' P.commonEndpoints i j := by
  ext p
  simp only [Polygon.commonEndpoints, mem_ofPred_eq, mem_preimage, transpose_n, transpose_vtx]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rcases h1 with h | h
      · left; rw [h, Prod.swap_swap]
      · right; rw [h, Prod.swap_swap]
    · rcases h2 with h | h
      · left; rw [h, Prod.swap_swap]
      · right; rw [h, Prod.swap_swap]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rcases h1 with h | h
      · left; rw [← h, Prod.swap_swap]
      · right; rw [← h, Prod.swap_swap]
    · rcases h2 with h | h
      · left; rw [← h, Prod.swap_swap]
      · right; rw [← h, Prod.swap_swap]

/-- The transpose of a simple polygon is simple. -/
theorem transpose_simple {P : Polygon} (hP : P.Simple) : (transpose P).Simple := by
  obtain ⟨h3, hinj, hedge⟩ := hP
  refine ⟨by simpa using h3, ?_, ?_⟩
  · intro i j hi hj h
    rw [transpose_n] at hi hj
    rw [transpose_vtx, transpose_vtx] at h
    exact hinj i j hi hj (Prod.swap_injective h)
  · intro i j hi hj hij
    rw [transpose_n] at hi hj
    rw [transpose_edge, transpose_edge, transpose_commonEndpoints, ← preimage_inter,
      hedge i j hi hj hij]

/-- `Prod.swap` as a homeomorphism of the plane. -/
def swapHomeo : Point ≃ₜ Point := Homeomorph.prodComm ℝ ℝ

@[simp] theorem swapHomeo_apply (p : Point) : swapHomeo p = p.swap := rfl

theorem swap_image_eq_preimage (S : Set Point) : Prod.swap '' S = Prod.swap ⁻¹' S := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩; simpa using hq
  · intro h; exact ⟨p.swap, h, Prod.swap_swap p⟩

/-- Connected components in a transposed set are the transposed components. -/
theorem connectedComponentIn_swap (S : Set Point) (z : Point) :
    connectedComponentIn (Prod.swap ⁻¹' S) z = Prod.swap ⁻¹' connectedComponentIn S z.swap := by
  by_cases hz : z ∈ Prod.swap ⁻¹' S
  · have := swapHomeo.image_connectedComponentIn hz
    have hcoe : ⇑swapHomeo = Prod.swap := rfl
    rw [hcoe, swap_image_eq_preimage, swap_image_eq_preimage, preimage_preimage] at this
    simp only [Prod.swap_swap, preimage_id'] at this
    rw [← this, preimage_preimage]
    simp
  · have hz' : z.swap ∉ S := hz
    rw [connectedComponentIn_eq_empty hz, connectedComponentIn_eq_empty hz']
    simp

/-- Boundedness is invariant under transposition. -/
theorem isBoundedSet_swap_iff (S : Set Point) : IsBoundedSet (Prod.swap ⁻¹' S) ↔ IsBoundedSet S := by
  constructor
  · rintro ⟨R, hR⟩
    refine ⟨R, fun p hp => ?_⟩
    have := hR p.swap (by simpa using hp)
    exact ⟨this.2, this.1⟩
  · rintro ⟨R, hR⟩
    refine ⟨R, fun p hp => ?_⟩
    have := hR p.swap hp
    exact ⟨this.2, this.1⟩

/-- The filled region of the transpose is the transposed filled region. -/
theorem transpose_filled (P : Polygon) : (transpose P).filled = Prod.swap ⁻¹' P.filled := by
  ext p
  simp only [Polygon.filled, transpose_boundary, mem_union, mem_preimage, mem_ofPred_eq]
  rw [← preimage_compl, connectedComponentIn_swap, isBoundedSet_swap_iff]

theorem mem_transpose_filled_iff (P : Polygon) (p : Point) :
    p ∈ (transpose P).filled ↔ p.swap ∈ P.filled := by
  rw [transpose_filled]; rfl

theorem mem_transpose_boundary_iff (P : Polygon) (p : Point) :
    p ∈ (transpose P).boundary ↔ p.swap ∈ P.boundary := by
  rw [transpose_boundary]; rfl

/-! ### Horizontal parity -/

/-! ### Horizontal rays and their first boundary hit -/

/-- The point at parameter `t` on the horizontal ray from `p` in direction `σ`. -/
def rayPt (p : Point) (σ t : ℝ) : Point := (p.1 + σ * t, p.2)

@[simp] theorem rayPt_fst (p : Point) (σ t : ℝ) : (rayPt p σ t).1 = p.1 + σ * t := rfl
@[simp] theorem rayPt_snd (p : Point) (σ t : ℝ) : (rayPt p σ t).2 = p.2 := rfl
@[simp] theorem rayPt_zero (p : Point) (σ : ℝ) : rayPt p σ 0 = p := by
  simp [rayPt]

theorem continuous_rayPt (p : Point) (σ : ℝ) : Continuous (rayPt p σ) := by
  unfold rayPt; fun_prop

theorem rayPt_injective (p : Point) {σ : ℝ} (hσ : σ ≠ 0) : Function.Injective (rayPt p σ) := by
  intro s t h
  have := congrArg Prod.fst h
  simp only [rayPt_fst] at this
  exact mul_left_cancel₀ hσ (by linarith)

/-- The parameters `t > 0` at which the ray meets the boundary. -/
def hitSet (P : Polygon) (p : Point) (σ : ℝ) : Set ℝ :=
  {t : ℝ | 0 < t ∧ rayPt p σ t ∈ P.boundary}

/-- The parameter of the first boundary point of the open ray (`sInf` of `hitSet`; `0` when the
ray never meets the boundary). -/
noncomputable def hitParam (P : Polygon) (p : Point) (σ : ℝ) : ℝ := sInf (hitSet P p σ)

theorem hitSet_bddBelow (P : Polygon) (p : Point) (σ : ℝ) : BddBelow (hitSet P p σ) :=
  ⟨0, fun _ ht => ht.1.le⟩

/-- A connected piece of a horizontal ray avoiding the boundary and containing an interior point
is interior. -/
theorem rayPt_mem_interior_of_isPreconnected {P : Polygon} (hP : P.Simple) {p : Point} {σ : ℝ}
    {I : Set ℝ} (hI : IsPreconnected I) (hIb : ∀ t ∈ I, rayPt p σ t ∉ P.boundary)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) (hint : rayPt p σ t₀ ∈ P.filled \ P.boundary) :
    ∀ t ∈ I, rayPt p σ t ∈ P.filled \ P.boundary := by
  intro t ht
  have himg : IsPreconnected (rayPt p σ '' I) := hI.image _ (continuous_rayPt p σ).continuousOn
  have hsub : rayPt p σ '' I ⊆ P.boundaryᶜ := by
    rintro _ ⟨s, hs, rfl⟩; exact hIb s hs
  have hpar := parity_eq_of_isPreconnected P himg hsub (mem_image_of_mem _ ht₀) (mem_image_of_mem _ ht)
  refine ⟨?_, hIb t ht⟩
  rw [mem_filled_iff hP (hIb t ht), ← hpar, ← mem_filled_iff hP hint.2]
  exact hint.1

/-- If the open ray never met the boundary it would be an unbounded connected subset of the
filled region: so the ray meets the boundary. -/
theorem hitSet_nonempty {P : Polygon} (hP : P.Simple) {p : Point} {σ : ℝ} (hσ : σ ≠ 0)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (hint : rayPt p σ t₀ ∈ P.filled \ P.boundary) :
    (hitSet P p σ).Nonempty := by
  by_contra hempty
  rw [not_nonempty_iff_eq_empty] at hempty
  have hIb : ∀ t ∈ Ioi (0 : ℝ), rayPt p σ t ∉ P.boundary := by
    intro t ht hmem
    have : t ∈ hitSet P p σ := ⟨ht, hmem⟩
    rw [hempty] at this
    exact this
  have hall := rayPt_mem_interior_of_isPreconnected hP isPreconnected_Ioi hIb ht₀ hint
  obtain ⟨R, hR⟩ := filled_bounded P
  -- a far point of the ray, beyond `t₀`, leaves the square of radius `R`
  obtain ⟨s, hs0, hRs⟩ := exists_abs_add_mul_gt hσ (p.1 + σ * t₀) R
  have hs : t₀ + s ∈ Ioi (0 : ℝ) := by simp only [mem_Ioi]; linarith
  have h3 := (hR _ (hall _ hs).1).1
  simp only [rayPt_fst] at h3
  have : p.1 + σ * (t₀ + s) = p.1 + σ * t₀ + s * σ := by ring
  rw [this] at h3
  exact absurd h3 (not_le.2 hRs)

/-- **The first hit.**  If an initial open stretch `(0, t₀)` of the ray is interior, then the
first-hit parameter is at least `t₀`, the first-hit point is on the boundary, and every point of
the ray strictly before it is interior. -/
theorem hit_of_initial {P : Polygon} (hP : P.Simple) {p : Point} {σ : ℝ} (hσ : σ ≠ 0)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (hint : ∀ t, 0 < t → t < t₀ → rayPt p σ t ∈ P.filled \ P.boundary) :
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

/-- Every boundary point of the open ray is at or after the first hit. -/
theorem hitParam_le_of_mem_boundary (P : Polygon) (p : Point) (σ : ℝ) {t : ℝ} (ht : 0 < t)
    (hmem : rayPt p σ t ∈ P.boundary) : hitParam P p σ ≤ t :=
  csInf_le (hitSet_bddBelow P p σ) ⟨ht, hmem⟩

/-- **Uniqueness of the first hit.**  A boundary point of the open ray with no boundary point of
the ray strictly before it is the first hit. -/
theorem hitParam_eq_of_first (P : Polygon) (p : Point) (σ : ℝ) {t : ℝ} (ht : 0 < t)
    (hmem : rayPt p σ t ∈ P.boundary) (hfirst : ∀ s, 0 < s → s < t → rayPt p σ s ∉ P.boundary) :
    hitParam P p σ = t := by
  refine le_antisymm (hitParam_le_of_mem_boundary P p σ ht hmem) (le_csInf ⟨t, ht, hmem⟩ ?_)
  intro s hs
  by_contra h
  exact hfirst s hs.1 (not_le.1 h) hs.2

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
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht1]
  exact ht2

/-! ### The interior-point specialisations -/

/-- The parameter of the first boundary point of the horizontal ray to the right of `q`. -/
noncomputable def rightHitParam (P : Polygon) (q : Point) : ℝ := hitParam P q 1

/-- The parameter of the first boundary point of the horizontal ray to the left of `q`. -/
noncomputable def leftHitParam (P : Polygon) (q : Point) : ℝ := hitParam P q (-1)

theorem rayPt_one (q : Point) (t : ℝ) : rayPt q 1 t = (q.1 + t, q.2) := by
  simp [rayPt]

theorem rayPt_neg_one (q : Point) (t : ℝ) : rayPt q (-1) t = (q.1 - t, q.2) := by
  simp [rayPt, sub_eq_add_neg]

/-- The full first-hit package for the right ray from an interior point. -/
theorem rightHit_spec {P : Polygon} (hP : P.Simple) {q : Point} (hq : q ∈ P.filled \ P.boundary) :
    0 < rightHitParam P q ∧ (q.1 + rightHitParam P q, q.2) ∈ P.boundary ∧
      ∀ t, 0 ≤ t → t < rightHitParam P q → (q.1 + t, q.2) ∈ P.filled \ P.boundary := by
  obtain ⟨t₀, ht₀, hint⟩ := exists_initial_interior hP hq 1
  obtain ⟨h1, h2, h3⟩ := hit_of_initial hP one_ne_zero ht₀ hint
  rw [rayPt_one] at h2
  refine ⟨lt_of_lt_of_le ht₀ h1, h2, fun t ht0 ht1 => ?_⟩
  rcases ht0.lt_or_eq with h | h
  · have := h3 t h ht1
    rwa [rayPt_one] at this
  · rw [← h, add_zero]; exact hq

/-- The right ray from an interior point meets the boundary at a positive parameter. -/
theorem rightHitParam_pos {P : Polygon} (hP : P.Simple) {q : Point}
    (hq : q ∈ P.filled \ P.boundary) : 0 < rightHitParam P q :=
  (rightHit_spec hP hq).1

/-- The first hit point of the right ray lies on the boundary. -/
theorem rightHit_mem_boundary {P : Polygon} (hP : P.Simple) {q : Point}
    (hq : q ∈ P.filled \ P.boundary) : (q.1 + rightHitParam P q, q.2) ∈ P.boundary :=
  (rightHit_spec hP hq).2.1

/-- The half-open ray segment from `q` to its first hit is interior. -/
theorem open_ray_subset_interior {P : Polygon} (hP : P.Simple) {q : Point}
    (hq : q ∈ P.filled \ P.boundary) :
    ∀ t, 0 ≤ t → t < rightHitParam P q → (q.1 + t, q.2) ∈ P.filled \ P.boundary :=
  (rightHit_spec hP hq).2.2

/-- The full first-hit package for the left ray from an interior point. -/
theorem leftHit_spec {P : Polygon} (hP : P.Simple) {q : Point} (hq : q ∈ P.filled \ P.boundary) :
    0 < leftHitParam P q ∧ (q.1 - leftHitParam P q, q.2) ∈ P.boundary ∧
      ∀ t, 0 ≤ t → t < leftHitParam P q → (q.1 - t, q.2) ∈ P.filled \ P.boundary := by
  obtain ⟨t₀, ht₀, hint⟩ := exists_initial_interior hP hq (-1)
  obtain ⟨h1, h2, h3⟩ := hit_of_initial hP (neg_ne_zero.2 one_ne_zero) ht₀ hint
  rw [rayPt_neg_one] at h2
  refine ⟨lt_of_lt_of_le ht₀ h1, h2, fun t ht0 ht1 => ?_⟩
  rcases ht0.lt_or_eq with h | h
  · have := h3 t h ht1
    rwa [rayPt_neg_one] at this
  · rw [← h, sub_zero]; exact hq

theorem leftHitParam_pos {P : Polygon} (hP : P.Simple) {q : Point}
    (hq : q ∈ P.filled \ P.boundary) : 0 < leftHitParam P q :=
  (leftHit_spec hP hq).1

theorem leftHit_mem_boundary {P : Polygon} (hP : P.Simple) {q : Point}
    (hq : q ∈ P.filled \ P.boundary) : (q.1 - leftHitParam P q, q.2) ∈ P.boundary :=
  (leftHit_spec hP hq).2.1

theorem open_left_ray_subset_interior {P : Polygon} (hP : P.Simple) {q : Point}
    (hq : q ∈ P.filled \ P.boundary) :
    ∀ t, 0 ≤ t → t < leftHitParam P q → (q.1 - t, q.2) ∈ P.filled \ P.boundary :=
  (leftHit_spec hP hq).2.2

/-! ### Comparison with the half-open scan -/

end

end Chazelle.Visibility
