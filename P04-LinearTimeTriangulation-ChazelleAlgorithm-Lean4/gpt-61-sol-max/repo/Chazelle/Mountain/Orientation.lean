module

public meta import Chazelle.Arithmetic

public import Chazelle.Ears.Test

/-!
# The orientation of a simple polygon and the convexity test for ears

For a simple polygon `P` the interior lies on the *same* side of every edge (this is the content
of `Chazelle.Jordan.two_components`: the left offsets of all edges lie in one component of the
complement of the boundary, the right offsets in the other).  We record this side as a sign:

* `LeftInside P`: the left offsets of edge `0` near its midpoint are filled;
* `orient P : ℝ` is `1` if `LeftInside P` and `-1` otherwise.

Main statements (all for `hP : P.Simple`):

* `eventually_offset_orient`: for every edge `i` and parameter `t ∈ (0,1)`, for all small
  `δ > 0` the point of the edge pushed by `orient P * δ` (along the left normal) is interior and
  the point pushed by `-(orient P * δ)` is exterior — **the interior side is uniform**.
* `orient_eq_of_frequently`: if points on the `σ`-side (`σ = ±1`) of some edge are filled
  for arbitrarily small offsets, then `orient P = σ`.
* `orient_eq_of_filled_subset`: two simple polygons sharing an edge (as a directed segment),
  one with filled region inside the other, have the same orientation.
* `interior_triangle_mem_filled_iff`: if the open triangle `a v b` (with `a v` an edge of `P`)
  avoids the boundary, then it is interior exactly when `0 < orient P * det a v b`.
* `orient_det_pos_of_three`: a simple triangle has `0 < orient P * det v₀ v₁ v₂`.
* `isEar_iff_convex_of_empty`: for `n ≥ 4`, a nondegenerate corner `(prev i, i, next i)` whose
  closed triangle contains no other vertex is an ear **iff** it is strictly convex on the
  interior side, `0 < orient P * det (vtx (prev i)) (vtx i) (vtx (next i))`.
* `orient_det_pos_of_isEar`: every ear apex is strictly convex on the interior side.
-/

namespace Chazelle.Mountain

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Jordan
open Chazelle.Existence
open Chazelle.Ears
open Chazelle.Geometry (lerp lerp_fst lerp_snd det_lerp det_cyclic det_cyclic_right det_swap12
  det_swap13 det_swap23 det_self_left det_self_right det_self_outer
  det_eq_zero_of_mem_segment lerp_zero lerp_one lerp_mem_segment point_ext point_ext_iff
  mem_segment_iff_lerp ne_of_det_ne_zero continuous_lerp convex_triangle
  bary₁ bary₂ bary₃ bary₁_lerp bary₂_lerp bary₃_lerp mem_triangle_iff_bary
  mem_interior_triangle_iff bary₁_vertex_left bary₁_vertex_mid bary₁_vertex_right
  bary₂_vertex_left bary₂_vertex_mid bary₂_vertex_right bary₃_vertex_left bary₃_vertex_mid
  bary₃_vertex_right continuous_bary₁ continuous_bary₂ centroid_mem_interior)

/-! ### The orientation -/

/-- The left offsets of edge `0` near its midpoint are filled. -/
def LeftInside (P : Polygon) : Prop :=
  ∀ᶠ δ in 𝓝[>] (0 : ℝ), leftPoint P 0 (1 / 2) δ ∈ P.filled

open Classical in
/-- The orientation sign of a polygon: `1` when the interior is on the left of the edges,
`-1` when it is on the right. -/
noncomputable def orient (P : Polygon) : ℝ := if LeftInside P then 1 else -1

variable (P : Polygon)

/-- The orientation is `1` or `-1`. -/
theorem orient_eq : orient P = 1 ∨ orient P = -1 := by
  core_grind


/-- Two signs in `{1, -1}` are equal or opposite. -/
theorem sign_eq_or_eq_neg {σ τ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    σ = τ ∨ σ = -τ := by
  grind

/-- **The interior side is uniform.**  For every edge `i` and `t ∈ (0,1)`, for all small
`δ > 0` the offset point `offset (vtx i) (vtx (i+1)) t (orient P * δ)` lies in the interior region
and the opposite offset point lies outside the filled region. -/
theorem eventually_offset_orient {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      offset (P.vtx i) (P.vtx ((i + 1) % P.n)) t (orient P * δ) ∈ P.filled \ P.boundary ∧
      offset (P.vtx i) (P.vtx ((i + 1) % P.n)) t (-(orient P * δ)) ∉ P.filled := by
  have hn := simple_three_le hP
  obtain ⟨cL, cR, hcL, hcR, hne, -, hsides⟩ := two_components hP
  have h0 := hsides 0 (by omega) (1 / 2) ⟨by norm_num, by norm_num⟩
  have hi' := hsides i hi t ht
  have hLI : LeftInside P ↔ parity P cL = true := by
    constructor
    · intro h
      obtain ⟨δ, h1, h2⟩ := (h.and h0).exists
      unfold leftPoint at h1
      have hb : offset (P.vtx 0) (P.vtx ((0 + 1) % P.n)) (1 / 2) δ ∉ P.boundary :=
        connectedComponentIn_subset _ _ h2.1
      rw [mem_filled_iff hP hb] at h1
      rw [← parity_eq_of_mem_connectedComponentIn P h2.1]
      exact h1
    · intro h
      filter_upwards [h0] with δ hδ
      unfold leftPoint
      rw [mem_filled_iff hP (connectedComponentIn_subset _ _ hδ.1),
        parity_eq_of_mem_connectedComponentIn P hδ.1]
      exact h
  filter_upwards [hi'] with δ hδ
  have hb1 : offset (P.vtx i) (P.vtx ((i + 1) % P.n)) t δ ∉ P.boundary :=
    connectedComponentIn_subset _ _ hδ.1
  have hb2 : offset (P.vtx i) (P.vtx ((i + 1) % P.n)) t (-δ) ∉ P.boundary :=
    connectedComponentIn_subset _ _ hδ.2
  have hp1 := parity_eq_of_mem_connectedComponentIn P hδ.1
  have hp2 := parity_eq_of_mem_connectedComponentIn P hδ.2
  unfold orient
  split_ifs with hL
  · have hpL := hLI.1 hL
    have hpR : parity P cR = false := by
      grind
    rw [one_mul]
    refine ⟨⟨(mem_filled_iff hP hb1).2 (by grind), hb1⟩, ?_⟩
    intro hf
    rw [mem_filled_iff hP hb2, hp2, hpR] at hf
    simp_all
  · have hpL : parity P cL = false := by
      grind
    have hpR : parity P cR = true := by
      grind
    simp only [neg_one_mul, neg_neg]
    refine ⟨⟨(mem_filled_iff hP hb2).2 (by grind), hb2⟩, ?_⟩
    intro hf
    rw [mem_filled_iff hP hb1, hp1, hpL] at hf
    simp_all

/-- **The orientation is determined by any edge**: if for arbitrarily small `δ > 0` the point
of edge `i` at parameter `t ∈ (0,1)` pushed by `σ * δ` (`σ = ±1`) is filled, then
`orient P = σ`. -/
theorem orient_eq_of_frequently {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : ∃ᶠ δ in 𝓝[>] (0 : ℝ),
      offset (P.vtx i) (P.vtx ((i + 1) % P.n)) t (σ * δ) ∈ P.filled) :
    orient P = σ := by
  by_contra hne
  have hσ' : σ = -orient P := by
    rcases sign_eq_or_eq_neg hσ (orient_eq P) with h' | h'
    all_goals simp_all
  obtain ⟨δ, h1, h2⟩ := (h.and_eventually (eventually_offset_orient hP hi ht)).exists
  simp_all

/-- Variant of `orient_eq_of_frequently` with an `eventually` hypothesis. -/
theorem orient_eq_of_eventually {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      offset (P.vtx i) (P.vtx ((i + 1) % P.n)) t (σ * δ) ∈ P.filled) :
    orient P = σ :=
  orient_eq_of_frequently hP hi ht hσ h.frequently

/-- **Orientation transfers along a shared edge.**  If `Q` and `P` are simple, the directed
edge `i` of `Q` coincides with the directed edge `j` of `P`, and `Q.filled ⊆ P.filled`, then
`orient P = orient Q`. -/
theorem orient_eq_of_filled_subset {Q P : Polygon} (hQ : Q.Simple) (hP : P.Simple) {i j : ℕ}
    (hi : i < Q.n) (hj : j < P.n) (h1 : Q.vtx i = P.vtx j)
    (h2 : Q.vtx ((i + 1) % Q.n) = P.vtx ((j + 1) % P.n)) (hsub : Q.filled ⊆ P.filled) :
    orient P = orient Q := by
  apply orient_eq_of_eventually hP hj (t := 1 / 2) ⟨by norm_num, by norm_num⟩ (orient_eq Q)
  filter_upwards [eventually_offset_orient hQ hi (t := 1 / 2) ⟨by norm_num, by norm_num⟩]
    with δ hδ
  rw [← h1, ← h2]
  exact hsub hδ.1.1

/-! ### The open triangle on an edge -/

/-- **The open triangle on an edge is interior iff it is on the interior side.**  Let `a v` be
the directed edge `i` of `P`, `b` a point with `det a v b ≠ 0`, and suppose the open triangle
`a v b` avoids the boundary.  Then a point of the open triangle is filled iff
`0 < orient P * det a v b`. -/
theorem interior_triangle_mem_filled_iff {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n)
    {b : Point} (hdet : det (P.vtx i) (P.vtx ((i + 1) % P.n)) b ≠ 0)
    (hoff : ∀ x ∈ interior (convexHull ℝ ({P.vtx i, P.vtx ((i + 1) % P.n), b} : Set Point)),
      x ∉ P.boundary)
    {x : Point} (hx : x ∈ interior (convexHull ℝ ({P.vtx i, P.vtx ((i + 1) % P.n), b} : Set Point))) :
    x ∈ P.filled ↔ 0 < orient P * det (P.vtx i) (P.vtx ((i + 1) % P.n)) b := by
  set a := P.vtx i with ha
  set v := P.vtx ((i + 1) % P.n) with hv
  have hav : a ≠ v := (ne_of_det_ne_zero hdet).1
  have hsq := sqLen_pos hav
  set D := interior (convexHull ℝ ({a, v, b} : Set Point)) with hD
  have hconn : IsPreconnected D := (convex_triangle a v b).interior.isPreconnected
  have hsub : D ⊆ P.boundaryᶜ := fun y hy => hoff y hy
  obtain ⟨σ, hσ, hpos⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ 0 < σ * det a v b := by
    grind
  -- the offset points of the edge at its midpoint, on the `σ` side, lie in the open triangle
  set W : Set Point := {y | 0 < bary₁ a v b y} ∩ {y | 0 < bary₂ a v b y} with hW
  have hWo : IsOpen W :=
    (isOpen_lt continuous_const (continuous_bary₁ a v b)).inter
      (isOpen_lt continuous_const (continuous_bary₂ a v b))
  have hmW : lerp a v (1 / 2) ∈ W := by
    refine ⟨?_, ?_⟩
    · show 0 < bary₁ a v b (lerp a v (1 / 2))
      rw [bary₁_lerp, bary₁_vertex_left hdet, bary₁_vertex_mid]; norm_num
    · show 0 < bary₂ a v b (lerp a v (1 / 2))
      rw [bary₂_lerp, bary₂_vertex_left, bary₂_vertex_mid hdet]; norm_num
  have hev1 := eventually_offset_mem σ hWo hmW
  have hev2 := eventually_offset_orient hP hi (t := 1 / 2) ⟨by norm_num, by norm_num⟩
  obtain ⟨δ, hδW, hδor, hδ0⟩ := (hev1.and (hev2.and self_mem_nhdsWithin)).exists
  have hδ0' : (0 : ℝ) < δ := hδ0
  rw [← ha, ← hv] at hδor
  have hpD : offset a v (1 / 2) (σ * δ) ∈ D := by
    rw [hD, mem_interior_triangle_iff hdet]
    refine ⟨hδW.1, hδW.2, ?_⟩
    unfold bary₃
    rw [det_offset]
    have e : σ * δ * sqLen a v / det a v b =
        δ * sqLen a v * (σ * det a v b) / (det a v b * det a v b) := by
      rw [div_eq_div_iff hdet (mul_ne_zero hdet hdet)]
      ring
    rw [e]
    exact div_pos (mul_pos (mul_pos hδ0' hsq) hpos) (mul_self_pos.2 hdet)
  have hxb : x ∉ P.boundary := hoff x hx
  have hpar := parity_eq_of_isPreconnected P hconn hsub hx hpD
  rcases sign_eq_or_eq_neg hσ (orient_eq P) with heq | heq
  · -- the convex side is the interior side
    subst heq
    refine iff_of_true ?_ hpos
    rw [mem_filled_iff hP hxb, hpar, ← mem_filled_iff hP (hoff _ hpD)]
    exact hδor.1.1
  · -- the convex side is the exterior side
    subst heq
    rw [neg_mul] at hpD hpar
    refine iff_of_false ?_ (by linarith)
    intro hf
    rw [mem_filled_iff hP hxb, hpar, ← mem_filled_iff hP (hoff _ hpD)] at hf
    grind

/-- **A simple triangle is strictly convex on the interior side**:
`0 < orient P * det v₀ v₁ v₂`. -/
theorem orient_det_pos_of_three {P : Polygon} (hP : P.Simple) (h3 : P.n = 3) :
    0 < orient P * det (P.vtx 0) (P.vtx 1) (P.vtx 2) := by
  have hdet := det_ne_zero_of_simple_three P hP h3
  have h1 : (0 + 1) % P.n = 1 := by rw [h3]
  have key := interior_triangle_mem_filled_iff hP (i := 0) (by omega) (b := P.vtx 2)
    (by simp_all)
    (by rw [h1]; intro x hx; exact not_mem_boundary_of_mem_interior_triangle P h3 hdet hx)
    (x := Geometry.centroid (P.vtx 0) (P.vtx 1) (P.vtx 2))
    (by rw [h1]; exact centroid_mem_interior hdet)
  rw [h1] at key
  rw [← key, filled_eq_triangle P hP h3]
  exact interior_subset (centroid_mem_interior hdet)

/-! ### Ears and convexity -/

/-- Under the "no other vertex in the closed corner triangle" hypothesis, the open corner
triangle at vertex `i` avoids the boundary. -/
theorem interior_earHull_not_mem_boundary {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n)
    (hdet : det (P.vtx (prevIdx P i)) (P.vtx i) (P.vtx ((i + 1) % P.n)) ≠ 0)
    (hnone : ∀ j, j < P.n → j ≠ prevIdx P i → j ≠ i → j ≠ (i + 1) % P.n →
      P.vtx j ∉ convexHull ℝ ({P.vtx (prevIdx P i), P.vtx i, P.vtx ((i + 1) % P.n)} : Set Point))
    {x : Point}
    (hx : x ∈ interior (convexHull ℝ
      ({P.vtx (prevIdx P i), P.vtx i, P.vtx ((i + 1) % P.n)} : Set Point))) :
    x ∉ P.boundary := by
  have h3 := simple_three_le hP
  have hn : 0 < P.n := by omega
  set Q := P.rotate i with hQdef
  have hQ : Q.Simple := simple_rotate P i hP
  have hQn : Q.n = P.n := n_rotate P i
  obtain ⟨ea, ev, eb⟩ := vtx_rotate_fan P i (by omega) hi
  have hdetQ : det (Q.vtx (Q.n - 1)) (Q.vtx 0) (Q.vtx 1) ≠ 0 := by
    grind
  have hnoneQ : ∀ j, j < Q.n →
      Q.vtx j ∈ convexHull ℝ ({Q.vtx (Q.n - 1), Q.vtx 0, Q.vtx 1} : Set Point) →
        j = 0 ∨ j = 1 ∨ j = Q.n - 1 := by
    intro j hj hmem
    rw [ea, ev, eb] at hmem
    rw [hQn] at hj ⊢
    have hQj : Q.vtx j = P.vtx ((i + j) % P.n) := vtx_rotate P i hj
    rw [hQj] at hmem
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨hj0, hj1, hjn⟩ := hcon
    refine hnone ((i + j) % P.n) (Nat.mod_lt _ hn) ?_ ?_ ?_ hmem
    · intro h
      unfold prevIdx at h
      rw [show i + P.n - 1 = i + (P.n - 1) by omega] at h
      exact hjn (rot_index_inj hj (by omega) h)
    · intro h
      exact hj0 (rot_index_inj hj hn (by rw [h, Nat.add_zero, Nat.mod_eq_of_lt hi]))
    · intro h
      exact hj1 (rot_index_inj hj (by omega) h)
  have hvert := vert_le_zero_of_none hnoneQ
  rw [mem_interior_triangle_iff hdet] at hx
  rw [← boundary_rotate P i]
  rw [← ea, ← ev, ← eb] at hx
  exact interior_fan_not_mem_boundary hQ hdetQ hvert hx.1 hx.2.1 hx.2.2

/-- **The ear test by convexity.**  For a simple polygon with `n ≥ 4` and a vertex `i` whose
corner `(prev i, i, next i)` is nondegenerate and whose closed corner triangle contains no other
vertex, vertex `i` is the apex of an ear iff the corner is strictly convex on the interior side:
`0 < orient P * det (vtx (prev i)) (vtx i) (vtx (next i))`. -/
theorem isEar_iff_convex_of_empty {P : Polygon} (hP : P.Simple) (h4 : 4 ≤ P.n) {i : ℕ}
    (hi : i < P.n)
    (hdet : det (P.vtx (prevIdx P i)) (P.vtx i) (P.vtx ((i + 1) % P.n)) ≠ 0)
    (hnone : ∀ j, j < P.n → j ≠ prevIdx P i → j ≠ i → j ≠ (i + 1) % P.n →
      P.vtx j ∉ convexHull ℝ ({P.vtx (prevIdx P i), P.vtx i, P.vtx ((i + 1) % P.n)} : Set Point)) :
    IsEar P i ↔ 0 < orient P * det (P.vtx (prevIdx P i)) (P.vtx i) (P.vtx ((i + 1) % P.n)) := by
  rw [isEar_iff P i hP h4 hi]
  simp only [hdet, ne_eq, not_false_eq_true, true_and]
  rw [and_iff_right hnone]
  set a := P.vtx (prevIdx P i) with ha
  set v := P.vtx i with hv
  set b := P.vtx ((i + 1) % P.n) with hb
  have hab : a ≠ b := vtx_prev_ne_vtx_succ P i hP hi
  set m := lerp a b (1 / 2) with hm
  have hmB : m ∉ P.boundary :=
    open_chord_not_mem_boundary_of_test P i hP h4 hi hdet hnone m
      (lerp_mem_segment _ _ (by norm_num) (by norm_num)) (lerp_ne_left hab (by norm_num))
      (lerp_ne_right hab (by norm_num))
  -- barycentric coordinates of the midpoint of the chord
  have hm1 : bary₁ a v b m = 1 / 2 := by
    rw [hm, bary₁_lerp, bary₁_vertex_left hdet, bary₁_vertex_right]; ring
  have hm2 : bary₂ a v b m = 0 := by
    grind [bary₂_lerp, bary₂_vertex_left, bary₂_vertex_right]
  have hm3 : bary₃ a v b m = 1 / 2 := by
    rw [hm, bary₃_lerp, bary₃_vertex_left, bary₃_vertex_right hdet]; ring
  -- the segment from the midpoint towards the apex
  have hint : ∀ s ∈ Ioo (0 : ℝ) 1, lerp m v s ∈ interior (convexHull ℝ ({a, v, b} : Set Point)) := by
    intro s hs
    rw [mem_interior_triangle_iff hdet]
    refine ⟨?_, ?_, ?_⟩
    · rw [bary₁_lerp, hm1, bary₁_vertex_mid]; nlinarith [hs.1, hs.2]
    · rw [bary₂_lerp, hm2, bary₂_vertex_mid hdet]; nlinarith [hs.1]
    · rw [bary₃_lerp, hm3, bary₃_vertex_mid]; nlinarith [hs.1, hs.2]
  have hoff : ∀ x ∈ interior (convexHull ℝ ({a, v, b} : Set Point)), x ∉ P.boundary :=
    fun x hx => interior_earHull_not_mem_boundary hP hi hdet hnone hx
  have hS : IsPreconnected (lerp m v '' Icc (0 : ℝ) (1 / 2)) :=
    isPreconnected_Icc.image _ (continuous_lerp m v).continuousOn
  have hSb : lerp m v '' Icc (0 : ℝ) (1 / 2) ⊆ P.boundaryᶜ := by
    grind [lerp_zero]
  have hx1 : lerp m v (1 / 2) ∈ interior (convexHull ℝ ({a, v, b} : Set Point)) :=
    hint (1 / 2) ⟨by norm_num, by norm_num⟩
  have hpar := parity_eq_of_isPreconnected P hS hSb (x := lerp m v 0) (y := lerp m v (1 / 2))
    ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩ ⟨1 / 2, ⟨by norm_num, le_rfl⟩, rfl⟩
  rw [lerp_zero] at hpar
  -- the edge `prev i` is the directed segment `a v`
  have hprev : prevIdx P i < P.n := prevIdx_lt P hi
  have hsucc : P.vtx ((prevIdx P i + 1) % P.n) = v := by rw [prevIdx_add_one_mod P hi]
  have key := interior_triangle_mem_filled_iff hP hprev (b := b) (by grind)
    (by rw [hsucc]; exact hoff) (x := lerp m v (1 / 2)) (by grind)
  rw [hsucc] at key
  rw [← key, hpar, ← mem_filled_iff hP (hoff _ hx1)]

/-- **Every ear apex is strictly convex on the interior side.** -/
theorem orient_det_pos_of_isEar {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n)
    (he : IsEar P i) :
    0 < orient P * det (P.vtx (prevIdx P i)) (P.vtx i) (P.vtx ((i + 1) % P.n)) := by
  have h4 := four_le_of_isEar P i he
  obtain ⟨hdet, hnone, -⟩ := (isEar_iff P i hP h4 hi).1 he
  exact (isEar_iff_convex_of_empty hP h4 hi hdet hnone).1 he

end

end Chazelle.Mountain
