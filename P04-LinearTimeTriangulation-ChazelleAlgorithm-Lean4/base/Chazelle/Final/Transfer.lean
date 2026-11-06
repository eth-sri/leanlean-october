module

public import Chazelle.Final.LinkSplit
public import Chazelle.Core.ShearInv
public import Chazelle.Mountain.BaseSign

/-!
# Transfer between the input polygon and the sheared geometry polygon

The final stage runs on the input polygon `P` (the machine reads `P`'s coordinates) while the
tables describe the geometry polygon `Q = shear ε P` (`Chazelle.Core.ShearRel`).  This file
collects the facts that move every test and every conclusion between the two.

* `nodeWedge_shear`, `findCopy_shear`, `step_shear`, `runState_shear`: the linked-structure
  splitting only uses orientation tests, which are shear-invariant (`Core.det_shearPt`), so it
  computes the same structure on `P` and on `shear ε P`.
* `subPoly_shear`, `rotate_shear`: sub-polygons and rotations commute with the shear.
* `isMountain_of_shear`: a polygon whose vertices are vertices of `P` is a monotone mountain
  as soon as its shear is (the `(y, x)`-order of `P`'s vertices is that of `Q`'s: `YlexAgree`).
* `weakTriangulates_shear`: weak triangulations are transported by the shear.
* `orient_det_pos_of_ylexMin`: for a simple polygon and a `(y, x)`-lexicographically smallest
  vertex `k`, `0 < orient P * det v_{k-1} v_k v_{k+1}` (generalising
  `Chazelle.Mountain.mountain_orient_det`); this is how the machine computes the orientation.
-/

namespace Chazelle.Final

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Core (shear shearPt shear_vtx shear_n det_shearPt YlexAgree ShearRel)
open Chazelle.EarClip (subPoly n_subPoly)
open Chazelle.Existence (WeakTriangulates)
open Chazelle.Mountain (IsMountain ylexLT ylexLE orient orient_eq sign_eq_or_eq_neg)

/-! ### The splitting is shear-invariant -/

/-- The node wedge test reads only orientation signs, which the shear preserves. -/
theorem nodeWedge_shear (ε : ℝ) (P : Polygon) : nodeWedge (shear ε P) = nodeWedge P := by
  funext σ S z w
  simp only [nodeWedge, wedgeTest, shear_vtx, det_shearPt]

/-- The copy search is the same on `P` and on `shear ε P`. -/
theorem findCopy_shear (ε : ℝ) (P : Polygon) : findCopy (shear ε P) = findCopy P := by
  funext σ S v w
  unfold findCopy
  rw [nodeWedge_shear]

/-- One splitting step is the same on `P` and on `shear ε P`. -/
theorem step_shear (ε : ℝ) (P : Polygon) : step (shear ε P) = step P := by
  funext σ S d
  simp only [step, findCopy_shear]

/-- **The linked-structure run is the same on `P` and on `shear ε P`.** -/
theorem runState_shear (ε : ℝ) (P : Polygon) (σ : ℝ) (S : LState) (D : List (ℕ × ℕ)) :
    runState (shear ε P) σ S D = runState P σ S D := by
  induction D generalizing S with
  | nil => rfl
  | cons d D ih => rw [runState_cons, runState_cons, ih, step_shear]

/-! ### Sub-polygons, rotations, mountains -/

theorem subPoly_shear (ε : ℝ) (P : Polygon) (l : List ℕ) :
    subPoly (shear ε P) l = shear ε (subPoly P l) := by
  simp only [subPoly, shear, List.map_map]
  congr 1
  apply List.map_congr_left
  intro x _
  simp only [Function.comp, ← shear_vtx]
  rfl

/-- Rotation commutes with the shear. -/
theorem rotate_shear (ε : ℝ) (R : Polygon) (s : ℕ) :
    (shear ε R).rotate s = shear ε (R.rotate s) := by
  have hn : (shear ε R).n = R.n := shear_n ε R
  unfold Polygon.rotate
  rw [hn]
  simp only [shear_vtx]
  simp only [shear, List.map_map]
  rfl

/-- **Mountains transfer back from the shear.**  If every vertex of `R` is a vertex of `P`
(index `< P.n`), `YlexAgree P (shear ε P)` holds and `shear ε R` is a monotone mountain, then so
is `R`. -/
theorem isMountain_of_shear {ε : ℝ} {P R : Polygon} (hag : YlexAgree P (shear ε P))
    (hR : ∀ i < R.n, ∃ j < P.n, R.vtx i = P.vtx j) (hM : IsMountain (shear ε R)) :
    IsMountain R := by
  obtain ⟨hs, hinc⟩ := hM
  refine ⟨?_, fun i hi => ?_⟩
  · have := Chazelle.Core.shear_simple (ε := -ε) hs
    rwa [Chazelle.Core.shear_shear] at this
  · rw [shear_n] at hinc
    have h := hinc i hi
    rw [shear_vtx, shear_vtx] at h
    obtain ⟨j, hj, e⟩ := hR i (by omega)
    obtain ⟨j', hj', e'⟩ := hR (i + 1) hi
    rw [e, e'] at h ⊢
    rw [← shear_vtx, ← shear_vtx] at h
    exact (hag j j' hj hj').2 h

/-- The vertices of a rotated sub-polygon are vertices of `P`. -/
theorem vtx_rotate_subPoly {P : Polygon} {l : List ℕ} (hl : ∀ x ∈ l, x < P.n) (s : ℕ) :
    ∀ i < ((subPoly P l).rotate s).n, ∃ j < P.n, ((subPoly P l).rotate s).vtx i = P.vtx j := by
  intro i hi
  rw [Chazelle.Existence.n_rotate, n_subPoly] at hi
  rw [Chazelle.Existence.vtx_rotate _ _ (by rw [n_subPoly]; exact hi), n_subPoly,
    Chazelle.EarClip.vtx_subPoly_getD P l (Nat.mod_lt _ (by omega))]
  exact ⟨_, hl _ (getD_mem_of_lt (Nat.mod_lt _ (by omega))), rfl⟩

/-- **The mountain hypothesis of the piece triangulator transfers from `Q` to `P`.** -/
theorem mountain_transfer {ε : ℝ} {P : Polygon} (hag : YlexAgree P (shear ε P)) {l : List ℕ}
    (hl : ∀ x ∈ l, x < P.n)
    (h : ∃ s, IsMountain ((subPoly (shear ε P) l).rotate s) ∨
      IsMountain ((subPoly (shear ε P) l.reverse).rotate s)) :
    ∃ s, IsMountain ((subPoly P l).rotate s) ∨ IsMountain ((subPoly P l.reverse).rotate s) := by
  obtain ⟨s, h | h⟩ := h
  · rw [subPoly_shear, rotate_shear] at h
    exact ⟨s, Or.inl (isMountain_of_shear hag (vtx_rotate_subPoly hl s) h)⟩
  · rw [subPoly_shear, rotate_shear] at h
    exact ⟨s, Or.inr (isMountain_of_shear hag
      (vtx_rotate_subPoly (fun x hx => hl x (List.mem_reverse.1 hx)) s) h)⟩

/-! ### Weak triangulations -/

/-- **Weak triangulations are transported by the shear.** -/
theorem weakTriangulates_shear (ε : ℝ) {R : Polygon} {T : List Polygon.Triangle}
    (h : WeakTriangulates R T) : WeakTriangulates (shear ε R) T := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun t ht => (Chazelle.Core.shear_validTriangle_iff ε R t).2 (h1 t ht),
    by rw [shear_n]; exact h2, ?_, ?_, ?_⟩
  · rw [Chazelle.Core.shear_union_triSet, Chazelle.Core.shear_filled, h3]
  · refine h4.imp fun {s t} hd => ?_
    rw [Chazelle.Core.shear_triSet, Chazelle.Core.shear_triSet,
      Chazelle.Core.interior_image_shearPt, Chazelle.Core.interior_image_shearPt]
    exact (Set.disjoint_image_iff (Chazelle.Core.shearPt_injective ε)).2 hd
  · intro t ht i hi hv
    rw [shear_n] at hi
    rw [Chazelle.Core.shear_triSet, shear_vtx,
      (Chazelle.Core.shearPt_injective ε).mem_set_image] at hv
    rw [Chazelle.Core.shear_triVertices, shear_vtx]
    exact Set.mem_image_of_mem _ (h5 t ht i hi hv)

/-! ### The orientation from the lowest vertex -/

section Lowest

open Chazelle.Jordan
open Chazelle.Existence (sector_subset_interior det_ne_zero_of_lexMin)
open Chazelle.Visibility (transpose transpose_n transpose_vtx transpose_simple
  mem_transpose_filled_iff)
open Chazelle.Programs (lexLE)
open Chazelle.Geometry (lerp det_cyclic)
open Chazelle.Mountain (det_swap_swap_swap swap_mem_ball_swap_iff orient_eq_of_eventually)

/-- The transposed lowest vertex is lexicographically smallest. -/
theorem lexMin_transpose {P : Polygon} (hmin : ∀ i < P.n, ylexLE (P.vtx 0) (P.vtx i)) :
    ∀ i, i < (transpose P).n → lexLE ((transpose P).vtx 0) ((transpose P).vtx i) := by
  intro i hi
  rw [transpose_n] at hi
  rw [transpose_vtx, transpose_vtx]
  rcases hmin i hi with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2⟩

/-- The open sector at a `(y, x)`-smallest vertex `v₀` is interior (generalises
`Chazelle.Mountain.sector_lowest_subset_interior`). -/
theorem sector_ylexMin_subset_interior {P : Polygon} (hP : P.Simple)
    (hmin : ∀ i < P.n, ylexLE (P.vtx 0) (P.vtx i)) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hpos : 0 < σ * det (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1)) :
    ∃ r > 0, ∀ y ∈ ball (P.vtx 0) r,
      0 < σ * det (P.vtx (P.n - 1)) (P.vtx 0) y → 0 < σ * det (P.vtx 0) (P.vtx 1) y →
        y ∈ P.filled \ P.boundary := by
  set T := transpose P with hTdef
  have hT : T.Simple := transpose_simple hP
  have hTn : T.n = P.n := transpose_n P
  have hσ' : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> norm_num
  have hposT : 0 < (-σ) * det (T.vtx (T.n - 1)) (T.vtx 0) (T.vtx 1) := by
    rw [hTn, hTdef, transpose_vtx, transpose_vtx, transpose_vtx, det_swap_swap_swap]
    linarith
  obtain ⟨r, hr, hsec⟩ := sector_subset_interior hT (lexMin_transpose hmin) hσ' hposT
  refine ⟨r, hr, fun y hy h1 h2 => ?_⟩
  have := hsec y.swap (by rw [hTdef, transpose_vtx, swap_mem_ball_swap_iff]; exact hy)
    (by rw [hTn, hTdef, transpose_vtx, transpose_vtx, det_swap_swap_swap]; linarith)
    (by rw [hTdef, transpose_vtx, transpose_vtx, det_swap_swap_swap]; linarith)
  rw [Set.mem_sdiff, mem_transpose_filled_iff, Chazelle.Visibility.mem_transpose_boundary_iff,
    Prod.swap_swap] at this
  exact this

/-- **The orientation is the sign of the corner at a `(y, x)`-smallest vertex `0`**
(generalises `Chazelle.Mountain.mountain_orient_det`). -/
theorem orient_det_pos_of_ylexMin0 {P : Polygon} (hP : P.Simple)
    (hmin : ∀ i < P.n, ylexLE (P.vtx 0) (P.vtx i)) :
    0 < orient P * det (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) := by
  have hn := simple_three_le hP
  have hdet : det (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) ≠ 0 := by
    have := det_ne_zero_of_lexMin (transpose_simple hP) (lexMin_transpose hmin)
    rw [transpose_n, transpose_vtx, transpose_vtx, transpose_vtx, det_swap_swap_swap] at this
    intro h; apply this; rw [h, neg_zero]
  obtain ⟨σ, hσ, hpos⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      0 < σ * det (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) := by
    rcases lt_or_gt_of_ne hdet with h | h
    · exact ⟨-1, Or.inr rfl, by linarith⟩
    · exact ⟨1, Or.inl rfl, by linarith⟩
  obtain ⟨r, hr, hsec⟩ := sector_ylexMin_subset_interior hP hmin hσ hpos
  set u := P.vtx (P.n - 1) with hu
  set v := P.vtx 0 with hv
  set w := P.vtx 1 with hw
  have huv : u ≠ v := simple_vtx_ne hP (by omega) (by omega) (by omega)
  have hsq := sqLen_pos huv
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hW : IsOpen (ball v r ∩ {x | 0 < σ * det v w x}) := isOpen_ball.inter (isOpen_det_pos v w σ)
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), lerp u v (1 - s) ∈ ball v r ∩ {x | 0 < σ * det v w x} ∧
      s ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [(tendsto_lerp_one_sub u v).eventually (isOpen_ball.mem_nhds (mem_ball_self hr)),
      Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with s hs hs01
    refine ⟨⟨hs, ?_⟩, hs01⟩
    show 0 < σ * det v w (lerp u v (1 - s))
    rw [Geometry.det_lerp, Geometry.det_self_outer, det_cyclic]
    nlinarith [mul_pos hs01.1 hpos]
  obtain ⟨s, hsW, hs01⟩ := hev.exists
  have hsucc : (P.n - 1 + 1) % P.n = 0 := by rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
  have hor : orient P = σ := by
    apply orient_eq_of_eventually hP (i := P.n - 1) (by omega) (t := 1 - s)
      ⟨by linarith [hs01.2], by linarith [hs01.1]⟩ hσ
    rw [hsucc, ← hu, ← hv]
    filter_upwards [eventually_offset_mem σ hW hsW, self_mem_nhdsWithin] with δ hδ hδ0
    have hδ0' : (0 : ℝ) < δ := hδ0
    refine (hsec _ hδ.1 ?_ hδ.2).1
    show 0 < σ * det u v (offset u v (1 - s) (σ * δ))
    rw [det_offset, show σ * (σ * δ * sqLen u v) = (σ * σ) * (δ * sqLen u v) by ring, hσ2, one_mul]
    exact mul_pos hδ0' hsq
  rw [hor]
  exact hpos

/-- **The orientation from any `(y, x)`-smallest vertex `k`**:
`0 < orient P * det v_{k-1} v_k v_{k+1}` (indices modulo `n`). -/
theorem orient_det_pos_of_ylexMin {P : Polygon} (hP : P.Simple) {k : ℕ} (hk : k < P.n)
    (hmin : ∀ i < P.n, ylexLE (P.vtx k) (P.vtx i)) :
    0 < orient P * det (P.vtx ((k + P.n - 1) % P.n)) (P.vtx k) (P.vtx ((k + 1) % P.n)) := by
  have hn := simple_three_le hP
  set R := P.rotate k with hR
  have hRs : R.Simple := Chazelle.Existence.simple_rotate P k hP
  have hRn : R.n = P.n := Chazelle.Existence.n_rotate P k
  have hv0 : R.vtx 0 = P.vtx k := by
    rw [hR, Chazelle.Existence.vtx_rotate P k (by omega), Nat.add_zero, Nat.mod_eq_of_lt hk]
  have hv1 : R.vtx 1 = P.vtx ((k + 1) % P.n) := by
    rw [hR, Chazelle.Existence.vtx_rotate P k (by omega)]
  have hvl : R.vtx (R.n - 1) = P.vtx ((k + P.n - 1) % P.n) := by
    rw [hRn, hR, Chazelle.Existence.vtx_rotate P k (by omega)]
    congr 2; omega
  have hminR : ∀ i < R.n, ylexLE (R.vtx 0) (R.vtx i) := by
    intro i hi
    rw [hRn] at hi
    rw [hv0, hR, Chazelle.Existence.vtx_rotate P k hi]
    exact hmin _ (Nat.mod_lt _ (by omega))
  have h := orient_det_pos_of_ylexMin0 hRs hminR
  have hor : orient P = orient R := by
    refine Chazelle.Mountain.orient_eq_of_filled_subset hRs hP (i := 0) (j := k) (by omega) hk
      hv0 ?_ (by rw [hR, Chazelle.Existence.filled_rotate])
    rw [hRn, Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < P.n), hv1]
  rw [hor, ← hv0, ← hv1, ← hvl]
  exact h

/-- **The orientation as a computable sign.**  If `k` is a `(y, x)`-smallest vertex and `σ`
is `1` when the corner determinant at `k` is positive and `-1` otherwise, then
`σ = orient P`. -/
theorem orient_eq_of_ylexMin {P : Polygon} (hP : P.Simple) {k : ℕ} (hk : k < P.n)
    (hmin : ∀ i < P.n, ylexLE (P.vtx k) (P.vtx i)) {σ : ℝ}
    (hσ : σ = if 0 < det (P.vtx ((k + P.n - 1) % P.n)) (P.vtx k) (P.vtx ((k + 1) % P.n))
      then 1 else -1) : orient P = σ := by
  have h := orient_det_pos_of_ylexMin hP hk hmin
  split_ifs at hσ with hd
  · rcases orient_eq P with ho | ho
    · rw [ho, hσ]
    · rw [ho] at h; nlinarith
  · rcases orient_eq P with ho | ho
    · rw [ho] at h; exact absurd (by linarith) hd
    · rw [ho, hσ]

end Lowest

end

end Chazelle.Final
