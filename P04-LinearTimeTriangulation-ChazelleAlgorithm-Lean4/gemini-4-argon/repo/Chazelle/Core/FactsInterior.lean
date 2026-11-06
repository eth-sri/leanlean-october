module

public import Chazelle.Core.FactsChain
public import Chazelle.Mountain.PiecesMain

/-!
# WP-B: the interior model satisfies the walk axioms

For a simple polygon `Q`, the interior model `interiorModel Q` (domain the interior
`Q.filled \ Q.boundary`, walk `interiorWalk Q` oriented with the interior on its left,
admissible chords the horizontal chords of the interior) satisfies the walk axioms `WalkAx`
(`walkAx_interiorModel`).

## Local structure of a simple polygon with the interior on the left

For a simple polygon `W` with `orient W = 1`:

* `edge_local`: near a point inside an edge, the open left half-plane is interior, the open
  right half-plane is exterior, and the line is the boundary (`strip` and the uniform interior
  side `eventually_offset_orient`);
* `vertex_local`: near a vertex, the open left sector of the corner is interior, the open right
  sector is exterior, and every point off the boundary is in one of the two (`sideSector`,
  coverage `sideCcw_or`, and simplicity: the corner is not a spike);
* `pos_unique`: a point of the boundary is at a single walk position.

## The chord system of the interior

`chordPoly`: for a horizontal chord from `e₁` (on edge `i`) to `e₂` (on edge `j ≠ i`), the closed
walk `vtx (i+1), …, vtx j, e₂, e₁` has its boundary in `∂W ∪ c` and its crossing parity flips
across the chord (`Jordan.parity_flip`), so every finite admissible family is a
`ChordSystem` of the interior (`interior_chordSystem`).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft SideClean ChordSystem IsHChordIn
  sideLeftOf sideCcw sideCross sideDot sideNonSpike sideSector sideLeftOf_not_seg_prev
  sideLeftOf_not_seg_next sideCcw_or sideCross_out sideLeft_edge sideLeft_zero sidePt_zero)
open Chazelle.Jordan
open Chazelle.Mountain (LeftInside orient orient_eq eventually_offset_orient)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext lerp_mem_segment lerp_zero lerp_one
  lerp_injective)
open Chazelle.Visibility (hseg)

namespace FactsInterior

variable {W : Polygon}

/-! ## Being filled is constant on preconnected sets off the boundary -/

theorem filled_iff_of_preconnected (hW : W.Simple) {S : Set Point} (hS : IsPreconnected S)
    (hSb : S ⊆ W.boundaryᶜ) {x y : Point} (hx : x ∈ S) (hy : y ∈ S) :
    x ∈ W.filled ↔ y ∈ W.filled := by
  rw [mem_filled_iff hW (hSb hx), mem_filled_iff hW (hSb hy),
    parity_eq_of_isPreconnected W hS hSb hx hy]

/-- A preconnected set off the boundary meeting the interior lies in the interior. -/
theorem subset_interior (hW : W.Simple) {S : Set Point} (hS : IsPreconnected S)
    (hSb : S ⊆ W.boundaryᶜ) {x : Point} (hx : x ∈ S) (hxi : x ∈ W.filled) :
    S ⊆ W.filled \ W.boundary := fun _y hy =>
  ⟨(filled_iff_of_preconnected hW hS hSb hx hy).1 hxi, hSb hy⟩

/-- A preconnected set off the boundary meeting the exterior lies in the exterior. -/
theorem subset_exterior (hW : W.Simple) {S : Set Point} (hS : IsPreconnected S)
    (hSb : S ⊆ W.boundaryᶜ) {x : Point} (hx : x ∈ S) (hxe : x ∉ W.filled) :
    S ⊆ W.filledᶜ := fun _y hy h =>
  hxe ((filled_iff_of_preconnected hW hS hSb hx hy).2 h)

/-! ## Near a point inside an edge -/

/-- **Near a point inside an edge**: the open left half-plane is interior, the open right
half-plane exterior, and the line of the edge is the boundary. -/
theorem edge_local (hW : W.Simple) (hL : orient W = 1) {p : ℕ} (hp : p < W.n) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ r > 0, ∀ x ∈ ball (sidePt W p t) r,
      (0 < det (W.vtx p) (W.vtx ((p + 1) % W.n)) x → x ∈ W.filled \ W.boundary) ∧
      (det (W.vtx p) (W.vtx ((p + 1) % W.n)) x < 0 → x ∉ W.filled) ∧
      (det (W.vtx p) (W.vtx ((p + 1) % W.n)) x = 0 → x ∈ W.boundary) := by
  set u := W.vtx p
  set v := W.vtx ((p + 1) % W.n)
  have huv : u ≠ v := simple_vtx_succ_ne hW hp
  have hsq := sqLen_pos huv
  obtain ⟨r, hr, hstrip⟩ := strip hW hp ht
  refine ⟨r, hr, fun x hx => ⟨fun hdet => ?_, fun hdet => ?_, fun hdet => ?_⟩⟩
  · -- the left half-ball
    set H := ball (sidePt W p t) r ∩ {y | 0 < 1 * det u v y}
    have hHc : IsPreconnected H := ((convex_ball _ _).inter (convex_det_pos _ _ 1)).isPreconnected
    have hHb : H ⊆ W.boundaryᶜ := fun y hy hyb => by
      have := (hstrip y hy.1).1 hyb
      have h2 := hy.2
      simp only [mem_ofPred_eq, one_mul] at h2
      linarith
    obtain ⟨δ, hδ1, hδ2, hδ0⟩ := ((eventually_offset_orient hW hp ht).and
      ((eventually_offset_mem 1 isOpen_ball (mem_ball_self hr) (u := u) (v := v) (t := t)).and
        self_mem_nhdsWithin)).exists
    rw [hL, one_mul] at hδ1
    rw [one_mul] at hδ2
    have hδ : (0 : ℝ) < δ := hδ0
    have hmem : offset u v t δ ∈ H := ⟨hδ2, by
      show 0 < 1 * det u v (offset u v t δ)
      rw [one_mul, det_offset]; exact mul_pos hδ hsq⟩
    exact subset_interior hW hHc hHb hmem hδ1.1.1 ⟨hx, by simpa using hdet⟩
  · -- the right half-ball
    set H := ball (sidePt W p t) r ∩ {y | 0 < (-1) * det u v y}
    have hHc : IsPreconnected H :=
      ((convex_ball _ _).inter (convex_det_pos _ _ (-1))).isPreconnected
    have hHb : H ⊆ W.boundaryᶜ := fun y hy hyb => by
      have := (hstrip y hy.1).1 hyb
      have h2 := hy.2
      simp only [mem_ofPred_eq] at h2
      rw [this] at h2; linarith
    obtain ⟨δ, hδ1, hδ2, hδ0⟩ := ((eventually_offset_orient hW hp ht).and
      ((eventually_offset_mem (-1) isOpen_ball (mem_ball_self hr) (u := u) (v := v)
        (t := t)).and self_mem_nhdsWithin)).exists
    rw [hL, one_mul] at hδ1
    have hδ : (0 : ℝ) < δ := hδ0
    have e : -δ = (-1) * δ := by ring
    rw [e] at hδ1
    have hmem : offset u v t ((-1) * δ) ∈ H := ⟨hδ2, by
      show 0 < (-1) * det u v (offset u v t ((-1) * δ))
      rw [det_offset]; nlinarith [mul_pos hδ hsq]⟩
    exact subset_exterior hW hHc hHb hmem hδ1.2 ⟨hx, by simp only [mem_ofPred_eq]; linarith⟩
  · exact (hstrip x hx).2 hdet

/-! ## Near a vertex -/

/-- The two edges at a vertex of a simple polygon meet only at the vertex. -/
theorem corner_meet (hW : W.Simple) {p : ℕ} (hp : p < W.n) :
    Chazelle.segment (W.vtx (prevIdx W p)) (W.vtx p) ∩
      Chazelle.segment (W.vtx p) (W.vtx ((p + 1) % W.n)) ⊆ {W.vtx p} := by
  have hn := simple_three_le hW
  set j := prevIdx W p
  have hjn : j < W.n := prevIdx_lt W hp
  have hji : j ≠ p := prevIdx_ne W hn hp
  have hsucc : (j + 1) % W.n = p := prevIdx_succ W hp
  have hjs : j ≠ (p + 1) % W.n := prevIdx_ne_succIdx W hn hp
  have hab : W.vtx j ≠ W.vtx ((p + 1) % W.n) := simple_vtx_ne hW hjn (succIdx_lt W hp) hjs
  intro x hx
  have : x ∈ W.edge j ∩ W.edge p := by
    rwa [edge_prevIdx W hp]
  rw [simple_edge_inter hW hjn hp hji] at this
  obtain ⟨h1, h2⟩ := this
  rw [hsucc] at h1
  rcases h1 with rfl | rfl
  · rcases h2 with h2 | h2
    · exact h2
    · exact absurd h2 hab
  · rfl

/-- The corner at a vertex of a simple polygon is not a spike. -/
theorem corner_nonSpike (hW : W.Simple) {p : ℕ} (hp : p < W.n) :
    sideNonSpike (W.vtx ((p + 1) % W.n) - W.vtx p) (W.vtx (prevIdx W p) - W.vtx p) := by
  have hbv : W.vtx p ≠ W.vtx ((p + 1) % W.n) := simple_vtx_succ_ne hW hp
  rintro ⟨hcr, hdot⟩
  rw [sideCross_out] at hcr
  obtain ⟨s, hs_eq⟩ := Geometry.exists_lerp_of_det_eq_zero hbv hcr
  rw [hs_eq] at hdot
  have hsq := sqLen_pos hbv
  have hs : 0 < s := by
    unfold sideDot at hdot
    simp only [Prod.fst_sub, Prod.snd_sub, lerp_fst, lerp_snd] at hdot
    unfold sqLen at hsq
    nlinarith
  set μ := min s 1 / 2 with hμ
  have hμ0 : 0 < μ := by rw [hμ]; have := lt_min hs one_pos; linarith
  have hμ1 : μ < 1 := by rw [hμ]; have := min_le_right s 1; linarith
  have hμs : μ ≤ s := by rw [hμ]; have := min_le_left s 1; linarith
  have hy1 : lerp (W.vtx p) (W.vtx ((p + 1) % W.n)) μ ∈
      Chazelle.segment (W.vtx p) (W.vtx ((p + 1) % W.n)) := lerp_mem_segment _ _ hμ0.le hμ1.le
  have hy2 : lerp (W.vtx p) (W.vtx ((p + 1) % W.n)) μ ∈
      Chazelle.segment (W.vtx (prevIdx W p)) (W.vtx p) := by
    rw [hs_eq, Geometry.segment_comm]
    refine ⟨μ / s, div_nonneg hμ0.le hs.le, (div_le_one hs).2 hμs, ?_⟩
    apply point_ext <;> simp only [lerp_fst, lerp_snd] <;> field_simp <;> ring
  have := corner_meet hW hp ⟨hy2, hy1⟩
  exact lerp_ne_left hbv hμ0 this

/-- **Near a vertex** of a simple polygon with the interior on the left: the open left sector
of the corner is interior, the open right sector is exterior, and every point off the boundary
lies in one of them. -/
theorem vertex_local (hW : W.Simple) (hL : orient W = 1) {p : ℕ} (hp : p < W.n) :
    ∃ r > 0, ∀ x ∈ ball (W.vtx p) r,
      (sideLeftOf (W.vtx (prevIdx W p)) (W.vtx p) (W.vtx ((p + 1) % W.n)) x →
        x ∈ W.filled \ W.boundary) ∧
      (sideLeftOf (W.vtx ((p + 1) % W.n)) (W.vtx p) (W.vtx (prevIdx W p)) x → x ∉ W.filled) ∧
      (x ∉ W.boundary →
        sideLeftOf (W.vtx (prevIdx W p)) (W.vtx p) (W.vtx ((p + 1) % W.n)) x ∨
          sideLeftOf (W.vtx ((p + 1) % W.n)) (W.vtx p) (W.vtx (prevIdx W p)) x) := by
  have hn := simple_three_le hW
  set j := prevIdx W p with hj
  set a := W.vtx j with ha
  set v := W.vtx p with hv
  set b := W.vtx ((p + 1) % W.n) with hb
  have hjn : j < W.n := prevIdx_lt W hp
  have hji : j ≠ p := prevIdx_ne W hn hp
  have hsucc : (j + 1) % W.n = p := prevIdx_succ W hp
  have hav : a ≠ v := simple_vtx_ne hW hjn hp hji
  have hbv : b ≠ v := (simple_vtx_succ_ne hW hp).symm
  -- near `v` the boundary is the two edges at `v`
  have hother : ∀ k ∈ ((Finset.range W.n).erase p).erase j, v ∉ W.edge k := by
    intro k hk hmem
    simp only [Finset.mem_erase, Finset.mem_range] at hk
    rcases (simple_vtx_mem_edge_iff hW hp hk.2.2).1 hmem with h | h
    · exact hk.2.1 h
    · exact hk.1 h
  obtain ⟨r₀, hr₀, hball⟩ := exists_ball_disjoint_edges W _ hother
  have hS : ∀ x ∈ ball v r₀, x ∈ W.boundary →
      x ∈ Chazelle.segment a v ∨ x ∈ Chazelle.segment v b := by
    rintro x hx ⟨k, hk, hxk⟩
    by_cases hkp : k = p
    · subst hkp; exact Or.inr hxk
    · by_cases hkj : k = j
      · subst hkj
        left
        rwa [← edge_prevIdx W hp]
      · exfalso
        exact hball x hx k (by simp [Finset.mem_erase, Finset.mem_range, hkp, hkj, hk]) hxk
  -- radius also below the edge lengths (for the coverage)
  set r := min r₀ (min ‖b - v‖ ‖a - v‖)
  have hbv0 : 0 < ‖b - v‖ := norm_pos_iff.2 (sub_ne_zero.2 hbv)
  have hav0 : 0 < ‖a - v‖ := norm_pos_iff.2 (sub_ne_zero.2 hav)
  have hr0 : 0 < r := lt_min hr₀ (lt_min hbv0 hav0)
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hrb : r ≤ ‖b - v‖ := (min_le_right _ _).trans (min_le_left _ _)
  have hra : r ≤ ‖a - v‖ := (min_le_right _ _).trans (min_le_right _ _)
  have hSr : ∀ x ∈ ball v r, x ∈ W.boundary →
      x ∈ Chazelle.segment a v ∨ x ∈ Chazelle.segment v b :=
    fun x hx => hS x (ball_subset_ball hrr₀ hx)
  -- the left sector
  have hSL : ∀ x ∈ ball v r, x ∈ W.boundary → ¬ sideLeftOf a v b x := by
    intro x hx hxb
    rcases hSr x hx hxb with h | h
    · exact sideLeftOf_not_seg_prev hav h
    · exact sideLeftOf_not_seg_next hbv h
  have hSR : ∀ x ∈ ball v r, x ∈ W.boundary → ¬ sideLeftOf b v a x := by
    intro x hx hxb
    rcases hSr x hx hxb with h | h
    · rw [Geometry.segment_comm] at h; exact sideLeftOf_not_seg_next hav h
    · rw [Geometry.segment_comm] at h; exact sideLeftOf_not_seg_prev hbv h
  obtain ⟨hLb, hLc, hLoff⟩ := sideSector hav hbv hr0 hSL
  obtain ⟨hRb, hRc, hRoff⟩ := (sideSector hbv hav hr0 hSR).reverse
  -- a point of the left sector is interior, one of the right sector exterior
  have hs01 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with s hs; exact hs
  obtain ⟨s, ⟨hsL, hsR⟩, hs⟩ := ((hLoff.and hRoff).and hs01).exists
  obtain ⟨δ, ⟨hδL, hδR⟩, hδo⟩ := ((hsL.and hsR).and (eventually_offset_orient hW hp hs)).exists
  rw [hL, one_mul] at hδo
  rw [one_mul] at hδL
  have hLin := subset_interior hW hLc hLb hδL.2 hδo.1.1
  have e : (-1) * δ = -δ := by ring
  rw [e] at hδR
  have hRout := subset_exterior hW hRc hRb hδR.2 hδo.2
  refine ⟨r, hr0, fun x hx => ⟨fun h => hLin ⟨hx, h⟩, fun h => hRout ⟨hx, h⟩, fun hxb => ?_⟩⟩
  -- coverage
  have hxv : x ≠ v := fun h => hxb (h ▸ Existence.vtx_mem_boundary W hp)
  have hray : ∀ w : Point, w ≠ v → ‖w - v‖ ≥ r → Chazelle.segment v w ⊆ W.boundary →
      ¬ (sideCross (w - v) (x - v) = 0 ∧ 0 ≤ sideDot (w - v) (x - v)) := by
    rintro w hwv hwr hseg ⟨hc, hd⟩
    rw [sideCross_out] at hc
    obtain ⟨μ, rfl⟩ := Geometry.exists_lerp_of_det_eq_zero (Ne.symm hwv) hc
    have hsq := sqLen_pos (Ne.symm hwv)
    have hμ0 : 0 ≤ μ := by
      unfold sideDot at hd
      simp only [Prod.fst_sub, Prod.snd_sub, lerp_fst, lerp_snd] at hd
      unfold sqLen at hsq
      nlinarith
    have e : lerp v w μ - v = μ • (w - v) := by
      apply point_ext <;> simp [lerp]
    have hdist : ‖lerp v w μ - v‖ < r := by rwa [← dist_eq_norm]
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ0] at hdist
    have hμ1 : μ ≤ 1 := by
      by_contra h
      push Not at h
      have : ‖w - v‖ < μ * ‖w - v‖ := by
        have := norm_pos_iff.2 (sub_ne_zero.2 hwv); nlinarith
      linarith
    exact hxb (hseg (lerp_mem_segment _ _ hμ0 hμ1))
  have hsegb : Chazelle.segment v b ⊆ W.boundary := Existence.edge_subset_boundary W hp
  have hsega : Chazelle.segment v a ⊆ W.boundary := by
    rw [Geometry.segment_comm, ← edge_prevIdx W hp]
    exact Existence.edge_subset_boundary W hjn
  exact sideCcw_or (sub_ne_zero.2 hbv) (sub_ne_zero.2 hav) (corner_nonSpike hW hp)
    (hray b hbv (le_trans hrb le_rfl) hsegb) (hray a hav hra hsega)

/-! ## Walk positions of a simple polygon -/

/-- **A point of a simple polygon is at a single walk position.** -/
theorem pos_unique (hW : W.Simple) {p p' : ℕ} {t t' : ℝ} (hp : p < W.n) (hp' : p' < W.n)
    (ht : 0 ≤ t) (ht1 : t < 1) (ht' : 0 ≤ t') (ht1' : t' < 1)
    (h : sidePt W p t = sidePt W p' t') : p = p' ∧ t = t' := by
  have key : ∀ {p p' : ℕ} {t t' : ℝ}, p < W.n → p' < W.n → t ∈ Ioo (0 : ℝ) 1 → 0 ≤ t' →
      t' < 1 → sidePt W p t = sidePt W p' t' → p = p' ∧ t = t' := by
    intro p p' t t' hp hp' ht ht' ht1' h
    rcases ht'.lt_or_eq with ht'0 | ht'0
    · by_cases hpp : p' = p
      · subst hpp
        exact ⟨rfl, lerp_injective (simple_vtx_succ_ne hW hp) h⟩
      · have hmem : sidePt W p t ∈ W.edge p' := by
          rw [h]; exact lerp_mem_segment _ _ ht'0.le ht1'.le
        exact absurd hmem (simple_openEdge_not_mem_other hW hp ht hp' hpp)
    · subst ht'0
      rw [sidePt_zero] at h
      exact absurd h (simple_openEdge_ne_vtx hW hp ht hp')
  rcases ht.lt_or_eq with ht0 | ht0
  · exact key hp hp' ⟨ht0, ht1⟩ ht' ht1' h
  · subst ht0
    rcases ht'.lt_or_eq with ht'0 | ht'0
    · obtain ⟨h1, h2⟩ := key hp' hp ⟨ht'0, ht1'⟩ le_rfl zero_lt_one h.symm
      exact ⟨h1.symm, h2.symm⟩
    · subst ht'0
      rw [sidePt_zero, sidePt_zero] at h
      exact ⟨simple_vtx_inj hW hp hp' h, rfl⟩

/-- A point of the boundary is the point of a walk position. -/
theorem exists_pos_of_mem_boundary {q : Point} (hq : q ∈ W.boundary) :
    ∃ p < W.n, ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ sidePt W p t = q := by
  obtain ⟨i, hi, hqi⟩ := hq
  obtain ⟨τ, hτ0, hτ1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hqi
  rcases hτ1.lt_or_eq with h | h
  · exact ⟨i, hi, τ, hτ0, h, rfl⟩
  · refine ⟨(i + 1) % W.n, Nat.mod_lt _ (by omega), 0, le_rfl, one_pos, ?_⟩
    rw [sidePt_zero, h, lerp_one]

/-- **Cleanness** of every position of a simple polygon with the interior on the left. -/
theorem clean (hW : W.Simple) (hL : orient W = 1) {p : ℕ} (hp : p < W.n) {t : ℝ} (ht : 0 ≤ t)
    (ht1 : t < 1) : SideClean W (W.filled \ W.boundary) p t := by
  rcases ht.lt_or_eq with ht0 | ht0
  · obtain ⟨r, hr, hloc⟩ := edge_local hW hL hp ⟨ht0, ht1⟩
    refine ⟨r, hr, fun x hx hxD hxl => hxD ((hloc x hx).1 ?_)⟩
    rwa [sideLeft_edge (simple_vtx_succ_ne hW hp) ⟨ht0, ht1⟩] at hxl
  · subst ht0
    obtain ⟨r, hr, hloc⟩ := vertex_local hW hL hp
    refine ⟨r, hr, fun x hx hxD hxl => hxD ((hloc x (by rwa [sidePt_zero] at hx)).1 ?_)⟩
    rwa [sideLeft_zero] at hxl

/-- Near its point, the interior points are in the left sector of a position. -/
theorem interior_left (hW : W.Simple) (hL : orient W = 1) {p : ℕ} (hp : p < W.n) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) :
    ∃ r > 0, ∀ x ∈ ball (sidePt W p t) r, x ∈ W.filled \ W.boundary → sideLeft W p t x := by
  rcases ht.lt_or_eq with ht0 | ht0
  · obtain ⟨r, hr, hloc⟩ := edge_local hW hL hp ⟨ht0, ht1⟩
    refine ⟨r, hr, fun x hx hxD => ?_⟩
    rw [sideLeft_edge (simple_vtx_succ_ne hW hp) ⟨ht0, ht1⟩]
    rcases lt_trichotomy 0 (det (W.vtx p) (W.vtx ((p + 1) % W.n)) x) with h | h | h
    · exact h
    · exact absurd ((hloc x hx).2.2 h.symm) hxD.2
    · exact absurd hxD.1 ((hloc x hx).2.1 h)
  · subst ht0
    obtain ⟨r, hr, hloc⟩ := vertex_local hW hL hp
    refine ⟨r, hr, fun x hx hxD => ?_⟩
    rw [sidePt_zero] at hx
    rw [sideLeft_zero]
    rcases (hloc x hx).2.2 hxD.2 with h | h
    · exact h
    · exact absurd hxD.1 ((hloc x hx).2.1 h)

/-- The endpoint condition for a segment `[e, e']` whose open part is interior, at the boundary
point `e`. -/
theorem walkEnd (hW : W.Simple) (hL : orient W = 1) {e e' : Point} (hee : e ≠ e')
    (he : e ∈ W.boundary)
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp e e' s ∈ W.filled \ W.boundary) :
    WalkEnd W (Chazelle.segment e e') e := by
  refine ⟨?_, fun p p' t t' hp ht ht1 hp' ht' ht1' hne h1 h2 => ?_⟩
  · obtain ⟨p, hp, t, ht, ht1, hpt⟩ := exists_pos_of_mem_boundary he
    obtain ⟨r, hr, hleft⟩ := interior_left hW hL hp ht ht1
    have hd : 0 < dist e e' := dist_pos.2 hee
    refine ⟨p, t, ⟨hp, ht, ht1, by rw [hpt]; exact Geometry.left_mem_segment _ _,
      min r (dist e e'), lt_min hr hd, fun x hx hxe hxd => ?_⟩, hpt⟩
    rw [hpt] at hxe hxd
    obtain ⟨s, hs0, hs1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx
    have hs0' : 0 < s := by
      rcases hs0.lt_or_eq with h | h
      · exact h
      · exact absurd (by rw [← h, lerp_zero]) hxe
    have hs1' : s < 1 := by
      rcases hs1.lt_or_eq with h | h
      · exact h
      · exfalso
        rw [h, lerp_one, dist_comm] at hxd
        exact lt_irrefl _ (hxd.trans_le (min_le_right _ _))
    refine hleft _ ?_ (hopen s ⟨hs0', hs1'⟩)
    rw [hpt, mem_ball]; exact hxd.trans_le (min_le_left _ _)
  · exfalso
    obtain ⟨h3, h4⟩ := pos_unique hW hp hp' ht ht1 ht' ht1' (h1.trans h2.symm)
    exact hne h3 h4

/-! ## The chord system of the interior -/

/-- The closed walk `vtx (i+1), …, vtx (i+m), e₂, e₁` of a chord from `e₁` to `e₂`. -/
def chordPoly (W : Polygon) (i m : ℕ) (e₁ e₂ : Point) : Polygon :=
  ⟨(List.range m).map (fun k => W.vtx ((i + 1 + k) % W.n)) ++ [e₂, e₁]⟩

theorem chordPoly_n (W : Polygon) (i m : ℕ) (e₁ e₂ : Point) : (chordPoly W i m e₁ e₂).n = m + 2 := by
  simp [chordPoly, Polygon.n]

theorem chordPoly_vtx_lt (W : Polygon) (i : ℕ) {m : ℕ} (e₁ e₂ : Point) {k : ℕ} (hk : k < m) :
    (chordPoly W i m e₁ e₂).vtx k = W.vtx ((i + 1 + k) % W.n) := by
  simp only [chordPoly, Polygon.vtx, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simpa using hk), List.getElem?_map, List.getElem?_range hk]
  rfl

theorem chordPoly_vtx_m (W : Polygon) (i m : ℕ) (e₁ e₂ : Point) :
    (chordPoly W i m e₁ e₂).vtx m = e₂ := by
  simp [chordPoly, Polygon.vtx, List.getD_eq_getElem?_getD]

theorem chordPoly_vtx_m1 (W : Polygon) (i m : ℕ) (e₁ e₂ : Point) :
    (chordPoly W i m e₁ e₂).vtx (m + 1) = e₁ := by
  simp [chordPoly, Polygon.vtx, List.getD_eq_getElem?_getD]

theorem chordPoly_edge_lt (W : Polygon) (i : ℕ) {m : ℕ} (e₁ e₂ : Point) {k : ℕ} (hk : k + 1 < m) :
    (chordPoly W i m e₁ e₂).edge k = W.edge ((i + 1 + k) % W.n) := by
  unfold Polygon.edge
  rw [chordPoly_n, Nat.mod_eq_of_lt (by omega : k + 1 < m + 2), chordPoly_vtx_lt W i e₁ e₂ (by omega),
    chordPoly_vtx_lt W i e₁ e₂ hk, Existence.mod_add_one_mod]

theorem chordPoly_edge_pen (W : Polygon) (i : ℕ) {m : ℕ} (e₁ e₂ : Point) (hm : 0 < m) :
    (chordPoly W i m e₁ e₂).edge (m - 1) = Chazelle.segment (W.vtx ((i + m) % W.n)) e₂ := by
  unfold Polygon.edge
  rw [chordPoly_n, show m - 1 + 1 = m by omega, Nat.mod_eq_of_lt (by omega : m < m + 2),
    chordPoly_vtx_lt W i e₁ e₂ (by omega), chordPoly_vtx_m, show i + 1 + (m - 1) = i + m by omega]

theorem chordPoly_edge_m (W : Polygon) (i m : ℕ) (e₁ e₂ : Point) :
    (chordPoly W i m e₁ e₂).edge m = Chazelle.segment e₂ e₁ := by
  unfold Polygon.edge
  rw [chordPoly_n, Nat.mod_eq_of_lt (by omega : m + 1 < m + 2), chordPoly_vtx_m, chordPoly_vtx_m1]

theorem chordPoly_edge_last (W : Polygon) (i : ℕ) {m : ℕ} (e₁ e₂ : Point) (hm : 0 < m) :
    (chordPoly W i m e₁ e₂).edge (m + 1) = Chazelle.segment e₁ (W.vtx ((i + 1) % W.n)) := by
  unfold Polygon.edge
  rw [chordPoly_n, show m + 1 + 1 = m + 2 by ring, Nat.mod_self, chordPoly_vtx_m1,
    chordPoly_vtx_lt W i e₁ e₂ hm, add_zero]

/-- **The parity flip across an interior chord**: for a chord `[e₁, e₂]` of the interior with
`e₁` on edge `i`, `e₂` on edge `j`, the walk `chordPoly` has its boundary in `∂W ∪ [e₁, e₂]` and
its parity flips across every interior point of the chord. -/
theorem chord_parity_flip (hW : W.Simple) {e₁ e₂ : Point} (h12 : e₁.1 ≠ e₂.1)
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp e₁ e₂ s ∈ W.filled \ W.boundary)
    {i j : ℕ} (hi : i < W.n) (hj : j < W.n) (he₁ : e₁ ∈ W.edge i) (he₂ : e₂ ∈ W.edge j)
    {z : Point} (hz : z ∈ Chazelle.segment e₁ e₂) (hzD : z ∈ W.filled \ W.boundary) :
    ∃ Γ : Polygon, Γ.boundary ⊆ W.boundary ∪ Chazelle.segment e₁ e₂ ∧
      ∃ ε₀ > (0 : ℝ), ∀ ε, 0 < ε → ε < ε₀ →
        (z.1, z.2 + ε) ∉ Γ.boundary ∧ (z.1, z.2 - ε) ∉ Γ.boundary ∧
          parity Γ (z.1, z.2 + ε) ≠ parity Γ (z.1, z.2 - ε) := by
  have hn := simple_three_le hW
  have hij : i ≠ j := by
    rintro rfl
    have hmid := hopen (1 / 2) ⟨by norm_num, by norm_num⟩
    apply hmid.2
    exact ⟨i, hi, Geometry.segment_subset_of_convex (Geometry.segment_convex _ _) he₁ he₂
      (lerp_mem_segment _ _ (by norm_num) (by norm_num))⟩
  set m := (j + W.n - i) % W.n with hm
  have hmv : (0 < m ∧ m < W.n) ∧ (i + m) % W.n = j := by
    rcases lt_or_gt_of_ne hij with h | h
    · have e : (j + W.n - i) % W.n = j - i := by
        rw [show j + W.n - i = (j - i) + W.n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hm, e]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [show i + (j - i) = j by omega, Nat.mod_eq_of_lt hj]
    · have e : (j + W.n - i) % W.n = j + W.n - i := Nat.mod_eq_of_lt (by omega)
      rw [hm, e]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [show i + (j + W.n - i) = j + W.n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  have hm0 : 0 < m := hmv.1.1
  have hjm : (i + m) % W.n = j := hmv.2
  set Γ := chordPoly W i m e₁ e₂ with hΓ
  have hΓn : Γ.n = m + 2 := chordPoly_n W i m e₁ e₂
  -- all edges but `m` are in the boundary of `W`
  have hedge : ∀ k, k < m + 2 → k ≠ m → Γ.edge k ⊆ W.boundary := by
    intro k hk hkm
    rcases Nat.lt_or_ge (k + 1) m with h | h
    · rw [hΓ, chordPoly_edge_lt W i e₁ e₂ h]
      exact Existence.edge_subset_boundary W (Nat.mod_lt _ (by omega))
    · rcases (show k = m - 1 ∨ k = m + 1 by omega) with rfl | rfl
      · rw [hΓ, chordPoly_edge_pen W i e₁ e₂ hm0, hjm]
        exact (Geometry.segment_subset_of_convex (Geometry.segment_convex _ _)
          (Geometry.left_mem_segment _ _) he₂).trans (Existence.edge_subset_boundary W hj)
      · rw [hΓ, chordPoly_edge_last W i e₁ e₂ hm0]
        exact (Geometry.segment_subset_of_convex (Geometry.segment_convex _ _) he₁
          (Geometry.right_mem_segment _ _)).trans (Existence.edge_subset_boundary W hi)
  refine ⟨Γ, ?_, ?_⟩
  · rintro x ⟨k, hk, hxk⟩
    rw [hΓn] at hk
    by_cases hkm : k = m
    · subst hkm
      right
      rwa [hΓ, chordPoly_edge_m, Geometry.segment_comm] at hxk
    · exact Or.inl (hedge k hk hkm hxk)
  · have hmn : m < Γ.n := by rw [hΓn]; omega
    have hsucc : (m + 1) % Γ.n = m + 1 := by rw [hΓn]; exact Nat.mod_eq_of_lt (by omega)
    have hzΓ : z ∈ Γ.edge m := by
      rwa [hΓ, chordPoly_edge_m, Geometry.segment_comm]
    have hne : (Γ.vtx m).1 ≠ (Γ.vtx ((m + 1) % Γ.n)).1 := by
      rw [hsucc, hΓ, chordPoly_vtx_m, chordPoly_vtx_m1]; exact Ne.symm h12
    have hzu : z ≠ Γ.vtx m := by
      rw [hΓ, chordPoly_vtx_m]
      rintro rfl
      exact hzD.2 (Existence.edge_subset_boundary W hj he₂)
    have hzv : z ≠ Γ.vtx ((m + 1) % Γ.n) := by
      rw [hsucc, hΓ, chordPoly_vtx_m1]
      rintro rfl
      exact hzD.2 (Existence.edge_subset_boundary W hi he₁)
    have hother : ∀ k, k < Γ.n → k ≠ m → z ∉ Γ.edge k := by
      intro k hk hkm hzk
      rw [hΓn] at hk
      exact hzD.2 (hedge k hk hkm hzk)
    exact parity_flip Γ hmn hzΓ hne hzu hzv hother

/-- The endpoints of a horizontal chord of the interior are on the boundary. -/
theorem hchord_end_mem_boundary {y a b : ℝ}
    (h : IsHChordIn (W.filled \ W.boundary) y a b) :
    ((a, y) : Point) ∈ W.boundary ∧ ((b, y) : Point) ∈ W.boundary := by
  have key : ∀ x : ℝ, ((x, y) : Point) ∉ W.filled \ W.boundary →
      (∀ ε > (0 : ℝ), ∃ x', |x' - x| < ε ∧ ((x', y) : Point) ∈ W.filled \ W.boundary) →
      ((x, y) : Point) ∈ W.boundary := by
    intro x hx happ
    by_contra hb
    have hnf : ((x, y) : Point) ∉ W.filled := fun hf => hx ⟨hf, hb⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isClosed_filled W).isOpen_compl _ hnf
    obtain ⟨x', hx', hx'D⟩ := happ r hr
    apply hball (show ((x', y) : Point) ∈ ball ((x, y) : Point) r by
      rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      simp only [sub_self, abs_zero]
      exact max_lt hx' hr)
    exact hx'D.1
  have hlt := h.lt
  refine ⟨key a h.left_not fun ε hε => ?_, key b h.right_not fun ε hε => ?_⟩
  · refine ⟨a + min ε (b - a) / 2, ?_, h.open_mem _ ?_ ?_⟩
    · rw [add_sub_cancel_left, abs_of_pos (by have := lt_min hε (sub_pos.2 hlt); linarith)]
      have := min_le_left ε (b - a); linarith
    · have := lt_min hε (sub_pos.2 hlt); linarith
    · have := min_le_right ε (b - a); linarith
  · refine ⟨b - min ε (b - a) / 2, ?_, h.open_mem _ ?_ ?_⟩
    · rw [show b - min ε (b - a) / 2 - b = -(min ε (b - a) / 2) by ring, abs_neg,
        abs_of_pos (by have := lt_min hε (sub_pos.2 hlt); linarith)]
      have := min_le_left ε (b - a); linarith
    · have := min_le_right ε (b - a); linarith
    · have := lt_min hε (sub_pos.2 hlt); linarith

/-- The open part of `[(a, y), (b, y)]` of a horizontal chord. -/
theorem hchord_open {D : Set Point} {y a b : ℝ} (h : IsHChordIn D y a b) :
    ∀ s ∈ Ioo (0 : ℝ) 1, lerp ((a, y) : Point) (b, y) s ∈ D := by
  intro s hs
  have e : lerp ((a, y) : Point) (b, y) s = ((a + s * (b - a), y) : Point) := by
    apply point_ext <;> simp [lerp]
  rw [e]
  exact h.open_mem _ (by nlinarith [h.lt, hs.1]) (by nlinarith [h.lt, hs.2])

/-- **Every finite family of horizontal chords of the interior is a chord system.** -/
theorem chordSystem (hW : W.Simple) {F : Set (Set Point)} (hfin : F.Finite)
    (hF : ∀ c ∈ F, ∃ y a b : ℝ, IsHChordIn (W.filled \ W.boundary) y a b ∧ c = hseg y a b) :
    ChordSystem (W.filled \ W.boundary) F where
  isOpen := isOpen_filled_sdiff_boundary hW
  finite := hfin
  hchord := hF
  walk := by
    intro c hc z hz hzD
    obtain ⟨y, a, b, h, rfl⟩ := hF c hc
    rw [FactsChain.hseg_eq_segment h.lt.le] at hz ⊢
    obtain ⟨ha, hb⟩ := hchord_end_mem_boundary h
    obtain ⟨i, hi, hai⟩ := ha
    obtain ⟨j, hj, hbj⟩ := hb
    obtain ⟨Γ, hΓ, hflip⟩ := chord_parity_flip hW (by simp only; exact h.lt.ne) (hchord_open h)
      hi hj hai hbj hz hzD
    refine ⟨Γ, hΓ.trans ?_, hflip⟩
    rintro x (hx | hx)
    · exact Or.inl fun hxD => hxD.2 hx
    · exact Or.inr hx

/-! ## Reach -/

/-- **Reach for a simple polygon with the interior on the left.** -/
theorem reach (hW : W.Simple) (hL : orient W = 1) {z : Point} (hz : z ∈ W.filled \ W.boundary)
    (hzv : ∀ i < W.n, z.2 ≠ (W.vtx i).2) :
    ∃ s > (0 : ℝ), (∀ s' ∈ Ico (0 : ℝ) s, ((z.1 + s', z.2) : Point) ∈ W.filled \ W.boundary) ∧
      ∃ p < W.n, ∃ t ∈ Ioo (0 : ℝ) 1, sidePt W p t = ((z.1 + s, z.2) : Point) ∧
        (W.vtx p).2 < (W.vtx ((p + 1) % W.n)).2 := by
  obtain ⟨s, hs, hseg, hq⟩ := exists_first_exit (isOpen_filled_sdiff_boundary hW) hz
    (R := coordBound W + 1) (fun x hx => by
      have := (abs_le.1 (filled_subset_square W hx.1).1).2; linarith)
  refine ⟨s, hs, hseg, ?_⟩
  set q : Point := (z.1 + s, z.2) with hqdef
  -- the exit point is filled, hence on the boundary
  have hqf : q ∈ W.filled := by
    by_contra hnf
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isClosed_filled W).isOpen_compl _ hnf
    set ε := min r s / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; have := lt_min hr hs; linarith
    have hεr : ε < r := by rw [hε]; have := min_le_left r s; linarith
    have hεs : ε < s := by rw [hε]; have := min_le_right r s; linarith
    apply hball (show ((z.1 + (s - ε), z.2) : Point) ∈ ball q r by
      rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      simp only [hqdef, sub_self, abs_zero]
      rw [show z.1 + (s - ε) - (z.1 + s) = -ε by ring, abs_neg, abs_of_pos hε0]
      exact max_lt hεr hr)
    exact (hseg (s - ε) ⟨by linarith, by linarith⟩).1
  have hqb : q ∈ W.boundary := by
    by_contra hb; exact hq ⟨hqf, hb⟩
  have hqv : ∀ j, j < W.n → q ≠ W.vtx j := fun j hj h => hzv j hj (by rw [← h])
  obtain ⟨p, hp, t, ht, hqe⟩ := exists_openEdge_of_mem_boundary W hqb hqv
  refine ⟨p, hp, t, ht, hqe.symm, ?_⟩
  set u := W.vtx p
  set v := W.vtx ((p + 1) % W.n)
  have hq2 : z.2 = u.2 + t * (v.2 - u.2) := by
    have := congrArg Prod.snd hqe; simp only [hqdef, lerp_snd] at this; exact this
  rcases lt_trichotomy u.2 v.2 with h | h | h
  · exact h
  · exfalso; apply hzv p hp; rw [hq2, h]; ring
  · exfalso
    obtain ⟨r, hr, hloc⟩ := edge_local hW hL hp ht
    set ε := min r s / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; have := lt_min hr hs; linarith
    have hεr : ε < r := by rw [hε]; have := min_le_left r s; linarith
    have hεs : ε < s := by rw [hε]; have := min_le_right r s; linarith
    have hx : ((z.1 + (s - ε), z.2) : Point) ∈ ball (sidePt W p t) r := by
      rw [show sidePt W p t = q from hqe.symm, mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      simp only [hqdef, sub_self, abs_zero]
      rw [show z.1 + (s - ε) - (z.1 + s) = -ε by ring, abs_neg, abs_of_pos hε0]
      exact max_lt hεr hr
    have hq0 : det u v q = 0 := by rw [hqe]; exact Geometry.det_lerp_self _ _ _
    have hdet : det u v ((z.1 + (s - ε), z.2) : Point) < 0 := by
      have e : det u v ((z.1 + (s - ε), z.2) : Point) = det u v q + ε * (v.2 - u.2) := by
        simp only [hqdef, det]; ring
      rw [e, hq0]; nlinarith
    exact (hloc _ hx).2.1 hdet (hseg (s - ε) ⟨by linarith, by linarith⟩).1

/-! ## The interior walk -/

/-- The reversed polygon. -/
theorem rev_n (Q : Polygon) : (⟨Q.vertices.reverse⟩ : Polygon).n = Q.n := by
  simp [Polygon.n]

theorem rev_vtx (Q : Polygon) : ∀ k < Q.n, (⟨Q.vertices.reverse⟩ : Polygon).vtx k =
    Q.vtx (Q.n - 1 - k) := by
  intro k hk
  have hk' : k < Q.vertices.reverse.length := by rwa [List.length_reverse]
  have hk2 : Q.n - 1 - k < Q.vertices.length := by
    have : Q.n = Q.vertices.length := rfl
    omega
  simp only [Polygon.vtx, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem hk', List.getElem_reverse, List.getElem?_eq_getElem hk2]
  rfl

/-- **The interior walk** of a simple polygon is a simple polygon with the same boundary and
filled region, with the interior on its left. -/
theorem interiorWalk_spec {Q : Polygon} (hQ : Q.Simple) :
    (interiorWalk Q).Simple ∧ (interiorWalk Q).boundary = Q.boundary ∧
      (interiorWalk Q).filled = Q.filled ∧ orient (interiorWalk Q) = 1 := by
  classical
  unfold interiorWalk
  split_ifs with h
  · refine ⟨hQ, rfl, rfl, ?_⟩
    unfold orient; simp [h]
  · set R : Polygon := ⟨Q.vertices.reverse⟩
    have hn := rev_n Q
    have hv := rev_vtx Q
    have hRs : R.Simple := Mountain.rev_simple hn hv hQ
    have hRf : R.filled = Q.filled := Mountain.rev_filled hn hv
    refine ⟨hRs, Mountain.rev_boundary hn hv, hRf, ?_⟩
    have hn3 := simple_three_le hQ
    have hQo : orient Q = -1 := by unfold orient; simp [h]
    obtain ⟨e1, e2⟩ := Mountain.rev_endpoints hn hv (k := 0) (by omega)
    apply Mountain.orient_eq_of_eventually hRs (i := 0) (by rw [hn]; omega)
      (t := 1 / 2) ⟨by norm_num, by norm_num⟩ (Or.inl rfl)
    set e := Mountain.revEdge Q.n 0
    have hel : e < Q.n := Mountain.revEdge_lt (by omega)
    filter_upwards [eventually_offset_orient hQ hel (t := 1 / 2) ⟨by norm_num, by norm_num⟩]
      with δ hδ
    rw [hRf, e1, e2, one_mul, offset_reverse, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    rw [hQo, neg_one_mul] at hδ
    exact hδ.1.1

/-- **Walk axioms from a simple polygon** with the interior on its left. -/
theorem walkAx_of_simple (hW : W.Simple) (hL : orient W = 1) (M : Model)
    (hMW : M.W = W) (hD : M.D = W.filled \ W.boundary)
    (hAdm : M.Adm = {c | ∃ y a b : ℝ, IsHChordIn M.D y a b ∧ c = hseg y a b}) : WalkAx M := by
  obtain ⟨D, W', counted, Adm, Full⟩ := M
  simp only at hMW hD hAdm
  subst hMW hD hAdm
  exact {
    isOpen := isOpen_filled_sdiff_boundary hW
    preconn := filled_sdiff_boundary_connected hW
    nonempty := filled_sdiff_boundary_nonempty hW
    nd := fun p hp => simple_vtx_succ_ne hW hp
    trace := fun p hp t ht ht1 hD =>
      hD.2 (Existence.edge_subset_boundary _ hp (lerp_mem_segment _ _ ht ht1))
    clean := fun p hp t ht ht1 => clean hW hL hp ht ht1
    sys := fun F hF hfin => chordSystem hW hfin fun c hc => hF hc
    ends := by
      intro c hc
      obtain ⟨y, a, b, h, rfl⟩ := hc
      obtain ⟨ha, hb⟩ := hchord_end_mem_boundary h
      have hopen := hchord_open h
      have hab : ((a, y) : Point) ≠ (b, y) := fun e => h.lt.ne (congrArg Prod.fst e)
      have hseg := FactsChain.hseg_eq_segment (y := y) h.lt.le
      refine ⟨(a, y), (b, y), hab, hseg, rfl, hopen, ?_, ?_⟩
      · rw [hseg]; exact walkEnd hW hL hab ha hopen
      · rw [hseg, Geometry.segment_comm]
        exact walkEnd hW hL hab.symm hb (WalkAx.open_rev hopen)
    reach := fun z hz hzv => reach hW hL hz hzv }

end FactsInterior

/-- **The interior model of a simple polygon satisfies the walk axioms.** -/
theorem walkAx_interiorModel {Q : Polygon} (hQ : Q.Simple) : WalkAx (interiorModel Q) := by
  obtain ⟨hs, hb, hf, ho⟩ := FactsInterior.interiorWalk_spec hQ
  exact FactsInterior.walkAx_of_simple hs ho (interiorModel Q) rfl (by
    show Q.filled \ Q.boundary = _; rw [hb, hf]) rfl

/-- **The chain model of a chain of a simple polygon satisfies the walk axioms.** -/
theorem walkAx_chainModel {C : Chain} (hP : C.P.Simple) : WalkAx (chainModel C) :=
  FactsChain.walkAx C hP

/-- **Every good model satisfies the walk axioms.** -/
theorem walkAx_of_goodModel {M : Model} (h : GoodModel M) : WalkAx M := by
  rcases h with ⟨C, hC, rfl⟩ | ⟨Q, hQ, rfl⟩
  · exact walkAx_chainModel hC
  · exact walkAx_interiorModel hQ

end

end Chazelle.Core
