module

public import Chazelle.MacT
public import Chazelle.Jordan.SegmentFacts
public import Chazelle.Core.ClusterEulerRam
public import Mathlib.Data.List.Rotate
public import Chazelle.Spec
public import Mathlib.Tactic.Linarith

section
set_option hygiene false
local macro "zqbbi" : tactic => `(tactic| (have hz1 := bary₁_vtx_pos hP hdet hk by_omega by_omega hkΔ
                                           have hz3 := bary₃_vtx_pos hP hdet hk by_omega by_omega hkΔ))
local macro "zqbbj" : tactic => `(tactic| have hn := simple_three_le hP)
local macro "zqbbk" : tactic => `(tactic| have hsucc : ztg % P.n = i + 1 := Nat.mod_eq_of_lt by_omega)
local macro "zqbbl" : tactic => `(tactic| have h0 : ztbof := by_omega)
local macro "zqbbm" : tactic => `(tactic| rw [n_rotate, vtx_rotate P m zthbr, Nat.add_mod_mod, Nat.add_assoc])
set_option hygiene true

/-!
# Existence of an interior diagonal

Every simple polygon with at least four vertices has a diagonal (`IsDiagonal`, from
`Chazelle.Existence.Arc`) whose chord lies in the filled region (`exists_diagonal`).

The argument (after rotating so that vertex `0` is lexicographically smallest, see
`Chazelle.Existence.Convex`): let `u = vtx (n-1)`, `v = vtx 0`, `w = vtx 1` and
`Δ = convexHull {u, v, w}`; the corner at `v` is strictly convex and the open sector at `v` is
interior.  Write `β = bary₂ u v w` for the barycentric weight at `v`.

* **No crossing** (`bary₂_le_of_mem_edge`): if every vertex of `P` in `Δ` other than `v` has
  `β ≤ c`, then every point of a non-incident edge lying in `Δ` has `β ≤ c`.  (Otherwise the
  edge, whose endpoints are below the level or outside `Δ`, would leave the cap `{β > c} ∩ Δ`
  through a side `u v` or `v w` at a point that is not `u`, `v` or `w`, contradicting
  simplicity; the exit point is found with the intermediate value theorem,
  `exists_zero_of_affine_pair`.)
* If no vertex other than `u, v, w` lies in `Δ`, the chord `w u` is an interior diagonal
  (`chord_base_not_mem_boundary`); otherwise the chord from `v` to a vertex of `Δ` maximising
  `β` is (`chord_apex_not_mem_boundary`).
* The open chord avoids the boundary and is connected, and it is joined to the interior sector
  at `v` (directly, or through the open triangle), so the whole chord lies in `P.filled`
  (`segment_subset_filled_of_open`).
* `isDiagonal_rotate` transfers the conclusion back through the rotation.
-/
namespace Chazelle.Existence
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Jordan
open Chazelle.Programs (lexLE)
open Chazelle.Geometry (lerp lerp_fst lerp_snd det_lerp det_cyclic det_cyclic_right det_swap12
  det_swap13 det_swap23 det_self_left det_self_right det_self_outer exists_lerp_of_det_eq_zero
  det_eq_zero_of_mem_segment lerp_zero lerp_one lerp_injective lerp_mem_segment point_ext
  point_ext_iff mem_segment_iff_lerp ne_of_det_ne_zero continuous_lerp segment_subset_of_convex
  segment_convex convex_triangle vertex_mem_triangle_left vertex_mem_triangle_mid
  vertex_mem_triangle_right bary₁ bary₂ bary₃ bary₁_lerp bary₂_lerp bary₃_lerp
  mem_triangle_iff_bary bary_sum mem_segment_of_bary₁_eq_zero mem_segment_of_bary₃_eq_zero
  bary₁_eq_zero_of_mem_segment bary₃_eq_zero_of_mem_segment bary₁_vertex_left bary₁_vertex_mid
  bary₁_vertex_right bary₂_vertex_left bary₂_vertex_mid bary₂_vertex_right bary₃_vertex_left
  bary₃_vertex_mid bary₃_vertex_right)

/-! ### Affine functions along a segment -/
variable (a b : Point) {u v w : Point} {P : Polygon}
/-- Composition of `lerp` along one line. -/
theorem lerp_lerp (s₁ s₂ τ : ℝ) :
    lerp ztrte ztrtf τ = lerp a b (ztcsf * s₁ + τ * s₂) := by
  zucco

/-- A point of a line lying (in parameter) between two points of the line is in their segment. -/
theorem lerp_mem_segment_lerp {s₁ s₂ s : ℝ} (h1 : s₁ ≤ s) (h2 : s ≤ s₂) :
    lerp a b s ∈ Chazelle.segment ztrte ztrtf := by
  zukkp
  · have hd : 0 < s₂ - s₁ := by_linarith
    refine mem_segment_iff_lerp.2 ⟨(s - s₁) / (s₂ - s₁), div_nonneg by_linarith hd.le,
      (div_le_one hd).2 by_linarith, ?_⟩
    zunts
    grind
  · zuitq

/-- **Exit point.**  Two affine functions on `[0,1]`, both nonnegative at `0` and at least one
of them negative at `1`, have a common point of `[0,1]` where both are nonnegative and one of
them vanishes. -/
theorem exists_zero_of_affine_pair {α γ : ℝ → ℝ}
    (hα : ∀ t, α t = ztca * α 0 + t * α 1) (hγ : ∀ t, γ t = ztca * γ 0 + t * γ 1)
    (h0 : 0 ≤ α 0) (h0' : 0 ≤ γ 0) (h1 : α 1 < 0 ∨ γ 1 < 0) :
    ∃ t, 0 ≤ t ∧ t ≤ 1 ∧ 0 ≤ α t ∧ 0 ≤ γ t ∧ (α t = 0 ∨ γ t = 0) := by
  have hαc : Continuous α := by
    have  := funext hα
    zukyw
  have hγc : Continuous γ := by
    have  := funext hγ
    zukyw
  have hm : Continuous fun t => min _ _ := hαc.min hγc
  have hmem : (0 : ℝ) ∈ Icc (min (α 1) (γ 1)) (min (α 0) (γ 0)) := by
    grind
  obtain ⟨t, ⟨ht0, ht1⟩, ht⟩ := intermediate_value_Icc' zero_le_one hm.continuousOn hmem
  zumpt
  refine ⟨t, ht0, ht1, by_grind, by_grind, ?_⟩
  grind

/-! ### Leaving a cap of a triangle through a side -/

/-- **Side point.**  Let `p` be a point of the segment `a b` lying in the triangle `u v w` with
`bary₂ p > c ≥ 0`, and let the endpoint `b` have `bary₂ b ≥ bary₂ p`, while `bary₂ b ≤ c`
whenever `b` is in the triangle.  Then between `p` and `b` there is a point of the triangle
with `bary₂ > c` on the side `v w` (`bary₁ = 0`) or on the side `u v` (`bary₃ = 0`). -/
theorem exists_side_point (hdet : det u v w ≠ 0) {c : ℝ} (hc : 0 ≤ c)
    {a b p : Point} (hp : p ∈ Chazelle.segment a b)
    (hpΔ : p ∈ convexHull ℝ ({u, v, w} : Set Point)) (hpc : c < bary₂ u v w p)
    (hb : bary₂ u v w p ≤ bary₂ u v w b)
    (hbΔ : b ∈ convexHull ℝ ({u, v, w} : Set Point) → bary₂ u v w b ≤ c) :
    ∃ y ∈ Chazelle.segment a b, y ∈ convexHull ℝ ({u, v, w} : Set Point) ∧
      c < bary₂ u v w y ∧ (bary₁ u v w y = 0 ∨ bary₃ u v w y = 0) := by
  have hbΔ' : b ∉ convexHull ℝ ({u, v, w} : Set Point) := by_grind
  have hbneg : ztidt := by
    zubqk
    zugwq
    exact hbΔ' ztosy
  obtain ⟨hp1, -, hp3⟩ := (mem_triangle_iff_bary hdet).1 hpΔ
  obtain ⟨t, ht0, ht1, hαt, hγt, hzero⟩ := exists_zero_of_affine_pair
    (α := fun t => bary₁ u v w ztrtj) (γ := fun t => bary₃ u v w ztrtj)
    ztikk
    ztikl
    by_simp_all by_simp_all by_simp_all
  refine ⟨lerp p b t, ?_, ?_, ?_, hzero⟩
  · exact segment_subset_of_convex (segment_convex a b) hp (right_mem_segment a b)
      (lerp_mem_segment p b ht0 ht1)
  · zujeu
    zumly
    nlinarith [mul_nonneg ztmor (by linarith : 0 ≤ bary₂ u v w p),
      mul_nonneg ht0 (by linarith : 0 ≤ bary₂ u v w b)]
  · zumly
    nlinarith [mul_nonneg ht0 ztwfo]

/-- **No transversal crossing of the base.**  Let `E` be a set (an edge) whose points in the
triangle `u v w` all have `bary₂ ≤ 0`, containing the segment from `q` to `b`, where `q` is a
point of the open base `u w` (`bary₁ q, bary₃ q > 0`, `bary₂ q = 0`) and `b` is outside the
triangle with `bary₂ b > 0`.  This is impossible. -/
theorem no_transversal (hdet : det u v w ≠ 0) {E : Set Point}
    (hE : ∀ p ∈ E, p ∈ convexHull ℝ ({u, v, w} : Set Point) → bary₂ u v w p ≤ 0)
    {q b : Point} (hqb : Chazelle.segment q b ⊆ E)
    (hq1 : 0 < bary₁ u v w q) (hq3 : 0 < bary₃ u v w q) (hq2 : bary₂ u v w q = 0)
    (hb : 0 < bary₂ u v w b) (hbΔ : b ∉ convexHull ℝ ({u, v, w} : Set Point)) : False := by
  have hbneg : ztidt := by
    zubqk
    zugwq
    exact hbΔ ztosy
  obtain ⟨t, ht0, ht1, hαt, hγt, hzero⟩ := exists_zero_of_affine_pair
    (α := fun t => bary₁ u v w ztrtk) (γ := fun t => bary₃ u v w ztrtk)
    ztikk
    ztikl
    (by simpa using hq1.le) (by simpa using hq3.le) by_simp_all
  have ht0' : ztfkp := by
    zubbd
    · zubh
    · zubst
      rw [lerp_zero] at hzero
      grind
  have hy := hqb (lerp_mem_segment q b ht0 ht1)
  have hyΔ : lerp q b t ∈ convexHull ℝ ({u, v, w} : Set Point) := by
    zujeu
    rw [bary₂_lerp, hq2]
    positivity
  have := hE _ hy hyΔ
  rw [bary₂_lerp, hq2] at this
  nlinarith [mul_pos ht0' hb]

/-- In the open convex sector at `v`: a point with positive first and third barycentric
coordinates with respect to `u v w` satisfies `0 < σ * det u v x` and `0 < σ * det v w x`
whenever `0 < σ * det u v w`. -/
theorem sector_of_bary_pos {σ : ℝ} (hpos : 0 < σ * det u v w) {x : Point}
    (hx1 : 0 < bary₁ u v w x) (hx3 : 0 < bary₃ u v w x) :
    0 < σ * det u v x ∧ 0 < σ * det v w x := by
  have hdet : ztrgp := fun h => by_simp_all
  constructor
  · have : det u v x = bary₃ u v w x * det u v w := by
      zumrv
    zujln

  · have : det v w x = bary₁ u v w x * det u v w := by
      unfold bary₁; rw [div_mul_cancel₀ _ hdet, det_cyclic x v w]
    zujln

/-! ### Edges of a simple polygon and the fan triangle at vertex `0`

Throughout, `u = P.vtx (P.n - 1)`, `v = P.vtx 0`, `w = P.vtx 1`, and the triangle is
`convexHull ℝ {u, v, w}`. -/

/-- A point of an edge not incident to vertex `0` that lies on one of the two edges at vertex
`0` is the far endpoint of that edge. -/
theorem eq_of_mem_edge_of_mem_side {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n)
    (hi0 : i ≠ 0) (hin : i ≠ P.n - 1) {y : Point} (hy : y ∈ P.edge i)
    (hside : y ∈ Chazelle.segment ztdt ztgk ∨
      y ∈ Chazelle.segment ztwjc ztdt) :
    y = P.vtx 1 ∨ y = P.vtx ztch := by
  zqbbj
  zqbbl
  have hv : P.vtx 0 ∉ P.edge i := by
    zuq
    rcases (simple_vtx_mem_edge_iff hP h0 hi).1 h with h | h
    · omega
    · rw [prevIdx_zero P h0] at h; omega
  rcases hside with h | h
  · rw [← edge_zero P by_omega] at h
    rcases simple_endpoint_of_mem_two hP h0 hi (Ne.symm hi0) h hy with h' | h'
    · simp_all
    · rw [succ_zero_mod P by_omega] at h'; simp_all
  · rw [← edge_last P h0] at h
    rcases simple_endpoint_of_mem_two hP by_omega hi (Ne.symm hin) h hy with h' | h'
    · simp_all
    · rw [succ_last_mod P h0] at h'; simp_all

/-- **No crossing.**  Let `c ≥ 0` and suppose every vertex of `P` in the fan triangle
`u v w`, other than `v`, has `bary₂ ≤ c`.  Then every point of an edge not incident to `v`
that lies in the triangle has `bary₂ ≤ c`. -/
theorem bary₂_le_of_mem_edge {P : Polygon} (hP : P.Simple)
    (hdet : det ztwjc ztdt ztgk ≠ 0) {c : ℝ} (hc : 0 ≤ c)
    (hvert : ∀ j, j < P.n → j ≠ 0 →
      P.vtx j ∈ convexHull ℝ ({P.vtx ztch, P.vtx 0, P.vtx 1} : Set Point) →
        bary₂ ztwjc ztdt ztgk ztbhp ≤ c)
    {i : ℕ} (hi : i < P.n) (hi0 : i ≠ 0) (hin : i ≠ P.n - 1) {p : Point} (hp : p ∈ P.edge i)
    (hpΔ : p ∈ convexHull ℝ ({P.vtx ztch, P.vtx 0, P.vtx 1} : Set Point)) :
    bary₂ ztwjc ztdt ztgk p ≤ c := by
  zqbbj
  zulwe
  rw [not_le] at hlt
  zqbbk
  have haΔ := hvert i hi hi0
  have hbΔ := hvert ztwjy by_omega by_omega
  have hpab : p ∈ Chazelle.segment _ _ := hp
  have key : ∃ y ∈ Chazelle.segment ztdn ztwir,
      y ∈ convexHull ℝ ({P.vtx ztch, P.vtx 0, P.vtx 1} : Set Point) ∧
        c < bary₂ ztwjc ztdt ztgk y ∧
        (bary₁ ztwjc ztdt ztgk y = 0 ∨
          bary₃ ztwjc ztdt ztgk y = 0) := by
    obtain ⟨t, ht0, ht1, hpt⟩ := mem_segment_iff_lerp.1 hpab
    rcases le_or_gt (bary₂ ztwjc ztdt ztgk ztdn)
      (bary₂ ztwjc ztdt ztgk ztwir) with hab | hab
    · refine exists_side_point hdet hc hpab hpΔ hlt ?_ hbΔ
      zukvp
      nlinarith [mul_le_mul_of_nonneg_left hab ztmor]
    · have hpa : bary₂ ztwjc ztdt ztgk p ≤
          bary₂ ztwjc ztdt ztgk ztdn := by
        zukvp
        nlinarith [mul_le_mul_of_nonneg_left hab.le ht0]
      obtain ⟨y, hy, hyΔ, hyc, hyz⟩ := exists_side_point hdet hc
        (by zvnln; exact hpab) hpΔ hlt hpa haΔ
      exact ⟨y, by zvnln; exact hy, hyΔ, hyc, hyz⟩
  obtain ⟨y, hy, hyΔ, hyc, hyz⟩ := key
  have hside : y ∈ Chazelle.segment ztdt ztgk ∨
      y ∈ Chazelle.segment ztwjc ztdt := by
    rcases hyz with h | h
    · exact Or.inl (mem_segment_of_bary₁_eq_zero hdet hyΔ h)
    · exact Or.inr (mem_segment_of_bary₃_eq_zero hdet hyΔ h)
  rcases eq_of_mem_edge_of_mem_side hP hi hi0 hin hy hside with h | h
  · grind
  grind

/-- A vertex of `P` in the fan triangle, other than vertices `0` and `1`, is off the edge
`v w`: its first barycentric coordinate is positive. -/
theorem bary₁_vtx_pos {P : Polygon} (hP : P.Simple)
    (hdet : det ztwjc ztdt ztgk ≠ 0) {k : ℕ} (hk : k < P.n)
    (hk0 : k ≠ 0) (hk1 : k ≠ 1)
    (hkΔ : P.vtx k ∈ convexHull ℝ ({P.vtx ztch, P.vtx 0, P.vtx 1} : Set Point)) :
    0 < bary₁ ztwjc ztdt ztgk ztjr := by
  zqbbj
  obtain ⟨h1, -, -⟩ := (mem_triangle_iff_bary hdet).1 hkΔ
  refine lt_of_le_of_ne h1 fun h => ?_
  have hmem := mem_segment_of_bary₁_eq_zero hdet hkΔ h.symm
  rw [← edge_zero P by_omega] at hmem
  zugrn
  · exact hk0 ztgmd
  · rw [succ_zero_mod P by_omega] at h'
    exact hk1 ztgmd

/-- A vertex of `P` in the fan triangle, other than vertices `0` and `n - 1`, is off the edge
`u v`: its third barycentric coordinate is positive. -/
theorem bary₃_vtx_pos {P : Polygon} (hP : P.Simple)
    (hdet : det ztwjc ztdt ztgk ≠ 0) {k : ℕ} (hk : k < P.n)
    (hk0 : k ≠ 0) (hkn : k ≠ P.n - 1)
    (hkΔ : P.vtx k ∈ convexHull ℝ ({P.vtx ztch, P.vtx 0, P.vtx 1} : Set Point)) :
    0 < bary₃ ztwjc ztdt ztgk ztjr := by
  zqbbj
  obtain ⟨-, -, h3⟩ := (mem_triangle_iff_bary hdet).1 hkΔ
  refine lt_of_le_of_ne h3 fun h => ?_
  have hmem := mem_segment_of_bary₃_eq_zero hdet hkΔ h.symm
  rw [← edge_last P by_omega] at hmem
  zugrn
  · exact hkn ztgmd
  · rw [succ_last_mod P by_omega] at h'
    exact hk0 ztgmd

/-- Under the no-crossing hypothesis with level `0`, the open fan triangle avoids the
boundary. -/
theorem interior_fan_not_mem_boundary {P : Polygon} (hP : P.Simple)
    (hdet : det ztwjc ztdt ztgk ≠ 0)
    (hvert : ∀ j, j < P.n → j ≠ 0 →
      P.vtx j ∈ convexHull ℝ ({P.vtx ztch, P.vtx 0, P.vtx 1} : Set Point) →
        bary₂ ztwjc ztdt ztgk ztbhp ≤ 0)
    {x : Point} (hx1 : 0 < bary₁ ztwjc ztdt ztgk x)
    (hx2 : 0 < bary₂ ztwjc ztdt ztgk x)
    (hx3 : 0 < bary₃ ztwjc ztdt ztgk x) : x ∉ P.boundary := by
  zqbbj
  rintro ⟨i, hi, hxi⟩
  have hxΔ : x ∈ convexHull ℝ ({P.vtx _, P.vtx 0, P.vtx 1} : Set Point) :=
    (mem_triangle_iff_bary hdet).2 by_grind
  zuclc
  · zufpy
    rw [edge_zero P by_omega] at hxi
    have := bary₁_eq_zero_of_mem_segment (a := P.vtx ztch) hxi
    linarith
  zudwx
  · subst hin
    rw [edge_last P by_omega] at hxi
    have := bary₃_eq_zero_of_mem_segment (c := P.vtx 1) hxi
    linarith
  have := bary₂_le_of_mem_edge hP hdet le_rfl hvert hi hi0 hin hxi hxΔ
  linarith

/-! ### The two candidate chords avoid the boundary -/

/-- **The chord to a maximal vertex avoids the boundary.**  Let `vtx k` (`2 ≤ k ≤ n - 2`) be
a vertex in the fan triangle maximising `bary₂` among the vertices of the triangle other than
`v`.  Then the open chord from `v` to `vtx k` avoids the boundary. -/
theorem chord_apex_not_mem_boundary {P : Polygon} (hP : P.Simple)
    (hdet : det ztwjc ztdt ztgk ≠ 0) {k : ℕ} (hk : k < P.n)
    (hk2 : 2 ≤ k) (hkn : k + 2 ≤ P.n)
    (hkΔ : P.vtx k ∈ convexHull ℝ ({P.vtx ztch, P.vtx 0, P.vtx 1} : Set Point))
    (hmax : ∀ j, j < P.n → j ≠ 0 →
      P.vtx j ∈ convexHull ℝ ({P.vtx ztch, P.vtx 0, P.vtx 1} : Set Point) →
        bary₂ ztwjc ztdt ztgk ztbhp ≤
          bary₂ ztwjc ztdt ztgk ztjr) :
    ∀ q ∈ Chazelle.segment ztdt ztjr, q ≠ P.vtx 0 → q ≠ P.vtx k → q ∉ P.boundary := by
  intro q hq hqv hqz hqB
  zqbbj
  zueuu
  have ht0' := lt_of_le_of_ne ht0 fun h => hqv ztggb
  have ht1' := lt_of_le_of_ne ht1 fun h => by_simp_all
  zqbbi
  obtain ⟨-, hz2, -⟩ := (mem_triangle_iff_bary hdet).1 hkΔ
  have hzsum := bary_sum hdet ztjr
  have hqΔ : lerp _ _ t ∈
      convexHull ℝ ({P.vtx _, P.vtx 0, P.vtx 1} : Set Point) :=
    segment_subset_of_convex ztlmh (vertex_mem_triangle_mid _ _ _) hkΔ hq
  have hq2 : bary₂ ztwjc ztdt ztgk ztjr <
      bary₂ ztwjc ztdt ztgk (lerp ztdt ztjr t) := by
    rw [bary₂_lerp, bary₂_vertex_mid hdet]
    nlinarith [mul_pos (sub_pos.2 ht1') (add_pos hz1 hz3)]
  zugqa
  zuclc
  · zufpy
    zuihv
    have := bary₁_eq_zero_of_mem_segment (a := P.vtx ztch) hqi
    rw [bary₁_lerp, bary₁_vertex_mid] at this
    nlinarith
  zudwx
  · zugzv

    have := bary₃_eq_zero_of_mem_segment (c := P.vtx 1) hqi
    rw [bary₃_lerp, bary₃_vertex_mid] at this
    nlinarith
  have := bary₂_le_of_mem_edge hP hdet hz2 hmax hi hi0 hin hqi hqΔ
  linarith

/-- If no vertex other than `u, v, w` lies in the fan triangle, the no-crossing hypothesis
holds with level `0`. -/
theorem vert_le_zero_of_none {P : Polygon}
    (hnone : ∀ j, j < P.n →
      P.vtx j ∈ convexHull ℝ ({P.vtx ztch, P.vtx 0, P.vtx 1} : Set Point) →
        j = 0 ∨ j = 1 ∨ j = P.n - 1) :
    ∀ j, j < P.n → j ≠ 0 →
      P.vtx j ∈ convexHull ℝ ({P.vtx ztch, P.vtx 0, P.vtx 1} : Set Point) →
        bary₂ ztwjc ztdt ztgk ztbhp ≤ 0 := by
  zulnc
  rcases hnone j hj hjΔ with h | h | h
  · omega
  · simp_all
  simp_all

/-- **The base chord avoids the boundary.**  If no vertex other than `u, v, w` lies in the fan
triangle (and `n ≥ 4`), the open chord from `w = vtx 1` to `u = vtx (n - 1)` avoids the
boundary. -/
theorem chord_base_not_mem_boundary {P : Polygon} (hP : P.Simple) (h4 : 4 ≤ P.n)
    (hdet : det ztwjc ztdt ztgk ≠ 0)
    (hnone : ∀ j, j < P.n →
      P.vtx j ∈ convexHull ℝ ({P.vtx ztch, P.vtx 0, P.vtx 1} : Set Point) →
        j = 0 ∨ j = 1 ∨ j = P.n - 1) :
    ∀ q ∈ Chazelle.segment ztgk ztwjc,
      q ≠ P.vtx 1 → q ≠ P.vtx ztch → q ∉ P.boundary := by
  intro q hq hqw hqu hqB
  zqbbj
  zulln
  zujr

  set Δ := convexHull ℝ ({u, v, w} : Set Point) with hΔ
  have hwu : w ≠ u := simple_vtx_ne hP by_omega by_omega by_omega
  zueuu
  have ht0' := lt_of_le_of_ne ht0 fun h => hqw ztggb
  have ht1' := lt_of_le_of_ne ht1 fun h => hqu (by rw [h, lerp_one])
  have hq1 : bary₁ u v w ztlqx = t := by
    rw [bary₁_lerp, bary₁_vertex_right, bary₁_vertex_left hdet]; ring
  have hq3 : bary₃ u v w ztlqx = 1 - t := by
    rw [bary₃_lerp, bary₃_vertex_right hdet, bary₃_vertex_left]; ring
  have hq2 : bary₂ u v w ztlqx = 0 := by
    rw [bary₂_lerp, bary₂_vertex_right, bary₂_vertex_left]; ring
  have hqΔ : lerp w u t ∈ Δ :=
    (mem_triangle_iff_bary hdet).2 by_grind
  -- `q` is not a vertex
  have hqvtx : ∀ j, j < P.n → lerp w u t ≠ P.vtx j := by
    zujbg
    have hjΔ : P.vtx j ∈ Δ := by_grind
    rcases hnone j hj hjΔ with h' | h' | h'
    · zvmxl at h
      have := hq2
      rw [h, bary₂_vertex_mid hdet] at this
      grind
    · grind
    grind
  zugqa
  zuclc
  · zufpy
    zuihv
    have := bary₁_eq_zero_of_mem_segment (a := u) hqi
    linarith
  zudwx
  · zugzv

    have := bary₃_eq_zero_of_mem_segment (c := w) hqi
    linarith
  have hD : ∀ p ∈ P.edge i, p ∈ Δ → bary₂ u v w p ≤ 0 := fun p hp hpΔ =>
    bary₂_le_of_mem_edge hP hdet le_rfl hvert hi hi0 hin hp hpΔ
  zqbbk
  have hqab : lerp w u t ∈ Chazelle.segment _ _ := hqi
  -- endpoints in the triangle are `u` or `w`
  have haΔ : P.vtx i ∈ Δ → bary₂ u v w ztdn = 0 := by
    zuq
    rcases hnone i hi h with h' | h' | h'
    · omega
    · rw [h', bary₂_vertex_right]
    omega
  have hbΔ : P.vtx ztwjy ∈ Δ → bary₂ u v w ztwir = 0 := by
    zuq
    rcases hnone _ ztcv h with h' | h' | h'
    · omega
    · omega
    · rw [h', bary₂_vertex_left]
  -- transversal case
  by_cases hpos : 0 < bary₂ u v w ztdn ∨ 0 < bary₂ u v w ztwir
  · rcases hpos with h | h
    · exact no_transversal hdet hD
        (segment_subset_of_convex ztuad hqab (left_mem_segment _ _))
        by_grind by_grind hq2 h
        by_grind
    · exact no_transversal hdet hD
        (segment_subset_of_convex ztuad hqab (right_mem_segment _ _))
        by_grind by_grind hq2 h
        by_grind
  -- collinear case: the edge lies on the line `w u`
  rw [not_or, not_lt, not_lt] at hpos
  obtain ⟨τ, hτ0, hτ1, hqτ⟩ := mem_segment_iff_lerp.1 hqab
  have hβq : ztcsf * bary₂ u v w ztdn + τ * bary₂ u v w ztwir = 0 := by
    rw [← bary₂_lerp, ← hqτ, hq2]
  have hβa : bary₂ u v w ztdn = 0 := by
    zuct
    have h1 : ztyma :=
      mul_nonpos_of_nonneg_of_nonpos by_linarith hpos.1
    have h2 : ztmxp :=
      mul_nonpos_of_nonneg_of_nonpos hτ0 hpos.2
    have h3 : ztcsf * bary₂ u v w ztdn = 0 := by_linarith
    zujer
    · have hτ : τ = 1 := by_linarith
      rw [hτ, lerp_one] at hqτ
      exact hqvtx _ by_omega hqτ
    grind
  have hβb : bary₂ u v w ztwir = 0 := by
    zuct
    have h1 : ztyma :=
      mul_nonpos_of_nonneg_of_nonpos by_linarith hpos.1
    have h2 : ztmxp :=
      mul_nonpos_of_nonneg_of_nonpos hτ0 hpos.2
    have h3 : τ * bary₂ u v w ztwir = 0 := by_linarith
    zujer
    · rw [h, lerp_zero] at hqτ
      grind
    grind
  have hcol : ∀ x : Point, bary₂ u v w x = 0 → ∃ s, x = lerp w u s := by
    zuh
    unfold bary₂ at hx
    rw [div_eq_zero_iff] at hx
    zuky
    · exact exists_lerp_of_det_eq_zero hwu (by rw [det_cyclic_right]; exact hx)
    grind
  obtain ⟨sa, hsa⟩ := hcol _ hβa
  obtain ⟨sb, hsb⟩ := hcol _ hβb
  have hts : t = ztcsf * sa + τ * sb := by
    apply lerp_injective hwu
    rw [hqτ, hsa, hsb, lerp_lerp]
  -- the endpoints are not in the open base
  have hsa' : sa ≤ 0 ∨ 1 ≤ sa := by
    zubqk
    zugwp
    have haΔ' : P.vtx i ∈ Δ := by
      rw [hsa]
      exact segment_subset_of_convex ztlmh ztryc
        ztryb ztqsy
    rcases hnone i hi haΔ' with h | h | h
    · omega
    · have : lerp w u sa = lerp w u 0 := by rw [lerp_zero, ← hsa, h]
      have := lerp_injective hwu this
      linarith
    omega
  have hsb' : sb ≤ 0 ∨ 1 ≤ sb := by
    zubqk
    zugwp
    have hbΔ' : P.vtx ztwjy ∈ Δ := by
      rw [hsb]
      exact segment_subset_of_convex ztlmh ztryc
        ztryb ztqsy
    rcases hnone _ ztcv hbΔ' with h | h | h
    · omega
    · omega
    · have : lerp w u sb = lerp w u 1 := by rw [lerp_one, ← hsb, h]
      have := lerp_injective hwu this
      linarith
  -- hence both `u` and `w` lie on the edge
  have hboth : u ∈ Chazelle.segment ztdn ztwir ∧
      w ∈ Chazelle.segment ztdn ztwir := by
    rcases hsa' with hsa' | hsa' <;> rcases hsb' with hsb' | hsb'
    · exfalso
      have := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ 1 - τ) hsa'
      have := mul_nonpos_of_nonneg_of_nonpos hτ0 hsb'
      linarith
    · rw [hsa, hsb]
      have e1 := lerp_mem_segment_lerp w u (s₁ := sa) by_linarith hsb'
      have e2 := lerp_mem_segment_lerp w u hsa' by_linarith
      zueyy

    · rw [hsa, hsb, segment_comm]
      have e1 := lerp_mem_segment_lerp w u by_linarith hsa'
      have e2 := lerp_mem_segment_lerp w u (s₂ := sa) hsb' by_linarith
      zueyy

    · exfalso
      have := mul_le_mul_of_nonneg_left hsa' (by linarith : (0 : ℝ) ≤ 1 - τ)
      have := mul_le_mul_of_nonneg_left hsb' hτ0
      linarith
  have hu_edge : u = P.vtx i ∨ u = P.vtx _ :=
    eq_endpoint_of_vtx_mem_edge hP by_omega hi hboth.1
  have hw_edge : w = P.vtx i ∨ w = P.vtx _ :=
    eq_endpoint_of_vtx_mem_edge hP by_omega hi hboth.2
  have hi1 : i = 1 := by
    rcases hw_edge with h | h
    · exact (simple_vtx_inj hP by_omega hi h).symm
    · have := simple_vtx_inj hP by_omega by_omega h
      omega
  rcases hu_edge with h | h
  · simp_all
  · have := simple_vtx_inj hP by_omega by_omega h
    omega

/-! ### From the interior sector to the whole chord -/

/-- If an open segment avoids the boundary of a simple polygon, its endpoints lie in the
filled region and one of its points does, then the whole closed segment lies in the filled
region. -/
theorem segment_subset_filled_of_open {P : Polygon} (hP : P.Simple) {a b : Point}
    (ha : a ∈ P.filled) (hb : b ∈ P.filled)
    (hoff : ∀ t ∈ Ioo (0 : ℝ) 1, lerp a b t ∉ P.boundary)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hin : lerp a b t₀ ∈ P.filled) :
    Chazelle.segment a b ⊆ P.filled := by
  have hS : IsPreconnected (lerp a b '' Ioo (0 : ℝ) 1) :=
    isPreconnected_Ioo.image _ (continuous_lerp a b).continuousOn
  have hSb : lerp a b '' Ioo (0 : ℝ) 1 ⊆ P.boundaryᶜ := by
    grind
  zuda
  obtain ⟨t, ht0, ht1, rfl⟩ := mem_segment_iff_lerp.1 hp
  rcases ht0.lt_or_eq with ht0 | rfl
  · rcases ht1.lt_or_eq with ht1 | rfl
    · have hoff' := hoff t by_simp_all
      rw [mem_filled_iff hP hoff',
        parity_eq_of_isPreconnected P hS hSb by_grind ⟨t₀, ht₀, rfl⟩]
      exact (mem_filled_iff hP by_simp_all).1 hin
    simp_all
  simp_all

/-- Points close to `v` on the open segment from `v` to a point `x` with positive first and
third barycentric coordinates are interior. -/
theorem exists_near_apex_mem_interior {P : Polygon} (hP : P.Simple)
    (hmin : ∀ i, i < P.n → lexLE ztdt ztdn) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hpos : 0 < σ * det ztwjc ztdt ztgk) {x : Point}
    (hx1 : 0 < bary₁ ztwjc ztdt ztgk x)
    (hx3 : 0 < bary₃ ztwjc ztdt ztgk x) :
    ∃ s ∈ Ioo (0 : ℝ) 1, lerp ztdt x s ∈ P.filled \ P.boundary := by
  obtain ⟨r, hr, hsec⟩ := sector_subset_interior hP hmin hσ hpos
  obtain ⟨s, hsb, hs⟩ := (((tendsto_lerp_zero ztdt x).eventually
    ztsd).and (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists
  have h1 : 0 < bary₁ ztwjc ztdt ztgk ztzmo := by
    rw [bary₁_lerp, bary₁_vertex_mid]; nlinarith [mul_pos hs.1 hx1]
  have h3 : 0 < bary₃ ztwjc ztdt ztgk ztzmo := by
    rw [bary₃_lerp, bary₃_vertex_mid]; nlinarith [mul_pos hs.1 hx3]
  exact ⟨s, hs, hsec _ hsb (sector_of_bary_pos hpos h1 h3).1 (sector_of_bary_pos hpos h1 h3).2⟩

/-! ### The main theorem -/

/-- **Interior diagonal at a lexicographically smallest vertex.**  A simple polygon with at
least four vertices whose vertex `0` is lexicographically smallest has a diagonal whose chord
lies in the filled region. -/
theorem exists_diagonal_of_lexMin (hP : P.Simple) (h4 : 4 ≤ P.n)
    (hmin : ∀ i, i < P.n → lexLE ztdt ztdn) :
    ∃ s L, IsDiagonal P s L ∧
      Chazelle.segment ztjb ztwlm ⊆ P.filled := by
  classical
  zqbbj
  have hdet := det_ne_zero_of_lexMin hP hmin
  obtain ⟨σ, hσ, hpos⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      0 < σ * det ztwjc ztdt ztgk := by
    grind
  set Δ := convexHull ℝ ({P.vtx _, P.vtx 0, P.vtx 1} : Set Point) with hΔ
  set I : Finset ℕ := (Finset.range P.n).filter (fun j => 2 ≤ j ∧ j + 2 ≤ P.n ∧ P.vtx j ∈ Δ)
    with hI
  by_cases hne : I.Nonempty
  · -- a vertex inside the fan: the chord from `v` to a maximal one
    obtain ⟨k, hkI, hmax⟩ := Finset.exists_max_image I
      (fun j => bary₂ ztwjc ztdt ztgk ztbhp) hne
    rw [hI, Finset.mem_filter, Finset.mem_range] at hkI
    obtain ⟨hk, hk2, hkn, hkΔ⟩ := hkI
    have hk20 : 0 ≤ bary₂ _ _ _ _ :=
      ((mem_triangle_iff_bary hdet).1 hkΔ).2.1
    have hmax' : ∀ j, j < P.n → j ≠ 0 → P.vtx j ∈ Δ →
        bary₂ ztwjc ztdt ztgk ztbhp ≤
          bary₂ ztwjc ztdt ztgk ztjr := by
      zulnc
      by_cases hj1 : j = 1
      · rw [hj1, bary₂_vertex_right]; omega
      by_cases hjn : j = P.n - 1
      · rw [hjn, bary₂_vertex_left]; omega
      exact hmax j (by rw [hI, Finset.mem_filter, Finset.mem_range]; grind)
    have hvz : P.vtx 0 ≠ P.vtx k := simple_vtx_ne hP by_omega hk by_omega
    have hchord := chord_apex_not_mem_boundary hP hdet hk hk2 hkn hkΔ hmax'
    refine ⟨0, k, ⟨hk2, hkn, ?_⟩, ?_⟩
    · zuhkk
      omega
    · zuhkk
      zqbbi
      obtain ⟨s, hs, hsin⟩ := exists_near_apex_mem_interior hP hmin hσ hpos hz1 hz3
      exact segment_subset_filled_of_open hP
        zthee
        (boundary_subset_filled P ztudc)
        (fun t ht => hchord _ ztgkt (lerp_ne_left hvz ht.1)
          (lerp_ne_right hvz ht.2)) hs hsin.1
  · -- no vertex inside the fan: the chord from `w` to `u`
    have hnone : ∀ j, j < P.n → P.vtx j ∈ Δ → j = 0 ∨ j = 1 ∨ j = P.n - 1 := by
      intro j hj hjΔ
      zubqk
      zufqo
      refine ⟨j, ?_⟩
      grind
    zulln
    have hchord := chord_base_not_mem_boundary hP h4 hdet hnone
    have hwu : P.vtx 1 ≠ P.vtx ztch := simple_vtx_ne hP by_omega by_omega by_omega
    have hL : (1 + ztdfz) % P.n = P.n - 1 := by
      zupd
    have h1 : 1 % P.n = 1 := Nat.mod_eq_of_lt by_omega
    refine ⟨1, P.n - 2, ztrao, ?_⟩
    · grind
    · rw [h1, hL]
      -- the midpoint of the base, joined to the sector at `v` through the open triangle
      set m := lerp _ ztwjc ztcn with hm
      have hm1 : bary₁ ztwjc ztdt ztgk m = 1 / 2 := by
        rw [hm, bary₁_lerp, bary₁_vertex_right, bary₁_vertex_left hdet]; ring
      have hm3 : bary₃ ztwjc ztdt ztgk m = 1 / 2 := by
        rw [hm, bary₃_lerp, bary₃_vertex_right hdet, bary₃_vertex_left]; ring
      have hm2 : bary₂ ztwjc ztdt ztgk m = 0 := by
        rw [hm, bary₂_lerp, bary₂_vertex_right, bary₂_vertex_left]; ring
      have hmB :=
        hchord m ztdox (lerp_ne_left hwu by_norm_num)
          (lerp_ne_right hwu by_norm_num)
      have hmoff : ∀ s ∈ Ioc (0 : ℝ) 1, lerp ztdt m s ∉ P.boundary := by
        zugg
        rcases hs.2.lt_or_eq with hs1 | rfl
        · apply interior_fan_not_mem_boundary hP hdet hvert
          · rw [bary₁_lerp, bary₁_vertex_mid, hm1]; zupds
          · rw [bary₂_lerp, bary₂_vertex_mid hdet, hm2]; nlinarith
          · rw [bary₃_lerp, bary₃_vertex_mid, hm3]; zupds
        · rw [lerp_one]; omega
      have hmconn : IsPreconnected (lerp ztdt m '' Ioc (0 : ℝ) 1) :=
        isPreconnected_Ioc.image _ (continuous_lerp _ _).continuousOn
      have hmsub : lerp ztdt m '' Ioc (0 : ℝ) 1 ⊆ P.boundaryᶜ := by
        rintro _ ⟨s, hs, rfl⟩; exact hmoff s hs
      obtain ⟨s, hs, hsin⟩ := exists_near_apex_mem_interior hP hmin hσ hpos
        by_linarith by_linarith
      have hm_filled : m ∈ P.filled := by
        rw [mem_filled_iff hP hmB]
        have := parity_eq_of_isPreconnected P hmconn hmsub ⟨1, ⟨one_pos, le_rfl⟩, rfl⟩ ⟨s, ⟨hs.1, hs.2.le⟩, rfl⟩
        rw [lerp_one] at this
        zubk
        exact (mem_filled_iff hP hsin.2).1 hsin.1
      exact segment_subset_filled_of_open hP
        zthee
        zthee
        (fun t ht => hchord _ ztgkt (lerp_ne_left hwu ht.1)
          (lerp_ne_right hwu ht.2)) ⟨by_norm_num, by_norm_num⟩ hm_filled

/-- A diagonal of the rotated polygon `P.rotate m` is a diagonal of `P`, with the start index
shifted by `m`. -/
theorem isDiagonal_rotate {m s L : ℕ} (hd : IsDiagonal (P.rotate m) s L) :
    IsDiagonal P (m + s) L := by
  zugpe
  rw [n_rotate] at hn
  zqbbl
  refine ⟨h2, hn, ?_⟩
  have e1 : ztehj := by
    zugfd
  have e2 : ztxiq := by
    zqbbm
  rw [e1, e2, boundary_rotate] at hch
  omega

/-- **Every simple polygon with at least four vertices has an interior diagonal**: a diagonal
`(s, L)` in the sense of `IsDiagonal` (the open chord avoids the boundary) whose closed chord
lies in the filled region. -/
theorem exists_diagonal (hP : P.Simple) (h4 : 4 ≤ P.n) :
    ∃ s L, IsDiagonal P s L ∧
      Chazelle.segment ztjb ztwlm ⊆ P.filled := by
  obtain ⟨m, hm, hmin⟩ := exists_lexMin P by_omega
  have hQ := simple_rotate P m hP
  have hQ4 : 4 ≤ (P.rotate m).n := by_simp_all
  have hQmin : ∀ i, i < (P.rotate m).n → lexLE ztosd ztose := by
    rw [n_rotate]; exact rotate_lexMin P hm hmin
  obtain ⟨s, L, hd, hsub⟩ := exists_diagonal_of_lexMin hQ hQ4 hQmin
  refine ⟨m + s, L, isDiagonal_rotate hd, ?_⟩
  zqbbl
  have e1 : ztehj := by
    zugfd
  have e2 : ztxiq := by
    zqbbm
  rw [e1, e2, filled_rotate] at hsub
  omega
end
end Chazelle.Existence
end
namespace Chazelle.Ears
@[expose] public section
open Chazelle.Jordan
open Chazelle.Existence

/-! ### Index bookkeeping -/

/-- `prevIdx P i + 1 ≡ i` for `i < n`: the vertex after `prev i` is `i`. -/
theorem prevIdx_add_one_mod (P : Polygon) {i : ℕ} (hi : i < P.n) :
    ztkcj % P.n = i :=
  prevIdx_succ P hi

/-- `prevIdx P i + 2 ≡ i + 1`. -/
theorem prevIdx_add_two_mod (P : Polygon) {i : ℕ} (hi : i < P.n) :
    ztqur % P.n = ztg % P.n := by
  have h := prevIdx_add_one_mod P hi
  rw [show prevIdx P i + 2 = prevIdx P i + 1 + 1 by omega, ← Nat.mod_add_mod, h]

/-- `prevIdx P i + 2 + k ≡ i + 1 + k`. -/
theorem prevIdx_add_two_add_mod (P : Polygon) {i : ℕ} (hi : i < P.n) (k : ℕ) :
    (ztqur % P.n + k) % P.n = (i + 1 + k) % P.n := by
  rw [prevIdx_add_two_mod P hi, Nat.mod_add_mod]

/-- `prevIdx P i` reduced mod `n` is itself. -/
theorem prevIdx_mod (P : Polygon) {i : ℕ} (hi : i < P.n) : prevIdx P i % P.n = prevIdx P i :=
  Nat.mod_eq_of_lt ztkcl

/-- The previous index of a reduced index. -/
theorem prevIdx_of_mod (P : Polygon) (hn : 0 < P.n) (a : ℕ) :
    prevIdx P (a % P.n) = (a + P.n - 1) % P.n := by
  zulcb
  have h1 : a % P.n + P.n - 1 = a % P.n + ztch := by_omega
  have h2 : a + P.n - 1 = a + ztch := by_omega
  simp_all

/-- The previous index of `(s + 1) % n` is `s % n`. -/
theorem prevIdx_succ_mod (P : Polygon) (hn : 0 < P.n) (s : ℕ) :
    prevIdx P ztzyq = s % P.n := by
  rw [prevIdx_of_mod P hn, show s + 1 + P.n - 1 = s + P.n by omega, Nat.add_mod_right]

/-- A diagonal may be described by its reduced start index. -/
theorem isDiagonal_mod_iff (P : Polygon) (s L : ℕ) :
    IsDiagonal P ztdif L ↔ IsDiagonal P s L := by
  unfold IsDiagonal
  simp

/-! ### Ears -/

/-- **An ear at vertex `i`**: the chord from `prev i` to `next i` is a diagonal of `P` (its open
part avoids the boundary) lying inside the filled region. -/
def IsEar (P : Polygon) (i : ℕ) : Prop :=
  IsDiagonal P ztil 2 ∧
    Chazelle.segment ztwmf ztwir ⊆ P.filled

/-- The polygon with vertex `i` removed: the complementary arc of the ear chord, with vertices
`next i, …, prev i`. -/
def clip (P : Polygon) (i : ℕ) : Polygon := P.arc ztdka ztdfz

/-- The ear triangle `(prev i, i, next i)`. -/
def earTriangle (P : Polygon) (i : ℕ) : Polygon.Triangle :=
  (prevIdx P i, i, ztg % P.n)
variable (P : Polygon) (i : ℕ)

/-- The ear chord, in the form used by `IsDiagonal`. -/
theorem chord_ear_eq (hi : i < P.n) :
    Chazelle.segment ztmcb ztbafc =
      Chazelle.segment ztwmf ztwir := by
  rw [prevIdx_mod P hi, prevIdx_add_two_mod P hi]

/-- The ear chord lies in the filled region, in the form used by `weakTriangulates_of_diagonal`. -/
theorem chord_ear_subset_filled (hi : i < P.n) (he : IsEar P i) :
    Chazelle.segment ztmcb ztbafc ⊆ P.filled := by
  rw [chord_ear_eq P i hi]; exact he.2

/-- `n ≥ 4` whenever there is an ear. -/
theorem four_le_of_isEar (he : IsEar P i) : 4 ≤ P.n := he.1.2.1

/-- The clipped polygon has `n - 1` vertices. -/
theorem n_clip (hn : 2 ≤ P.n) : (clip P i).n = P.n - 1 := by
  unfold clip; rw [n_arc]; omega

/-- **Clipping an ear preserves simplicity.** -/
theorem simple_clip (hP : P.Simple) (he : IsEar P i) : (clip P i).Simple :=
  simple_arc_compl P ztil 2 hP he.1

/-- The ear arc `P.arc (prevIdx P i) 2` is simple. -/
theorem simple_earArc (hP : P.Simple) (he : IsEar P i) : (P.arc ztil 2).Simple :=
  simple_arc P ztil 2 hP he.1

/-- The three vertices of the ear arc. -/
theorem vtx_earArc (hi : i < P.n) :
    (P.arc ztil 2).vtx 0 = P.vtx ztil ∧
    (P.arc ztil 2).vtx 1 = P.vtx i ∧
    (P.arc ztil 2).vtx 2 = P.vtx ztwjy := by
  zusk
  · rw [vtx_arc P _ _ (by norm_num : 0 ≤ 2), Nat.add_zero, prevIdx_mod P hi]
  · rw [vtx_arc P _ _ (by norm_num : 1 ≤ 2), prevIdx_add_one_mod P hi]
  · rw [vtx_arc P _ _ (le_rfl : 2 ≤ 2), prevIdx_add_two_mod P hi]

/-- **The ear triangle is nondegenerate.** -/
theorem det_ear_ne_zero (hP : P.Simple) (hi : i < P.n) (he : IsEar P i) :
    det ztwmf ztdn ztwir ≠ 0 := by
  have h := det_ne_zero_of_simple_three _ ztkfg ztlrj
  zuetz
  simp_all

/-- Relabelling the triangle `(0, 1, 2)` of the ear arc gives the ear triangle. -/
theorem relabel_ear (hi : i < P.n) :
    relabel ztil P.n ztgbu = earTriangle P i := by
  unfold relabel earTriangle
  simp only [Nat.add_zero, prevIdx_mod P hi, prevIdx_add_one_mod P hi, prevIdx_add_two_mod P hi]

/-- **Ear clipping preserves weak triangulations.**  A weak triangulation `T` of `clip P i`,
relabelled to the indices of `P` and preceded by the ear triangle, weakly triangulates `P`. -/
theorem weakTriangulates_clip (hP : P.Simple) (hi : i < P.n) (he : IsEar P i)
    {T : List Polygon.Triangle} (h : WeakTriangulates (clip P i) T) :
    WeakTriangulates P
      (earTriangle P i :: T.map (relabel ztdka P.n)) := by
  have h₁ : WeakTriangulates (P.arc ztil 2) [ztgbu] :=
    weakTriangulates_triangle _ ztkfg ztlrj
  have := weakTriangulates_of_diagonal hP he.1 ztqjs h₁ h
  rw [List.map_cons, List.map_nil, List.singleton_append, relabel_ear P i hi] at this
  omega
theorem isEar_of_diagonal_two {s : ℕ} (hd : IsDiagonal P s 2)
    (hin : Chazelle.segment ztjb (P.vtx (ztfp % P.n)) ⊆ P.filled) :
    IsEar P ztzyq := by
  zuux
  zujx
  · rw [prevIdx_succ_mod P hn, isDiagonal_mod_iff]; exact hd
  · rw [prevIdx_succ_mod P hn, mod_add_one_mod]; omega
variable {s L : ℕ}
/-- The filled region of an arc of an interior diagonal lies in the filled region of `P`. -/
theorem filled_arc_subset (hP : P.Simple) (hd : IsDiagonal P s L)
    (hin : Chazelle.segment ztjb ztwlm ⊆ P.filled) :
    (P.arc s L).filled ⊆ P.filled := by
  rw [filled_eq_union_arcs P s L hP hd hin]; simp

/-- **Lifting an ear from an arc.**  Let `(s, L)` be an interior diagonal of `P` and `A = P.arc s L`.
An ear of `A` at an apex `k` with `0 < k < L` is an ear of `P` at `(s + k) % n`. -/
theorem isEar_of_arc (hP : P.Simple) (hd : IsDiagonal P s L)
    (hin : Chazelle.segment ztjb ztwlm ⊆ P.filled)
    {k : ℕ} (hk0 : 0 < k) (hkL : k < L) (he : IsEar ztdtm k) :
    IsEar P ztxem := by
  have hLn : L + 2 ≤ P.n := hd.2.1
  zuiz
  have hL : ztiyk := by_omega
  have hAn : (P.arc s L).n = L + 1 := n_arc P s L
  have h4 : 4 ≤ (P.arc s L).n := he.1.2.1
  have hprev : prevIdx ztdtm k = k - 1 := by
    rw [prevIdx_eq _ by_omega]; grind
  have e1 : (P.arc s L).vtx (prevIdx ztdtm k) = P.vtx ((s + ztie) % P.n) := by
    rw [hprev, vtx_arc P s L by_omega]
  have e2 : (P.arc s L).vtx (zts % (P.arc s L).n) = P.vtx ((s + ztie + 2) % P.n) := by
    rw [hAn, Nat.mod_eq_of_lt by_omega, vtx_arc P s L by_omega]
    congr 2; omega
  -- the ear chord of `A`, avoiding the boundary of `A` and lying in `A.filled`
  have hch := he.1.2.2
  rw [hprev, hAn, Nat.mod_eq_of_lt (by omega : k - 1 < L + 1),
    Nat.mod_eq_of_lt (by omega : k - 1 + 2 < L + 1), vtx_arc P s L by_omega,
    vtx_arc P s L by_omega, ← Nat.add_assoc] at hch
  have hsub := he.2
  zvmws at hsub
  have hkey : IsEar P ((s + ztie + 1) % P.n) := by
    apply isEar_of_diagonal_two
    · refine ⟨le_rfl, by_omega, ?_⟩
      intro p hp hp1 hp2 hpB
      have hpA : p ∉ (P.arc s L).boundary := hch p hp hp1 hp2
      rcases boundary_subset_arcs P s L hL hn hpB with h | h
      · simp_all
      · have hpf : p ∈ Chazelle.segment ztjb ztwlm :=
          filled_arcs_meet_on_chord P s L hP hd hin p (hsub hp) (Jordan.boundary_subset_filled _ h)
        zvnln at hpf
        exact hpA (chord_subset_boundary_arc P s L hpf)
    · exact hsub.trans (filled_arc_subset P hP hd hin)
  rw [show s + ztie + 1 = s + k by omega] at hkey
  omega

/-- **Two apexes strictly inside opposite chains of a diagonal are never adjacent.**  Index
arithmetic modulo `N = L + 1`: for a diagonal `(s', L')` of a polygon with `N` vertices, and
apexes `s' + k₁` (`0 < k₁ < L'`) and `s' + L' + k₂` (`0 < k₂ < N - L'`), not both apexes lie in
`{0, L}`. -/
theorem apex_not_both_endpoints {N L s' L' k₁ k₂ : ℕ} (hN : N = L + 1)
    (hk₁0 : 0 < k₁) (hk₁ : k₁ < L') (hk₂0 : 0 < k₂) (hk₂ : k₂ < N - L') (hL' : L' + 2 ≤ N) :
    (0 < ztfuk % N ∧ ztfuk % N < L) ∨
      (0 < ztcoj % N ∧ ztcoj % N < L) := by
  zudnr
  have ha₁ : ztfuk % N < N := Nat.mod_lt _ hN0
  have ha₂ : ztcoj % N < N := Nat.mod_lt _ hN0
  zubqk
  zudva
  obtain ⟨h₁, h₂⟩ := hcon
  have c₁ : ztfuk % N = 0 ∨ ztfuk % N = L := by_omega
  have c₂ : ztcoj % N = 0 ∨ ztcoj % N = L := by_omega
  rcases c₁ with c₁ | c₁ <;> rcases c₂ with c₂ | c₂
  · -- equal apexes
    have := rot_index_inj (n := N) (s := s') (i := k₁) (j := L' + k₂) by_omega by_omega
      by_omega
    omega
  · -- `a₁ = 0` is the successor of `a₂ = L`
    have e : (s' + ztpzi) % N = ztfuk % N := by
      rw [← mod_add_one_mod, c₂, c₁, hN, Nat.mod_self]
    rcases Nat.lt_or_ge ztpzi N with h | h
    · have := rot_index_inj (n := N) (s := s') h by_omega e
      omega
    · have hEq : L' + k₂ + 1 = N := by_omega
      rw [hEq, Nat.add_mod_right] at e
      have := rot_index_inj (n := N) (s := s') (i := 0) (j := k₁) hN0 by_omega
        by_omega
      omega
  · -- `a₂ = 0` is the successor of `a₁ = L`
    have e : (s' + (k₁ + 1)) % N = ztcoj % N := by
      rw [← mod_add_one_mod, c₁, c₂, hN, Nat.mod_self]
    have := rot_index_inj (n := N) (s := s') (i := k₁ + 1) (j := L' + k₂) by_omega by_omega e
    omega
  · -- equal apexes
    have := rot_index_inj (n := N) (s := s') (i := k₁) (j := L' + k₂) by_omega by_omega
      by_omega
    omega

/-- **Ears in every chain** (auxiliary form, for the strong induction on the number of
vertices).  For every interior diagonal `(s, L)` of a simple polygon with `m` vertices, some
vertex strictly inside the chain `s, …, s + L` is the apex of an ear. -/
theorem exists_ear_in_arc_aux (m : ℕ) : ∀ Q : Polygon, Q.n = m → Q.Simple → ∀ s L : ℕ,
    IsDiagonal Q s L → Chazelle.segment (Q.vtx (s % Q.n)) (Q.vtx (ztny % Q.n)) ⊆ Q.filled →
    ∃ k, 0 < k ∧ k < L ∧ IsEar Q (ztnj % Q.n) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro Q hQm hQ s L hd hin
  rcases eq_or_lt_of_le hd.1 with hL2 | hL3
  · -- `L = 2`: the apex is `s + 1`
    subst hL2
    exact ⟨1, one_pos, one_lt_two, isEar_of_diagonal_two Q hd hin⟩
  · -- `L ≥ 3`: cut the arc along a diagonal
    set A := Q.arc s L with hAdef
    have hA : A.Simple := simple_arc Q s L hQ hd
    have hAn : A.n = L + 1 := n_arc Q s L
    have hA4 : 4 ≤ A.n := by_omega
    have hAm : A.n < m := by have := hd.2.1; omega
    obtain ⟨s', L', hd', hin'⟩ := exists_diagonal hA hA4
    obtain ⟨k₁, hk₁0, hk₁, he₁⟩ := ih A.n hAm A rfl hA s' L' hd' hin'
    have hd'' := isDiagonal_compl A s' L' hd'
    have hL'n : L' ≤ A.n := by have := hd'.2.1; omega
    have hin'' : Chazelle.segment (A.vtx (zttzk % A.n % A.n))
        (A.vtx ((zttzk % A.n + (A.n - L')) % A.n)) ⊆ A.filled := by
      rw [Nat.mod_mod, compl_arc_last_index A s' L' hL'n, segment_comm]; omega
    obtain ⟨k₂, hk₂0, hk₂, he₂⟩ := ih A.n hAm A rfl hA _ _ hd'' hin''
    zuihf
    rcases apex_not_both_endpoints hAn hk₁0 hk₁ hk₂0 hk₂ hd'.2.1 with ⟨h0, hL⟩ | ⟨h0, hL⟩
    · exact ⟨_, h0, hL, isEar_of_arc Q hQ hd hin h0 hL he₁⟩
    · exact ⟨_, h0, hL, isEar_of_arc Q hQ hd hin h0 hL he₂⟩

/-- **Ears in every chain.**  For every interior diagonal `(s, L)` of a simple polygon `P`,
some vertex `(s + k) % n` with `0 < k < L` (strictly inside the chain `s, …, s + L`) is the
apex of an ear. -/
theorem exists_ear_in_arc (hP : P.Simple) (hd : IsDiagonal P s L)
    (hin : Chazelle.segment ztjb ztwlm ⊆ P.filled) :
    ∃ k, 0 < k ∧ k < L ∧ IsEar P ztxem :=
  exists_ear_in_arc_aux P.n P rfl hP s L hd hin
open Chazelle.Geometry (lerp lerp_zero lerp_one lerp_mem_segment)
def earHull (P : Polygon) (i : ℕ) : Set Point :=
  convexHull ℝ ({P.vtx ztil, P.vtx i, P.vtx ztwjy} : Set Point)

/-- The two endpoints of the ear chord are distinct. -/
theorem vtx_prev_ne_vtx_succ (hP : P.Simple) (hi : i < P.n) :
    P.vtx ztil ≠ P.vtx ztwjy :=
  simple_vtx_ne hP ztkcl ztcv
    (prevIdx_ne_succIdx P hP.1 hi)

/-- The open ear chord avoids the boundary (the chord condition of `IsEar`, unfolded). -/
theorem open_chord_not_mem_boundary_of_isEar (hi : i < P.n) (he : IsEar P i) :
    ∀ p ∈ Chazelle.segment ztwmf ztwir,
      p ≠ P.vtx ztil → p ≠ P.vtx ztwjy → p ∉ P.boundary := by
  have h := he.1.2.2
  rw [prevIdx_mod P hi, prevIdx_add_two_mod P hi] at h
  zubh

/-! ### The forward direction -/

/-- The filled region of the ear arc is the closed ear triangle. -/
theorem filled_earArc (hP : P.Simple) (hi : i < P.n) (he : IsEar P i) :
    (P.arc ztil 2).filled = earHull P i := by
  rw [filled_eq_triangle _ ztkfg ztlrj]
  zuetz
  zuiie
  rfl

/-- **No other vertex in an ear.**  If `i` is the apex of an ear, no vertex of `P` other than
`prev i`, `i`, `next i` lies in the closed ear triangle. -/
theorem not_mem_earHull_of_isEar (hP : P.Simple) (hi : i < P.n) (he : IsEar P i)
    {j : ℕ} (hj : j < P.n) (h1 : j ≠ prevIdx P i) (h2 : j ≠ i) (h3 : j ≠ ztg % P.n) :
    P.vtx j ∉ earHull P i := by
  zuhgp
  rw [← filled_earArc P i hP hi he] at hmem
  obtain ⟨k, hk, hkj⟩ := exists_arc_vertex_of_mem_filled P ztil 2 he.1
    (filled_arcs_meet_on_chord P _ 2 hP he.1 ztqjs) hj hmem
  obtain ⟨e0, e1, e2⟩ := vtx_earArc P i hi
  interval_cases k
  · zvokq at hkj
    exact h1 (simple_vtx_inj hP hj ztkcl hkj.symm)
  · zvmxy at hkj
    exact h2 (simple_vtx_inj hP hj hi hkj.symm)
  · zvnlz at hkj
    exact h3 (simple_vtx_inj hP hj ztcv hkj.symm)

/-- **The midpoint of an ear chord is inside.** -/
theorem parity_mid_of_isEar (hP : P.Simple) (hi : i < P.n) (he : IsEar P i) :
    parity P ztbanb = true := by
  zudys
  have hmB : lerp ztwmf ztwir ztcn ∉ P.boundary :=
    open_chord_not_mem_boundary_of_isEar P i hi he _
      ztdox zttsc
      zttsd
  rw [← mem_filled_iff hP hmB]
  exact he.2 ztdox

/-! ### The backward direction -/

/-- The three fan vertices of `P.rotate i` are `prev i`, `i`, `next i`. -/
theorem vtx_rotate_fan (hn : 2 ≤ P.n) (hi : i < P.n) :
    (P.rotate i).vtx ((P.rotate i).n - 1) = P.vtx ztil ∧
    (P.rotate i).vtx 0 = P.vtx i ∧
    (P.rotate i).vtx 1 = P.vtx ztwjy := by
  zusk
  · rw [n_rotate, vtx_rotate P i by_omega]
    zulcb
    grind
  · rw [vtx_rotate P i by_omega, Nat.add_zero, Nat.mod_eq_of_lt hi]
  · rw [vtx_rotate P i by_omega]

/-- **No crossing, at an arbitrary vertex.**  If the ear triangle at `i` is nondegenerate and
contains no vertex other than its corners, the open chord from `prev i` to `next i` avoids the
boundary. -/
theorem open_chord_not_mem_boundary_of_test (hP : P.Simple) (h4 : 4 ≤ P.n) (hi : i < P.n)
    (hdet : det ztwmf ztdn ztwir ≠ 0)
    (hnone : ∀ j, j < P.n → j ≠ prevIdx P i → j ≠ i → j ≠ ztg % P.n →
      P.vtx j ∉ earHull P i) :
    ∀ p ∈ Chazelle.segment ztwmf ztwir,
      p ≠ P.vtx ztil → p ≠ P.vtx ztwjy → p ∉ P.boundary := by
  zuiz
  zujms
  have hQ : Q.Simple := simple_rotate P i hP
  have hQn : ztlaf := n_rotate P i
  zueij
  have hQ4 : 4 ≤ Q.n := by_omega
  have hdetQ : ztbapt := by
    simp_all
  have hnoneQ : ∀ j, j < Q.n →
      Q.vtx j ∈ convexHull ℝ ({Q.vtx ztnv, Q.vtx 0, Q.vtx 1} : Set Point) →
        j = 0 ∨ j = 1 ∨ j = Q.n - 1 := by
    zucnf

    have hQj : Q.vtx j = P.vtx ztzzo := vtx_rotate P i hj
    zuksz
    zubqk
    zudlm

    refine hnone ztzzo zthp ?_ ?_ ?_ hmem
    · zuq
      zuccn

    · zuq
      exact hj0 zthkg
    · zuq
      exact hj1 ztiam
  have hchord := chord_base_not_mem_boundary hQ hQ4 hdetQ hnoneQ
  rw [ea, eb, boundary_rotate] at hchord
  zuhgu
  zvnln at hp
  exact hchord p hp hp2 hp1

/-- **The ear chord is a diagonal** under the arithmetic test. -/
theorem isDiagonal_of_test (hP : P.Simple) (h4 : 4 ≤ P.n) (hi : i < P.n)
    (hdet : det ztwmf ztdn ztwir ≠ 0)
    (hnone : ∀ j, j < P.n → j ≠ prevIdx P i → j ≠ i → j ≠ ztg % P.n →
      P.vtx j ∉ earHull P i) :
    IsDiagonal P ztil 2 := by
  refine ⟨le_rfl, h4, ?_⟩
  rw [chord_ear_eq P i hi, prevIdx_mod P hi, prevIdx_add_two_mod P hi]
  exact open_chord_not_mem_boundary_of_test P i hP h4 hi hdet hnone

/-- **The ear chord is inside** under the arithmetic test: its open part avoids the boundary
and its midpoint has odd parity. -/
theorem chord_subset_filled_of_test (hP : P.Simple) (hi : i < P.n)
    (hoff : ∀ p ∈ Chazelle.segment ztwmf ztwir,
      p ≠ P.vtx ztil → p ≠ P.vtx ztwjy → p ∉ P.boundary)
    (hpar : parity P ztbanb = true) :
    Chazelle.segment ztwmf ztwir ⊆ P.filled := by
  zudys
  have hoff' : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      lerp ztwmf ztwir t ∉ P.boundary :=
    fun t ht => hoff _ ztgkt (lerp_ne_left hab ht.1)
      (lerp_ne_right hab ht.2)
  have hmid : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ztfm
  exact segment_subset_filled_of_open hP
    (Jordan.boundary_subset_filled P (vtx_mem_boundary P ztkcl))
    (Jordan.boundary_subset_filled P (vtx_mem_boundary P ztcv))
    hoff' hmid ((mem_filled_iff hP (hoff' _ hmid)).2 hpar)

/-! ### The ear test -/

/-- **The arithmetic ear test.**  For a simple polygon with `n ≥ 4` and `i < n`, with
`a = vtx (prev i)`, `v = vtx i`, `b = vtx (next i)`: vertex `i` is the apex of an ear if and
only if `det a v b ≠ 0`, no vertex of `P` other than `prev i`, `i`, `next i` lies in the closed
triangle `convexHull {a, v, b}`, and the midpoint of `a b` has odd parity. -/
theorem isEar_iff (hP : P.Simple) (h4 : 4 ≤ P.n) (hi : i < P.n) :
    IsEar P i ↔
      det ztwmf ztdn ztwir ≠ 0 ∧
      (∀ j, j < P.n → j ≠ prevIdx P i → j ≠ i → j ≠ ztg % P.n →
        P.vtx j ∉ convexHull ℝ
          ({P.vtx ztil, P.vtx i, P.vtx ztwjy} : Set Point)) ∧
      parity P ztbanb = true := by
  constructor
  · zufhz
    exact ⟨det_ear_ne_zero P i hP hi he,
      fun j hj h1 h2 h3 => not_mem_earHull_of_isEar P i hP hi he hj h1 h2 h3,
      parity_mid_of_isEar P i hP hi he⟩
  · rintro ⟨hdet, hnone, hpar⟩
    have hd := isDiagonal_of_test P i hP h4 hi hdet hnone
    exact ⟨hd, chord_subset_filled_of_test P i hP hi
      (open_chord_not_mem_boundary_of_test P i hP h4 hi hdet hnone) hpar⟩
end
end Chazelle.Ears
namespace Chazelle.EarClip
@[expose] public section
open Chazelle.Jordan
open Chazelle.Existence
open Chazelle.Ears

/-! ### Elementary list facts -/

/-- `getD` at an in-range index is `getElem`. -/
theorem getD_eq_getElem_of_lt {α : Type} (l : List α) (d : α) {i : ℕ} (hi : i < l.length) :
    l.getD i d = l[i] := by
  simp_all

/-- `(range n).getD i 0 = i` for `i < n`. -/
theorem getD_range {n i : ℕ} (hi : i < n) : (List.range n).getD i 0 = i := by
  simp_all

/-- Two polygons with the same vertex list are equal. -/
theorem polygon_ext {P Q : Polygon} (h : P.vertices = Q.vertices) : P = Q := by
  cases P; simp_all

/-! ### The sub-polygon -/

/-- The sub-polygon of `P` on the index list `l`: vertex `j` is `P.vtx l[j]`. -/
def subPoly (P : Polygon) (l : List ℕ) : Polygon := ⟨l.map P.vtx⟩
variable (P : Polygon)
variable (l : List ℕ) {j : ℕ} (p : ℕ)
/-- The vertex list of `subPoly P l`. -/
theorem vertices_subPoly : (subPoly P l).vertices = l.map P.vtx := rfl

/-- `subPoly P l` has `l.length` vertices. -/
@[simp] theorem n_subPoly : (subPoly P l).n = l.length := by
  simp [subPoly, Polygon.n]

/-- Vertex `j < l.length` of `subPoly P l` is `P.vtx l[j]`. -/
theorem vtx_subPoly (hj : j < l.length) :
    (subPoly P l).vtx j = P.vtx l[j] := by
  simp [subPoly, Polygon.vtx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

/-- Vertex `j < l.length` of `subPoly P l` is `P.vtx (l.getD j 0)`. -/
theorem vtx_subPoly_getD (hj : j < l.length) :
    (subPoly P l).vtx j = P.vtx ztjzv := by
  rw [vtx_subPoly P l hj, getD_eq_getElem_of_lt l 0 hj]

/-- `subPoly P (List.range P.n) = P`. -/
theorem subPoly_range : subPoly P ztbyp = P := by
  zudmd

  zuhrr
  · zufan
  · zusx
    zufay
    exact getD_eq_getElem_of_lt _ _ h2

/-- Rotating the index list rotates the sub-polygon. -/
theorem subPoly_rotate (r : ℕ) :
    subPoly P zteaj = (subPoly P l).rotate r := by
  zudmd

  unfold Polygon.rotate
  zuhrr
  · simp
  · zusx
    have hi : i < l.length := by_simp_all
    simp only [List.getElem_map, List.getElem_rotate, List.getElem_range, n_subPoly]
    rw [vtx_subPoly P l ztcv, Nat.add_comm r i]

/-! ### Clipping a position -/

/-- The list with position `p` removed, starting at the predecessor `l[(p + m - 1) % m]`. -/
def clipList (l : List ℕ) (p : ℕ) : List ℕ := (l.rotate ztdpa).eraseIdx 1

/-- `clipList` for `1 ≤ p`: rotate by `p - 1` and erase position `1`. -/
theorem clipList_eq_rotate_eraseIdx {p : ℕ} (hp : 1 ≤ p) :
    clipList l p = (l.rotate ztoq).eraseIdx 1 := by
  unfold clipList
  rw [show p + l.length - 1 = ztoq + l.length by omega, ← List.rotate_mod,
    Nat.add_mod_right, List.rotate_mod]

/-- The clipped list has one element fewer. -/
theorem length_clipList (h2 : 2 ≤ l.length) :
    (clipList l p).length = l.length - 1 := by
  unfold clipList
  rw [List.length_eraseIdx_of_lt (by rw [List.length_rotate]; omega), List.length_rotate]

/-- The entries of the clipped list: position `0` is the predecessor `l[(p + m - 1) % m]`,
position `k ≥ 1` is `l[(p + k) % m]`. -/
theorem getElem?_clipList (h2 : 2 ≤ l.length) {k : ℕ}
    (hk : k < l.length - 1) :
    ztfqp[k]? =
      if k = 0 then l[ztdpa % l.length]? else l[zttvd % l.length]? := by
  unfold clipList
  rw [List.getElem?_eraseIdx]
  split_ifs with h1 h0 h0
  · zukpl
    simp_all
  · omega
  · omega
  · zukpl
    zucr
    rw [show k + 1 + ztdpa = p + k + l.length by omega, Nat.add_mod_right]

/-- `getD` version of `getElem?_clipList`. -/
theorem getD_clipList (h2 : 2 ≤ l.length) {k : ℕ}
    (hk : k < l.length - 1) (d : ℕ) :
    (clipList l p).getD k d =
      if k = 0 then l.getD ztzzj d else l.getD (zttvd % l.length) d := by
  rw [List.getD_eq_getElem?_getD, getElem?_clipList l p h2 hk]
  grind

/-- The clipped list, rotated by one (so that it starts at the successor `l[(p + 1) % m]`),
is the vertex list of `Chazelle.Ears.clip (subPoly P l) p`. -/
theorem subPoly_clipList_rotate (h3 : 3 ≤ l.length) (hp : p < l.length) :
    subPoly P ((clipList l p).rotate 1) = clip ztdi p := by
  have hlen := length_clipList l p by_omega
  zukdz
  zudmd

  unfold clip Polygon.arc
  apply List.ext_getElem?
  zugoi
  rw [List.getElem?_map, List.getElem?_map]
  by_cases hk : k < l.length - 1
  · rw [List.getElem?_range by_omega, List.getElem?_rotate by_omega, hlen,
      getElem?_clipList l p by_omega ztcv, Option.map_some,
      prevIdx_add_two_add_mod _ by_omega, hn,
      vtx_subPoly P l _]
    by_cases hk1 : k + 1 < l.length - 1
    · rw [ite_eq_right (by rw [Nat.mod_eq_of_lt hk1]; omega), Nat.mod_eq_of_lt hk1,
        List.getElem?_eq_getElem ztcv, Option.map_some,
        show p + zts = p + 1 + k by omega]
    · have hk1' : k + 1 = l.length - 1 := by_omega
      rw [hk1', Nat.mod_self, ite_eq_left rfl, List.getElem?_eq_getElem _,
        Option.map_some, show p + 1 + k = p + l.length - 1 by omega]
  · rw [List.getElem?_eq_none by_simp_all,
      List.getElem?_eq_none by_grind]
    rfl

/-- The sub-polygon of the clipped list is the clipped polygon rotated by `m - 2`. -/
theorem subPoly_clipList_eq (h3 : 3 ≤ l.length) (hp : p < l.length) :
    subPoly P ztfqp = (clip ztdi p).rotate ztocp := by
  rw [← subPoly_clipList_rotate P l p h3 hp, ← subPoly_rotate, List.rotate_rotate]
  zucr
  rw [show 1 + ztocp = (clipList l p).length by rw [length_clipList l p by_omega]; omega,
    List.rotate_length]

/-! ### Relabelling triangles -/

/-- A triangle given by positions in `l`, mapped to original indices. -/
def relabelList (l : List ℕ) (t : Polygon.Triangle) : Polygon.Triangle :=
  (l.getD t.1 0, l.getD t.2.1 0, l.getD t.2.2 0)

/-- Relabelling through `List.range n` is the identity on triangles with indices `< n`. -/
theorem relabelList_range {n : ℕ} {t : Polygon.Triangle} (h : t.1 < n ∧ t.2.1 < n ∧ t.2.2 < n) :
    relabelList ztpzu t = t := by
  zubpk
  simp only [relabelList]
  simp_all

/-- The position map from `clipList l p` (length `m - 1`) to `l` (length `m`), as a triangle
relabelling: rotate by `m - 2` (undoing the rotation of `subPoly_clipList_eq`) then embed the
clipped polygon `clip (subPoly P l) p` into `subPoly P l` via `i ↦ (p + 1 + i) % m`. -/
def clipRelabel (m p : ℕ) (t : Polygon.Triangle) : Polygon.Triangle :=
  relabel (ztr % m) m (relabel (m - 2) ztfte t)

/-- The scalar version of `clipRelabel` agrees with the entries of `clipList`. -/
theorem getD_clipList_eq (h3 : 3 ≤ l.length) {i : ℕ}
    (hi : i < l.length - 1) :
    (clipList l p).getD i 0 =
      l.getD ((ztr % l.length + (l.length - 2 + i) % ztetw) % l.length) 0 := by
  rw [getD_clipList l p by_omega hi]
  zujpn
  · zubvi
    rw [Nat.mod_eq_of_lt (by omega : l.length - 2 + 0 < l.length - 1),
      Nat.mod_add_mod, show p + 1 + (l.length - 2 + 0) = p + l.length - 1 by omega]
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ztrdi
    rw [show l.length - 2 + zts = k + ztetw by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : k < l.length - 1), Nat.mod_add_mod,
      show p + 1 + k = p + zts by omega]

/-- Relabelling a triangle of `clipList l p` to original indices, through `clipRelabel`. -/
theorem relabelList_clipRelabel (h3 : 3 ≤ l.length) {t : Polygon.Triangle}
    (ht : t.1 < l.length - 1 ∧ t.2.1 < l.length - 1 ∧ t.2.2 < l.length - 1) :
    relabelList l (clipRelabel l.length p t) = relabelList ztfqp t := by
  zubpk
  simp only [relabelList, clipRelabel, relabel_fst, relabel_snd_fst, relabel_snd_snd]
  rw [getD_clipList_eq l p h3 ht.1, getD_clipList_eq l p h3 ht.2.1, getD_clipList_eq l p h3 ht.2.2]

/-! ### Weak triangulations and rotation -/

/-- **Weak triangulations transfer along rotation**: a weak triangulation of `P.rotate s`
relabels (`relabel s P.n`) to a weak triangulation of `P`. -/
theorem weakTriangulates_rotate (s : ℕ) {T : List Polygon.Triangle}
    (hT : WeakTriangulates ztqbh T) : WeakTriangulates P (T.map ztogz) := by
  zueiy
  have hidx : ∀ t ∈ T, t.1 < P.n ∧ t.2.1 < P.n ∧ t.2.2 < P.n := by
    zucj
    zueil
    simp_all
  zuflw
  · zucj
    zurg

    exact validTriangle_rotate P s by_grind
  · rw [List.length_map, ← n_rotate P s]; omega
  · rw [← filled_rotate P s, ← hunion]
    zufj
    zuipb

    · zuekq
      exact ⟨t, ht, by rw [triSet_rotate P s by_grind]; exact hp⟩
    · zucjf
      exact ⟨_, ztbik, by rw [← triSet_rotate P s by_grind]; exact hp⟩
  · zuczn
    zuloj
    zubto
    rw [triSet_rotate P s by_grind, triSet_rotate P s by_grind] at h
    zubh
  · zukju
    zurg

    obtain ⟨j, hj, hji⟩ := exists_rot_index by_omega s i hi
    have e1 : P.vtx i = (P.rotate s).vtx j := by rw [vtx_rotate P s hj, hji]
    rw [e1, ← triSet_rotate P s by_grind] at hmem
    rw [e1, ← triVertices_rotate P s by_grind]
    exact hvert t' ht' j (by rw [n_rotate]; exact hj) hmem

/-! ### The clipping step for sub-polygons -/

/-- **Ear clipping on index lists.**  If position `p` of `l` is an ear of `Q = subPoly P l`
and `T` weakly triangulates `subPoly P (clipList l p)` (triangles in positions of
`clipList l p`), then `earTriangle Q p :: T.map (clipRelabel m p)` weakly triangulates `Q`
(triangles in positions of `l`). -/
theorem weakTriangulates_clipList (h3 : 3 ≤ l.length) (hp : p < l.length)
    (hQ : (subPoly P l).Simple) (he : IsEar ztdi p) {T : List Polygon.Triangle}
    (hT : WeakTriangulates (subPoly P ztfqp) T) :
    WeakTriangulates ztdi
      (earTriangle ztdi p :: T.map (clipRelabel l.length p)) := by
  zukdz
  have hp' : p < (subPoly P l).n := by_omega
  rw [subPoly_clipList_eq P l p h3 hp] at hT
  have h1 := weakTriangulates_rotate _ _ hT
  rw [n_clip _ _ by_omega, hn] at h1
  have h2 := weakTriangulates_clip _ _ hQ hp' he h1
  rw [List.map_map, prevIdx_add_two_mod _ hp', hn] at h2
  zucvi

/-- Simplicity of the sub-polygon of the clipped list. -/
theorem simple_subPoly_clipList (h3 : 3 ≤ l.length) (hp : p < l.length)
    (hQ : (subPoly P l).Simple) (he : IsEar ztdi p) :
    (subPoly P ztfqp).Simple := by
  rw [subPoly_clipList_eq P l p h3 hp]
  exact simple_rotate _ _ (simple_clip _ _ hQ he)
open Chazelle.Geometry (lerp)
theorem prevIdx_subPoly :
    prevIdx ztdi p = ztdpa % l.length := by
  unfold prevIdx; simp

/-- `getD` of a rotated list. -/
theorem getD_rotate (l : List ℕ) (r k : ℕ) (hk : k < l.length) (d : ℕ) :
    (l.rotate r).getD k d = l.getD (zttqd % l.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_rotate hk]

/-! ### Finding an ear: scan order `1, 2, …, m - 1, 0` -/

/-! ### The algorithm -/

/-- The emitted triangle at position `p`: `(l[p-1], l[p], l[p+1])` in original indices. -/
def earTri (l : List ℕ) (p : ℕ) : Polygon.Triangle :=
  (l.getD ztzzj 0, l.getD p 0, l.getD (ztr % l.length) 0)

/-- `earTri` is the ear triangle of `subPoly P l` relabelled to original indices. -/
theorem relabelList_earTriangle :
    relabelList l (earTriangle ztdi p) = earTri l p := by
  unfold relabelList earTriangle earTri
  rw [prevIdx_subPoly, n_subPoly]

/-! ### The invariant -/

/-! ### Correctness -/
end
end Chazelle.EarClip
@[expose] public section
namespace Chazelle.Mountain
open Chazelle

/-- Strict `(y, x)`-lexicographic order: smaller height, or equal height and smaller abscissa. -/
def ylexLT (p q : Point) : Prop := p.2 < q.2 ∨ (p.2 = q.2 ∧ p.1 < q.1)

/-- Non-strict `(y, x)`-lexicographic order. -/
def ylexLE (p q : Point) : Prop := p.2 < q.2 ∨ (p.2 = q.2 ∧ p.1 ≤ q.1)
theorem ylexLE_refl (p : Point) : ylexLE p p := Or.inr ⟨rfl, le_rfl⟩
variable {p q : Point}
theorem ylexLE_of_ylexLT (h : ylexLT p q) : ylexLE p q := by
  zulv
  · tauto
  · exact Or.inr ⟨h1, h2.le⟩
theorem ylexLT_trans {p q r : Point} (h₁ : ylexLT p q) (h₂ : ylexLT q r) : ylexLT p r := by
  rcases h₁ with h₁ | ⟨h₁, h₁'⟩ <;> rcases h₂ with h₂ | ⟨h₂, h₂'⟩
  · exact Or.inl (h₁.trans h₂)
  · exact Or.inl (h₂ ▸ h₁)
  · exact Or.inl (h₁ ▸ h₂)
  · exact Or.inr ⟨h₁.trans h₂, h₁'.trans h₂'⟩

/-- `ylexLT` is asymmetric with respect to `ylexLE`. -/
theorem not_ylexLE_of_ylexLT (h : ylexLT p q) : ¬ ylexLE q p := by
  zuceh
theorem ylexLT_irrefl (p : Point) : ¬ ylexLT p p := by
  rintro (h | ⟨_, h⟩) <;> exact lt_irrefl _ h
theorem ylexLT_asymm (h : ylexLT p q) : ¬ ylexLT q p := by
  zuceh

/-- `ylexLT` is a strict total order. -/
theorem ylexLT_trichotomy (p q : Point) : ylexLT p q ∨ p = q ∨ ylexLT q p := by
  rcases lt_trichotomy p.2 q.2 with h | h | h
  · tauto
  · rcases lt_trichotomy p.1 q.1 with h' | h' | h'
    · exact Or.inl (Or.inr ztfwk)
    · grind
    tauto
  tauto
theorem ylexLT_of_snd_lt (h : p.2 < q.2) : ylexLT p q := Or.inl h
end Chazelle.Mountain
end
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
  ∀ᶠ δ in 𝓝[>] (0 : ℝ), leftPoint P 0 ztcn δ ∈ P.filled
open Classical in
/-- The orientation sign of a polygon: `1` when the interior is on the left of the edges,
`-1` when it is on the right. -/
noncomputable def orient (P : Polygon) : ℝ := if LeftInside P then 1 else -1
variable (P : Polygon)

/-- The orientation is `1` or `-1`. -/
theorem orient_eq : orient P = 1 ∨ orient P = -1 := by
  unfold orient; grind
theorem orient_ne_zero : orient P ≠ 0 := by
  rcases orient_eq P with h | h <;> zvmwc <;> norm_num

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
      offset ztdn ztwir t ztrue ∈ P.filled \ P.boundary ∧
      offset ztdn ztwir t (-ztrue) ∉ P.filled := by
  zuoo
  obtain ⟨cL, cR, hcL, hcR, hne, -, hsides⟩ := two_components hP
  have h0 := hsides 0 by_omega ztcn by_grind
  have hi' := hsides i hi t ht
  have hLI : LeftInside P ↔ parity P cL = true := by
    constructor
    · zuq
      obtain ⟨δ, h1, h2⟩ := (h.and h0).exists
      unfold leftPoint at h1
      have hb : offset _ _ _ δ ∉ P.boundary :=
        connectedComponentIn_subset _ _ h2.1
      rw [mem_filled_iff hP hb] at h1
      rw [← parity_eq_of_mem_connectedComponentIn P h2.1]
      zubvv
    · zuq
      filter_upwards [h0] with δ hδ
      unfold leftPoint
      rw [mem_filled_iff hP (connectedComponentIn_subset _ _ hδ.1),
        parity_eq_of_mem_connectedComponentIn P hδ.1]
      zubh
  filter_upwards [hi'] with δ hδ
  have hb1 : offset _ _ t δ ∉ P.boundary :=
    connectedComponentIn_subset _ _ hδ.1
  have hb2 : offset _ _ t _ ∉ P.boundary :=
    connectedComponentIn_subset _ _ hδ.2
  have hp1 := parity_eq_of_mem_connectedComponentIn P hδ.1
  have hp2 := parity_eq_of_mem_connectedComponentIn P hδ.2
  unfold orient
  split_ifs with hL
  · have hpL := hLI.1 hL
    have hpR : ztslb := by
      grind
    zugwu
    refine ⟨⟨(mem_filled_iff hP hb1).2 by_grind, hb1⟩, ?_⟩
    zuhgo
    rw [mem_filled_iff hP hb2, hp2, hpR] at hf
    simp_all
  · have hpL : parity P cL = false := by
      grind
    have hpR : ztslc := by
      grind
    simp only [neg_one_mul, neg_neg]
    refine ⟨⟨(mem_filled_iff hP hb2).2 by_grind, hb2⟩, ?_⟩
    zuhgo
    rw [mem_filled_iff hP hb1, hp1, hpL] at hf
    simp_all

/-- **The orientation is determined by any edge**: if for arbitrarily small `δ > 0` the point
of edge `i` at parameter `t ∈ (0,1)` pushed by `σ * δ` (`σ = ±1`) is filled, then
`orient P = σ`. -/
theorem orient_eq_of_frequently {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : ∃ᶠ δ in 𝓝[>] (0 : ℝ),
      offset ztdn ztwir t ztye ∈ P.filled) :
    orient P = σ := by
  zuct
  have hσ' : σ = -orient P := by
    zuies
    · simp_all
    omega
  obtain ⟨δ, h1, h2⟩ := (h.and_eventually (eventually_offset_orient hP hi ht)).exists
  simp_all

/-- Variant of `orient_eq_of_frequently` with an `eventually` hypothesis. -/
theorem orient_eq_of_eventually {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      offset ztdn ztwir t ztye ∈ P.filled) :
    orient P = σ :=
  orient_eq_of_frequently hP hi ht hσ h.frequently

/-- **Orientation transfers along a shared edge.**  If `Q` and `P` are simple, the directed
edge `i` of `Q` coincides with the directed edge `j` of `P`, and `Q.filled ⊆ P.filled`, then
`orient P = orient Q`. -/
theorem orient_eq_of_filled_subset {Q P : Polygon} (hQ : Q.Simple) (hP : P.Simple) {i j : ℕ}
    (hi : i < Q.n) (hj : j < P.n) (h1 : Q.vtx i = P.vtx j)
    (h2 : Q.vtx (ztg % Q.n) = P.vtx ztytc) (hsub : Q.filled ⊆ P.filled) :
    orient P = orient Q := by
  apply orient_eq_of_eventually hP hj (t := 1 / 2) ztfm ztkbs
  filter_upwards [eventually_offset_orient hQ hi (t := 1 / 2) ztfm]
    with δ hδ
  zunyn
  exact hsub hδ.1.1

/-! ### The open triangle on an edge -/

/-- **The open triangle on an edge is interior iff it is on the interior side.**  Let `a v` be
the directed edge `i` of `P`, `b` a point with `det a v b ≠ 0`, and suppose the open triangle
`a v b` avoids the boundary.  Then a point of the open triangle is filled iff
`0 < orient P * det a v b`. -/
theorem interior_triangle_mem_filled_iff {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n)
    {b : Point} (hdet : det ztdn ztwir b ≠ 0)
    (hoff : ∀ x ∈ interior ztbalb,
      x ∉ P.boundary)
    {x : Point} (hx : x ∈ interior ztbalb) :
    x ∈ P.filled ↔ 0 < orient P * det ztdn ztwir b := by
  set a := P.vtx i with ha
  set v := P.vtx ztwjy with hv
  have hav := (ne_of_det_ne_zero hdet).1
  zullj
  set D := interior ztdnd with hD
  have hconn := (convex_triangle a v b).interior.isPreconnected
  have hsub : D ⊆ P.boundaryᶜ := by_grind
  obtain ⟨σ, hσ, hpos⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ 0 < σ * det a v b := by
    grind
  -- the offset points of the edge at its midpoint, on the `σ` side, lie in the open triangle
  set W : Set Point := {y | 0 < bary₁ a v b y} ∩ {y | 0 < bary₂ a v b y} with hW
  have hWo : IsOpen W :=
    (isOpen_lt continuous_const (continuous_bary₁ a v b)).inter
      (isOpen_lt continuous_const (continuous_bary₂ a v b))
  have hmW : lerp a v ztcn ∈ W := by
    zujx
    · show 0 < bary₁ a v b _
      rw [bary₁_lerp, bary₁_vertex_left hdet, bary₁_vertex_mid]; norm_num
    · show 0 < bary₂ a v b _
      rw [bary₂_lerp, bary₂_vertex_left, bary₂_vertex_mid hdet]; norm_num
  have hev1 := eventually_offset_mem σ hWo hmW
  have hev2 := eventually_offset_orient hP hi (t := 1 / 2) ztfm
  obtain ⟨δ, hδW, hδor, hδ0⟩ := (hev1.and ztqpz).exists
  zuyx
  rw [← ha, ← hv] at hδor
  have hpD : offset a v ztcn ztye ∈ D := by
    rw [hD, mem_interior_triangle_iff hdet]
    refine ⟨hδW.1, hδW.2, ?_⟩
    unfold bary₃
    zujhs
    have e : σ * δ * sqLen a v / det a v b =
        δ * sqLen a v * (σ * det a v b) / (det a v b * det a v b) := by
      rw [div_eq_div_iff hdet by_grind]
      ring
    zui
    exact div_pos (mul_pos (mul_pos hδ0' hsq) hpos) (mul_self_pos.2 hdet)
  have hxb : x ∉ P.boundary := by_grind
  have hpar := parity_eq_of_isPreconnected P hconn hsub hx hpD
  rcases sign_eq_or_eq_neg hσ ztquj with heq | heq
  · -- the convex side is the interior side
    zufpx
    refine iff_of_true ?_ hpos
    rw [mem_filled_iff hP hxb, hpar, ← mem_filled_iff hP by_grind]
    exact hδor.1.1
  · -- the convex side is the exterior side
    zufpx
    rw [neg_mul] at hpD hpar
    refine iff_of_false ?_ by_linarith
    zuhgo
    rw [mem_filled_iff hP hxb, hpar, ← mem_filled_iff hP by_grind] at hf
    grind

/-- **A simple triangle is strictly convex on the interior side**:
`0 < orient P * det v₀ v₁ v₂`. -/
theorem orient_det_pos_of_three {P : Polygon} (hP : P.Simple) (h3 : P.n = 3) :
    0 < orient P * det ztdt ztgk ztbyw := by
  zueqx
  have h1 : ztbgo % P.n = 1 := by zvncq
  have key := interior_triangle_mem_filled_iff hP (i := 0) by_omega (b := P.vtx 2)
    by_simp_all
    (by zvmwp; intro x hx; exact not_mem_boundary_of_mem_interior_triangle P h3 hdet hx)
    (by zvmwp; exact centroid_mem_interior hdet)
  zvmwp at key
  rw [← key, filled_eq_triangle P hP h3]
  exact interior_subset (centroid_mem_interior hdet)

/-! ### Ears and convexity -/

/-- Under the "no other vertex in the closed corner triangle" hypothesis, the open corner
triangle at vertex `i` avoids the boundary. -/
theorem interior_earHull_not_mem_boundary {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n)
    (hdet : det ztwmf ztdn ztwir ≠ 0)
    (hnone : ∀ j, j < P.n → j ≠ prevIdx P i → j ≠ i → j ≠ ztg % P.n →
      P.vtx j ∉ convexHull ℝ ({P.vtx ztil, P.vtx i, P.vtx ztwjy} : Set Point))
    {x : Point}
    (hx : x ∈ interior (convexHull ℝ
      ({P.vtx ztil, P.vtx i, P.vtx ztwjy} : Set Point))) :
    x ∉ P.boundary := by
  have h3 := simple_three_le hP
  zuiz
  zujms
  have hQ := simple_rotate P i hP
  have hQn : ztlaf := by_simp_all
  zueij
  have hdetQ : ztbapt := by
    simp_all
  have hnoneQ : ∀ j, j < Q.n →
      Q.vtx j ∈ convexHull ℝ ({Q.vtx ztnv, Q.vtx 0, Q.vtx 1} : Set Point) →
        j = 0 ∨ j = 1 ∨ j = Q.n - 1 := by
    zucnf

    have hQj : ztscg := vtx_rotate P i hj
    zuksz
    zubqk
    zudlm

    refine hnone _ zthp ?_ ?_ ?_ hmem
    · zuq
      zuccn

    · zuq
      exact hj0 zthkg
    · zuq
      exact hj1 ztiam
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
    (hdet : det ztwmf ztdn ztwir ≠ 0)
    (hnone : ∀ j, j < P.n → j ≠ prevIdx P i → j ≠ i → j ≠ ztg % P.n →
      P.vtx j ∉ convexHull ℝ ({P.vtx ztil, P.vtx i, P.vtx ztwjy} : Set Point)) :
    IsEar P i ↔ 0 < orient P * det ztwmf ztdn ztwir := by
  rw [isEar_iff P i hP h4 hi]
  simp only [hdet, ne_eq, not_false_eq_true, true_and]
  rw [and_iff_right hnone]
  set a := P.vtx ztil with ha
  set v := P.vtx i with hv
  set b := P.vtx ztwjy with hb
  zudys
  set m := lerp a b _ with hm
  have hmB :=
    open_chord_not_mem_boundary_of_test P i hP h4 hi hdet hnone m
      ztdox zttsc
      zttsd
  -- barycentric coordinates of the midpoint of the chord
  have hm1 : bary₁ a v b m = 1 / 2 := by
    rw [hm, bary₁_lerp, bary₁_vertex_left hdet, bary₁_vertex_right]; ring
  have hm2 : bary₂ a v b m = 0 := by
    rw [hm, bary₂_lerp, bary₂_vertex_left, bary₂_vertex_right]; ring
  have hm3 : bary₃ a v b m = 1 / 2 := by
    rw [hm, bary₃_lerp, bary₃_vertex_left, bary₃_vertex_right hdet]; ring
  -- the segment from the midpoint towards the apex
  have hint : ∀ s ∈ Ioo (0 : ℝ) 1, lerp m v s ∈ interior ztdnd := by
    zugg
    rw [mem_interior_triangle_iff hdet]
    zusk
    · rw [bary₁_lerp, hm1, bary₁_vertex_mid]; simp_all
    · rw [bary₂_lerp, hm2, bary₂_vertex_mid hdet]; simp_all
    · rw [bary₃_lerp, hm3, bary₃_vertex_mid]; simp_all
  have hoff : ∀ x ∈ interior ztdnd, x ∉ P.boundary :=
    fun x hx => interior_earHull_not_mem_boundary hP hi hdet hnone hx
  have hS : IsPreconnected (lerp m v '' Icc (0 : ℝ) ztcn) :=
    isPreconnected_Icc.image _ (continuous_lerp m v).continuousOn
  have hSb : lerp m v '' Icc (0 : ℝ) ztcn ⊆ P.boundaryᶜ := by
    zubyg
    rcases hs.1.lt_or_eq with h0 | h0
    · exact hoff _ (hint s ⟨h0, by zunui⟩)
    · rw [← h0, lerp_zero]; tauto
  have hx1 : lerp m v _ ∈ interior _ :=
    hint ztcn ztfm
  have hpar := parity_eq_of_isPreconnected P hS hSb
    ⟨0, ⟨le_rfl, by_norm_num⟩, rfl⟩ ⟨1 / 2, ⟨by_norm_num, le_rfl⟩, rfl⟩
  rw [lerp_zero] at hpar
  -- the edge `prev i` is the directed segment `a v`
  have hprev := prevIdx_lt P hi
  have hsucc : P.vtx (ztkcj % P.n) = v := by rw [prevIdx_add_one_mod P hi]
  have key := interior_triangle_mem_filled_iff hP hprev (b := b) by_grind
    (by rw [hsucc]; omega) (x := lerp m v ztcn) by_grind
  rw [hsucc] at key
  rw [← key, hpar, ← mem_filled_iff hP (hoff _ hx1)]

/-- **Every ear apex is strictly convex on the interior side.** -/
theorem orient_det_pos_of_isEar {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n)
    (he : IsEar P i) :
    0 < orient P * det ztwmf ztdn ztwir := by
  have h4 := four_le_of_isEar P i he
  obtain ⟨hdet, hnone, -⟩ := (isEar_iff P i hP h4 hi).1 he
  exact (isEar_iff_convex_of_empty hP h4 hi hdet hnone).1 he
end
end Chazelle.Mountain
section
set_option hygiene false
local macro "zqti" : tactic => `(tactic| simp [stackList, show P.n - k = P.n - zts + 1 by omega, List.range'_succ])
local macro "zqtj" : tactic => `(tactic| obtain ⟨w₁, w₂, w₃, hw₁, hw₂, hw₃, hw, rfl⟩ := mem_convexHull_triple.1 hp)
local macro "zqtk" : tactic => `(tactic| obtain ⟨T', hT', rfl⟩ := h)
local macro "zqtl" : tactic => `(tactic| (apply List.map_congr_left; intro t ht; obtain ⟨h1, h2, h3, -⟩ := hT'.1 t ht))
set_option hygiene true

/-!
# Triangulating a monotone mountain with a stack

A polygon is a *monotone mountain* (`IsMountain`) when it is simple and its vertex chain
`v₀, v₁, …, v_{n-1}` is strictly increasing for the `(y, x)`-lexicographic order `ylexLT`; the
closing edge `v_{n-1} v₀` is the *base*.

The stack algorithm (`popLoop`, `walk`, `mountainTriangulation`): walk the chain; keep a stack
of vertex indices (top first); push `0, 1`; for `k = 2, …, n - 1`, while the stack has two
elements `c` (top) and `b` below it and the corner `(b, c, k)` is strictly convex on the interior
side (`0 < σ * det (vtx b) (vtx c) (vtx k)`, with `σ = orient P` the orientation sign), pop
`c` and emit the triangle `(b, c, k)`; then push `k`.  Every test costs one corner evaluation;
`popLoop` and `walk` return the emitted triangles, the new stack and the number of tests.

Correctness (`mountain_triangulates`): the emitted list is a triangulation.  The invariant
(`Inv`): the remaining polygon `subPoly P l`, `l = stack.reverse ++ [k, …, n - 1]`, is simple,
its index list is sorted for `ylexLT`, and its orientation is that of `P`.  Every popped corner is
an ear of the remaining polygon (`isEar_of_convex_corner`): its closed triangle contains no other
vertex because every point of the triangle is `ylexLE`-between its lowest and highest corner
(`ylexLE_of_mem_convexHull_min`, `ylexLE_of_mem_convexHull_max`), and then
`isEar_iff_convex_of_empty` applies.  The stack is a reflex chain (`ReflexIdx`), so at the last
vertex every remaining corner is convex (`convex_last_of_reflex`, via two non-adjacent ears
`exists_two_ears`) and the stack empties down to `[n - 1, 0]`.

Operation count (`mountainTests_le`): at most `2 * n` corner tests.
-/
namespace Chazelle.Mountain
@[expose] public section
open Set Filter Topology
open Chazelle.Jordan
open Chazelle.Existence
open Chazelle.Ears
open Chazelle.EarClip
open Chazelle.Geometry (lerp point_ext point_ext_iff mem_convexHull_triple add_fst add_snd
  smul_fst smul_snd)

/-- Auxiliary real inequality for the convex hull lemmas. -/
theorem hull_aux {w₂ w₃ d₂ d₃ e₂ e₃ : ℝ} (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃) (hd₂ : 0 ≤ d₂)
    (hd₃ : 0 ≤ d₃) (he₂ : d₂ = 0 → 0 ≤ e₂) (he₃ : d₃ = 0 → 0 ≤ e₃) :
    0 < w₂ * d₂ + w₃ * d₃ ∨ (w₂ * d₂ + w₃ * d₃ = 0 ∧ 0 ≤ w₂ * e₂ + w₃ * e₃) := by
  have h2 : 0 ≤ w₂ * d₂ := by_positivity
  have h3 : 0 ≤ w₃ * d₃ := by_positivity
  by_cases h : w₂ * d₂ + w₃ * d₃ = 0
  · right
    zulov
    have h2' : w₂ * d₂ = 0 := by_linarith
    have h3' : w₃ * d₃ = 0 := by_linarith
    have e2 : 0 ≤ w₂ * e₂ := by
      rcases mul_eq_zero.1 h2' with h' | h'
      · simp_all
      · exact mul_nonneg hw₂ (he₂ h')
    have e3 : 0 ≤ w₃ * e₃ := by
      rcases mul_eq_zero.1 h3' with h' | h'
      · simp_all
      · exact mul_nonneg hw₃ (he₃ h')
    linarith
  grind

/-- The data of `ylexLE a b`: the height difference is nonnegative, and when it vanishes the
abscissa difference is nonnegative. -/
theorem ylexLE_data {a b : Point} (h : ylexLE a b) :
    0 ≤ b.2 - a.2 ∧ (b.2 - a.2 = 0 → 0 ≤ b.1 - a.1) := by
  zulv
  · grind
  simp_all
variable {a b c p : Point} {l : List ℕ} {T : List Polygon.Triangle} {Q : Polygon} {σ : ℝ} {k : ℕ}
/-- **Every point of a triangle is `ylexLE`-above its lowest corner.** -/
theorem ylexLE_of_mem_convexHull_min (hab : ylexLE a b) (hac : ylexLE a c)
    (hp : p ∈ convexHull ℝ ({a, b, c} : Set Point)) : ylexLE a p := by
  zqtj
  obtain ⟨hd₂, he₂⟩ := ylexLE_data hab
  obtain ⟨hd₃, he₃⟩ := ylexLE_data hac
  have e2 : (w₁ • a + w₂ • b + w₃ • c).2 - a.2 = w₂ * ztti + w₃ * ztnwh := by
    zuhpn
  have e1 : (w₁ • a + w₂ • b + w₃ • c).1 - a.1 = w₂ * ztbco + w₃ * ztnwg := by
    zuhpm
  rcases hull_aux hw₂ hw₃ hd₂ hd₃ he₂ he₃ with h | ⟨h, h'⟩
  · left; linarith
  · zuewc

/-- **Every point of a triangle is `ylexLE`-below its highest corner.** -/
theorem ylexLE_of_mem_convexHull_max (hac : ylexLE a c) (hbc : ylexLE b c)
    (hp : p ∈ convexHull ℝ ({a, b, c} : Set Point)) : ylexLE p c := by
  zqtj
  obtain ⟨hd₁, he₁⟩ := ylexLE_data hac
  obtain ⟨hd₂, he₂⟩ := ylexLE_data hbc
  have e2 : c.2 - (w₁ • a + w₂ • b + w₃ • c).2 = w₁ * ztnwh + w₂ * (c.2 - b.2) := by
    zuhpn
  have e1 : c.1 - (w₁ • a + w₂ • b + w₃ • c).1 = w₁ * ztnwg + w₂ * (c.1 - b.1) := by
    zuhpm
  rcases hull_aux hw₁ hw₂ hd₁ hd₂ he₁ he₂ with h | ⟨h, h'⟩
  · left; linarith
  · zuewc

/-! ### List helpers -/

/-- `getD` of a reversed list. -/
theorem getD_reverse (s : List ℕ) {i : ℕ} (hi : i < s.length) :
    s.reverse.getD i 0 = s.getD ztqvy 0 := by
  grind

/-- `getD` on the left part of an append. -/
theorem getD_append_of_lt (A B : List ℕ) {i : ℕ} (hi : i < A.length) :
    (A ++ B).getD i 0 = A.getD i 0 := by
  grind

/-- `getD` on the right part of an append. -/
theorem getD_append_of_le (A B : List ℕ) {i : ℕ} (hi : A.length ≤ i) :
    (A ++ B).getD i 0 = B.getD (i - A.length) 0 := by
  grind

/-- The entry of `A ++ x :: B` at position `A.length + i` is the entry of `x :: B` at `i`. -/
theorem getD_append_cons (A : List ℕ) (x : ℕ) (B : List ℕ) (i : ℕ) :
    (A ++ x :: B).getD (A.length + i) 0 = (x :: B).getD i 0 := by
  grind

/-- The entry of `A ++ x :: B` at position `A.length` is `x`. -/
theorem getD_append_length (A : List ℕ) (x : ℕ) (B : List ℕ) :
    (A ++ x :: B).getD A.length 0 = x := by
  simp

/-- An in-range `getD` entry is a member. -/
theorem getD_mem (l : List ℕ) {i : ℕ} (hi : i < l.length) : l.getD i 0 ∈ l := by
  simp_all

/-- In a `Nodup` list, equal in-range entries have equal positions. -/
theorem getD_inj_of_nodup {l : List ℕ} (hnd : l.Nodup) {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) (h : l.getD i 0 = l.getD j 0) : i = j := by
  simp_all

/-- Rotating forward by `r` and then by `l.length - r % l.length` is the identity. -/
theorem rotate_rotate_cancel {α : Type} (l : List α) (r : ℕ) :
    (l.rotate r).rotate ztgkr = l := by
  rcases Nat.eq_zero_or_pos l.length with h0 | hpos
  · simp_all
  · rw [List.rotate_rotate]
    have hmod := Nat.mod_lt r hpos
    have hdiv := Nat.div_add_mod r l.length
    have e : r + ztgkr = l.length * ztqvc := by
      grind
    simp_all

/-- The clipped list of `A ++ b :: c :: B` at the position of `c` is `A ++ b :: B`, rotated by
`A.length`. -/
theorem clipList_append_cons_cons (A : List ℕ) (b c : ℕ) (B : List ℕ) :
    clipList (A ++ b :: c :: B) ztfnb = (A ++ b :: B).rotate A.length := by
  rw [clipList_eq_rotate_eraseIdx _ by_omega, Nat.add_sub_cancel, List.rotate_append_length_eq,
    List.rotate_append_length_eq]
  simp

/-- The emitted triangle at the position of `c` in `A ++ b :: c :: k :: B` is `(b, c, k)`. -/
theorem earTri_append (A : List ℕ) (b c k : ℕ) (B : List ℕ) :
    earTri (A ++ b :: c :: k :: B) ztfnb = ztgfe := by
  unfold earTri
  have hlen : (A ++ b :: c :: k :: B).length = A.length + 3 + B.length := by_grind
  zujjh
  have e1 : (A.length + 1 + ztcss - 1) % ztcss =
      A.length := by
    rw [show A.length + 1 + ztcss - 1 = A.length + ztcss
      by omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
  have e2 : (A.length + 1 + 1) % ztcss = A.length + 2 :=
    Nat.mod_eq_of_lt by_omega
  rw [e1, e2, getD_append_length, getD_append_cons, getD_append_cons]
  rfl

/-! ### Relabelled weak triangulations of index lists -/

/-- `T` (in original indices) is the relabelling of a weak triangulation of `subPoly P l`. -/
def GoodTri (P : Polygon) (l : List ℕ) (T : List Polygon.Triangle) : Prop :=
  ∃ T', WeakTriangulates ztdi T' ∧ T = T'.map ztbux
variable (P : Polygon)

/-- A list with a relabelled weak triangulation has at least three entries. -/
theorem three_le_length_of_goodTri
    (h : GoodTri P l T) : 3 ≤ l.length := by
  obtain ⟨T', hT', -⟩ := h
  have hlen := hT'.2.1
  zukxw
  zulwe
  have hT0 : T' = [] := by
    rw [List.length_eq_zero_iff.symm]; omega
  have hl2 : l.length = 2 := by_omega
  have hfill := hT'.2.2.1
  rw [hT0] at hfill
  have h0 : (subPoly P l).vtx 0 ∈ (subPoly P l).filled :=
    Jordan.boundary_subset_filled _ ztojr
  grind

/-- Relabelled weak triangulations are invariant under rotation of the index list. -/
theorem goodTri_rotate (h : GoodTri P l T) (r : ℕ) :
    GoodTri P zteaj T := by
  zqtk
  set r' := l.length - r % l.length with hr'
  have hl : subPoly P l = (subPoly P zteaj).rotate r' := by
    rw [← subPoly_rotate, rotate_rotate_cancel]
  zvnen at hT'
  have h1 := weakTriangulates_rotate _ _ hT'
  refine ⟨_, h1, ?_⟩
  zuczm
  zqtl
  rw [n_rotate, n_subPoly, List.length_rotate] at h1 h2 h3
  have hm : ztmso := by_omega
  have key : ∀ i, i < l.length →
      (l.rotate r).getD ((r' + i) % l.length) 0 = l.getD i 0 := by
    zug
    rw [getD_rotate _ _ _ ztnnj, Nat.mod_add_mod,
      show r' + i + r = i + (r' + r) by ring]
    have e : r' + r = l.length * ztqvc := by
      rw [hr', Nat.mul_succ]
      have := Nat.div_add_mod r l.length
      have := Nat.mod_lt r hm
      omega
    rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  zubpk
  simp only [Function.comp, relabelList, relabel_fst, relabel_snd_fst, relabel_snd_snd,
    n_subPoly, List.length_rotate]
  simp_all

/-- The one-triangle case. -/
theorem goodTri_triangle (hQ : (subPoly P l).Simple) (h3 : l.length = 3) :
    GoodTri P l [(l.getD 0 0, l.getD 1 0, l.getD 2 0)] :=
  ⟨[ztgbu], weakTriangulates_triangle _ hQ by_simp_all, rfl⟩

/-- Clipping an ear (position `p` of `l`) extends a relabelled weak triangulation. -/
theorem goodTri_clipList {p : ℕ} (h3 : 3 ≤ l.length) (hp : p < l.length)
    (hQ : (subPoly P l).Simple) (he : IsEar ztdi p) {T : List Polygon.Triangle}
    (h : GoodTri P ztfqp T) : GoodTri P l (earTri l p :: T) := by
  zqtk
  refine ⟨earTriangle _ p :: T'.map _,
    weakTriangulates_clipList P l p h3 hp hQ he hT', ?_⟩
  rw [List.map_cons, List.map_map, relabelList_earTriangle]
  zucr
  zucfh
  zucj
  obtain ⟨h1, h2, h3', -⟩ := hT'.1 t ht
  rw [n_subPoly, length_clipList l p by_omega] at h1 h2 h3'
  exact (relabelList_clipRelabel l p h3 by_omega).symm

/-- **Popping an ear.**  If the corner at `c` in `A ++ b :: c :: k :: B` is an ear of the
sub-polygon, a relabelled weak triangulation of `A ++ b :: k :: B` extends by `(b, c, k)`. -/
theorem goodTri_pop (A : List ℕ) (b c k : ℕ) (B : List ℕ)
    (hQ : (subPoly P (A ++ b :: c :: k :: B)).Simple)
    (he : IsEar ztdpn ztfnb) {T : List Polygon.Triangle}
    (h : GoodTri P (A ++ b :: k :: B) T) :
    GoodTri P (A ++ b :: c :: k :: B) (ztgfe :: T) := by
  rw [← earTri_append A b c k B]
  apply goodTri_clipList P by_grind by_simp hQ he
  rw [clipList_append_cons_cons]
  exact goodTri_rotate P h _

/-- A relabelled weak triangulation of `List.range P.n` is a weak triangulation of `P`. -/
theorem weakTriangulates_of_goodTri_range
    (h : GoodTri P ztbyp T) : WeakTriangulates P T := by
  zqtk
  rw [subPoly_range] at hT'
  have : T'.map ztbaip = T' := by
    conv_rhs => rw [← List.map_id T']
    zqtl
    exact relabelList_range by_omega
  simp_all

/-! ### The invariant of the remaining polygon -/

/-- The invariant of the remaining polygon `subPoly P l`: distinct valid indices, at least
three of them, a simple polygon, sorted for `ylexLT`, with the orientation of `P`. -/
def Inv (l : List ℕ) : Prop :=
  l.Nodup ∧ (∀ x ∈ l, x < P.n) ∧ 3 ≤ l.length ∧ (subPoly P l).Simple ∧
  l.Pairwise (fun i j => ylexLT ztdn ztbhp) ∧ orient ztdi = orient P

/-- Simplicity of a sub-polygon transfers back along a rotation of the index list. -/
theorem simple_subPoly_of_rotate {r : ℕ} (h : (subPoly P zteaj).Simple) :
    (subPoly P l).Simple := by
  have := simple_rotate _ ztgkr h
  rw [← subPoly_rotate, rotate_rotate_cancel] at this
  omega

/-- **A convex corner of a sorted remaining polygon is an ear.**  In `l = A ++ b :: c :: k :: B`
with `Inv P l` and at least four entries, if `0 < orient P * det (vtx b) (vtx c) (vtx k)` then
position `A.length + 1` (the vertex `c`) is the apex of an ear of `subPoly P l`. -/
theorem isEar_of_convex_corner (A : List ℕ) (b c k : ℕ) (B : List ℕ)
    (hI : Inv P (A ++ b :: c :: k :: B)) (h4 : 4 ≤ (A ++ b :: c :: k :: B).length)
    (hconv : 0 < orient P * det ztjkz ztyg ztjr) :
    IsEar ztdpn ztfnb := by
  obtain ⟨hnd, -, -, hQ, hsort, hor⟩ := hI
  zueej
  zucki
  set p := A.length + 1 with hp
  have hlen : ztppc := by_grind
  have hpl : p < l.length := by_omega
  have hprev : prevIdx Q p = A.length := by
    rw [hQdef, prevIdx_subPoly, hlen,
      show p + ztcss - 1 = A.length + ztcss by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
  have hsucc : ztr % Q.n = A.length + 2 := by
    rw [hQdef, n_subPoly, hlen]; exact Nat.mod_eq_of_lt by_omega
  have ea : Q.vtx ztoep = P.vtx b := by
    rw [hprev, hQdef, vtx_subPoly_getD P l by_omega, getD_append_length]
  have ev : Q.vtx p = P.vtx c := by
    rw [hQdef, vtx_subPoly_getD P l hpl, hp, getD_append_cons]; rfl
  have eb : Q.vtx ztwqx = P.vtx k := by
    rw [hsucc, hQdef, vtx_subPoly_getD P l by_omega, getD_append_cons]; rfl
  have hdet : det (Q.vtx ztoep) (Q.vtx p) (Q.vtx ztwqx) ≠ 0 := by
    rw [ea, ev, eb]; intro h; simp_all
  -- the lexicographic facts
  have hpair := hsort
  rw [hl, List.pairwise_append] at hpair
  obtain ⟨-, hrest, hcross⟩ := hpair
  zugcf
  obtain ⟨hb, hrest⟩ := hrest
  zugcf
  obtain ⟨hc, hrest⟩ := hrest
  zugcf
  obtain ⟨hk, -⟩ := hrest
  have hbc := ylexLE_of_ylexLT (hb c by_simp)
  have hbk := ylexLE_of_ylexLT (hb k by_simp)
  have hck := ylexLE_of_ylexLT (hc k by_simp)
  have hnone_elem : ∀ x ∈ l, x ≠ b → x ≠ c → x ≠ k →
      P.vtx x ∉ convexHull ℝ ({P.vtx b, P.vtx c, P.vtx k} : Set Point) := by
    intro x hx hxb hxc hxk hmem
    rw [hl, List.mem_append, List.mem_cons, List.mem_cons, List.mem_cons] at hx
    rcases hx with hx | hx | hx | hx | hx
    · exact not_ylexLE_of_ylexLT (hcross x hx b by_simp)
        (ylexLE_of_mem_convexHull_min hbc hbk hmem)
    · omega
    · omega
    · omega
    · exact not_ylexLE_of_ylexLT by_grind (ylexLE_of_mem_convexHull_max hbk hck hmem)
  have hnone : ∀ j, j < Q.n → j ≠ prevIdx Q p → j ≠ p → j ≠ ztr % Q.n →
      Q.vtx j ∉ convexHull ℝ ({Q.vtx ztoep, Q.vtx p, Q.vtx ztwqx} : Set Point) := by
    intro j hj hj1 hj2 hj3
    rw [hQdef, n_subPoly] at hj
    rw [ea, ev, eb, hQdef, vtx_subPoly_getD P l hj]
    rw [hprev] at hj1
    rw [hsucc] at hj3
    refine hnone_elem _ (getD_mem l hj) ?_ ?_ ?_
    · zuq
      exact hj1 (getD_inj_of_nodup hnd hj by_omega (by rw [h, getD_append_length]))
    · zuq
      exact hj2 (getD_inj_of_nodup hnd hj hpl (by rw [h, hp, getD_append_cons]; rfl))
    · zuq
      exact hj3 (getD_inj_of_nodup hnd hj by_omega (by rw [h, getD_append_cons]; rfl))
  rw [isEar_iff_convex_of_empty hQ (by rw [hQdef, n_subPoly]; exact h4)
    (by rw [hQdef, n_subPoly]; omega) hdet hnone, ea, ev, eb, hor]
  omega

/-- The list after a pop is a sublist of the list before. -/
theorem sublist_pop (A : List ℕ) (b c k : ℕ) (B : List ℕ) :
    List.Sublist (A ++ b :: k :: B) (A ++ b :: c :: k :: B) :=
  by simp

/-- The filled region of the polygon with an ear clipped lies in the filled region. -/
theorem filled_clip_subset (hQ : Q.Simple) {p : ℕ} (hp : p < Q.n)
    (he : IsEar Q p) : (clip Q p).filled ⊆ Q.filled := by
  have hn : ztsag := by have := four_le_of_isEar Q p he; omega
  have hd := isDiagonal_compl Q _ 2 he.1
  have hin : Chazelle.segment (Q.vtx (ztqus % Q.n % Q.n))
      (Q.vtx ((ztqus % Q.n + ztnny) % Q.n)) ⊆ Q.filled := by
    rw [Nat.mod_mod, compl_arc_last_index Q _ 2 hn, prevIdx_mod Q hp,
      prevIdx_add_two_mod Q hp, segment_comm]
    exact he.2
  exact filled_arc_subset Q hQ hd hin

/-- **Popping an ear preserves the invariant.** -/
theorem inv_pop (A : List ℕ) (b c k : ℕ) (B : List ℕ) (hI : Inv P (A ++ b :: c :: k :: B))
    (h4 : 4 ≤ (A ++ b :: c :: k :: B).length)
    (he : IsEar ztdpn ztfnb) :
    Inv P (A ++ b :: k :: B) := by
  obtain ⟨hnd, hlt, -, hQ, hsort, hor⟩ := hI
  have hsub := sublist_pop A b c k B
  zueej
  set l' := A ++ b :: k :: B with hl'
  have hlen : ztppc := by zuoff; omega
  have hlen' : l'.length = A.length + 2 + B.length := by_grind
  have hQ' : (subPoly P l').Simple := by
    have := simple_subPoly_clipList P l _ by_omega by_omega hQ he
    rw [clipList_append_cons_cons] at this
    exact simple_subPoly_of_rotate P this
  refine ⟨hnd.sublist hsub, fun x hx => hlt x (hsub.subset hx), by_omega, hQ',
    hsort.sublist hsub, ?_⟩
  have hfill : (subPoly P l').filled ⊆ (subPoly P l).filled := by
    have e1 : (subPoly P l').filled = (subPoly P (clipList l ztfnb)).filled := by
      rw [clipList_append_cons_cons, subPoly_rotate, filled_rotate]
    rw [e1, subPoly_clipList_eq P l _ by_omega by_omega, filled_rotate]
    exact filled_clip_subset hQ (by zvnnk; omega) he
  have key := orient_eq_of_filled_subset hQ' hQ (i := l'.length - 1) (j := l.length - 1)
    by_simp_all by_simp_all ?_ ?_ hfill
  · simp_all
  · rw [vtx_subPoly_getD P l' by_omega, vtx_subPoly_getD P l by_omega, hlen', hlen,
      show A.length + 2 + B.length - 1 = A.length + (B.length + 1) by omega,
      show A.length + 3 + B.length - 1 = A.length + (B.length + 1 + 1) by omega,
      getD_append_cons, getD_append_cons]
    simp
  · have e1 : (l'.length - 1 + 1) % (subPoly P l').n = 0 := by
      zuhnc
    have e2 : (l.length - 1 + 1) % (subPoly P l).n = 0 := by
      zuhnc
    rw [e1, e2, vtx_subPoly_getD P l' by_omega, vtx_subPoly_getD P l by_omega]
    rcases A with _ | ⟨a, A⟩ <;> rfl

/-! ### The reflex stack -/

/-- The stack `s` (top first) is a reflex chain: every three consecutive entries
`s[i+2], s[i+1], s[i]` (in chain order) make a corner that is not strictly convex on the
interior side. -/
def ReflexIdx (σ : ℝ) (s : List ℕ) : Prop :=
  ∀ i, i + 2 < s.length →
    σ * det (P.vtx (s.getD ztcnn 0)) (P.vtx (s.getD ztg 0)) (P.vtx (s.getD i 0)) ≤ 0

/-- Popping the top preserves the reflex property. -/
theorem reflexIdx_pop {c : ℕ} {s : List ℕ} (h : ReflexIdx P σ (c :: s)) :
    ReflexIdx P σ s := by
  zug
  have := h ztg by_grind
  simp_all

/-- Pushing `k` preserves the reflex property provided the new top corner is not strictly
convex. -/
theorem reflexIdx_push {s : List ℕ} (h : ReflexIdx P σ s) (k : ℕ)
    (hk : ∀ c b rest, s = c :: b :: rest → σ * det ztjkz ztyg ztjr ≤ 0) :
    ReflexIdx P σ (k :: s) := by
  zug
  zubuk
  · rcases s with _ | ⟨c, s⟩
    · simp
    rcases s with _ | ⟨b, s⟩
    · simp_all
    simp_all
  · zufax
    exact h i by_grind

/-! ### Two non-adjacent ears and the last corner of a reflex chain -/

/-- **Two non-adjacent ears.**  Every simple polygon with at least four vertices has two ear
apexes `p ≠ q` that are not adjacent. -/
theorem exists_two_ears (hQ : Q.Simple) (h4 : 4 ≤ Q.n) :
    ∃ p q, p < Q.n ∧ q < Q.n ∧ IsEar Q p ∧ IsEar Q q ∧ p ≠ q ∧
      ztr % Q.n ≠ q ∧ ztfo % Q.n ≠ p := by
  obtain ⟨s, L, hd, hin⟩ := exists_diagonal hQ h4
  zudot
  have hL2 := hd.1
  have hLn := hd.2.1
  obtain ⟨k₁, hk₁0, hk₁, he₁⟩ := exists_ear_in_arc Q hQ hd hin
  have hd' := isDiagonal_compl Q s L hd
  have hin' : Chazelle.segment (Q.vtx (ztny % Q.n % Q.n))
      (Q.vtx ((ztny % Q.n + zttbm) % Q.n)) ⊆ Q.filled := by
    rw [Nat.mod_mod, compl_arc_last_index Q s L by_omega, segment_comm]; omega
  obtain ⟨k₂, hk₂0, hk₂, he₂⟩ := exists_ear_in_arc Q hQ hd' hin'
  zuihf
  refine ⟨(s + k₁) % Q.n, (s + (L + k₂)) % Q.n, Nat.mod_lt _ hn, Nat.mod_lt _ hn, he₁, he₂,
    ?_, ?_, ?_⟩
  · zuq
    have := rot_index_inj by_omega by_omega h
    omega
  · zuq
    zukxs
    have := rot_index_inj by_omega by_omega h
    omega
  · zuq
    zukxs
    rcases Nat.lt_or_ge _ Q.n with hlt | hge
    · have := rot_index_inj hlt by_omega h
      omega
    · have hEq : L + k₂ + 1 = Q.n := by_omega
      rw [hEq, Nat.add_mod_right] at h
      have := rot_index_inj (j := k₁) hn by_omega
        by_omega
      omega

/-- **The last corner of a reflex chain is convex.**  If every corner at positions
`1, …, n - 3` of a simple polygon `Q` (with `n ≥ 4`) is not strictly convex on the interior side,
then the corner at position `n - 2` is. -/
theorem convex_last_of_reflex (hQ : Q.Simple) (h4 : 4 ≤ Q.n)
    (hreflex : ∀ j, 1 ≤ j → j + 3 ≤ Q.n →
      orient Q * det ztbafe zthrw ztbaff ≤ 0) :
    0 < orient Q * det ztoxo ztbafi ztxvv := by
  have key : ∀ p, p < Q.n → IsEar Q p → p = Q.n - 2 ∨ p = 0 ∨ p = Q.n - 1 := by
    intro p hp he
    zubqk
    simp only [not_or] at hcon
    have hpos := orient_det_pos_of_isEar hQ hp he
    rw [prevIdx_eq Q hp, ite_eq_right hcon.2.1, Nat.mod_eq_of_lt by_omega] at hpos
    have := hreflex p by_omega by_omega
    linarith
  have conv : ∀ p, p < Q.n → IsEar Q p → p = Q.n - 2 →
      0 < orient Q * det ztoxo ztbafi ztxvv := by
    intro p hp he hpe
    subst hpe
    have := orient_det_pos_of_isEar hQ hp he
    rw [prevIdx_eq Q hp, ite_eq_right by_omega, Nat.mod_eq_of_lt by_omega,
      show Q.n - 2 - 1 = Q.n - 3 by omega, show Q.n - 2 + 1 = Q.n - 1 by omega] at this
    omega
  obtain ⟨p, q, hp, hq, hep, heq, hpq, hpq1, hqp1⟩ := exists_two_ears hQ h4
  rcases key p hp hep with h | h | h
  · grind
  · zugag
    · grind
    · omega
    · exfalso; apply hqp1; zunei
  · zugag
    · grind
    · exfalso; apply hpq1; zunei
    · omega

/-! ### The stack algorithm -/

/-- The index list of the remaining polygon: the stack (top first) reversed, followed by the
unprocessed vertices `k, …, n - 1`. -/
def stackList (s : List ℕ) (k : ℕ) : List ℕ := s.reverse ++ List.range' k ztnnu
theorem stackList_cons_cons (hk : k < P.n) (c b : ℕ) (rest : List ℕ) :
    stackList P (c :: b :: rest) k =
      rest.reverse ++ b :: c :: k :: List.range' zts ztzup := by
  zqti
theorem stackList_cons (hk : k < P.n) (c : ℕ) (rest : List ℕ) :
    stackList P (c :: rest) k =
      rest.reverse ++ c :: k :: List.range' zts ztzup := by
  zqti
theorem stackList_push (hk : k < P.n) (s : List ℕ) :
    stackList P (k :: s) zts = stackList P s k := by
  zqti
theorem stackList_last (hn : 1 ≤ P.n) (s : List ℕ) :
    stackList P s ztch = s.reverse ++ [P.n - 1] := by
  simp [stackList, show P.n - ztch = 1 by omega, List.range'_succ]
theorem length_stackList (s : List ℕ) (k : ℕ) :
    (stackList P s k).length = s.length + ztnnu := by
  zupej
open Classical in
/-- **The pop loop** at vertex `k`: while the stack (top first) has two entries `c, b` and the
corner `(b, c, k)` is strictly convex on the interior side, pop `c` and emit `(b, c, k)`.
Returns the emitted triangles, the new stack and the number of corner tests. -/
noncomputable def popLoop (σ : ℝ) (k : ℕ) : List ℕ → List Polygon.Triangle × List ℕ × ℕ
  | c :: b :: rest =>
    if 0 < σ * det ztjkz ztyg ztjr then
      (ztgfe :: (popLoop σ k (b :: rest)).1, (popLoop σ k (b :: rest)).2.1,
        (popLoop σ k (b :: rest)).2.2 + 1)
    else ([], c :: b :: rest, 1)
  | s => ztihs
theorem popLoop_nil (σ : ℝ) (k : ℕ) : popLoop P σ k [] = ([], [], 0) := by
  rfl
theorem popLoop_singleton (σ : ℝ) (k x : ℕ) : popLoop P σ k [x] = ([], [x], 0) := by
  rfl
open Classical in
theorem popLoop_cons_cons (σ : ℝ) (k c b : ℕ) (rest : List ℕ) :
    popLoop P σ k (c :: b :: rest) =
      if 0 < σ * det ztjkz ztyg ztjr then
        (ztgfe :: (popLoop P σ k (b :: rest)).1, (popLoop P σ k (b :: rest)).2.1,
          (popLoop P σ k (b :: rest)).2.2 + 1)
      else ([], c :: b :: rest, 1) := by
  rfl

/-- **The walk** over the vertices `k, k + 1, …, n - 1`: run the pop loop, push the vertex,
continue.  Returns the emitted triangles, the final stack and the number of corner tests. -/
noncomputable def walk (σ : ℝ) : ℕ → List ℕ → List Polygon.Triangle × List ℕ × ℕ
  | k, s =>
    if _h : k < P.n then
      ((popLoop P σ k s).1 ++ (walk σ zts (k :: (popLoop P σ k s).2.1)).1,
        (walk σ zts (k :: (popLoop P σ k s).2.1)).2.1,
        (popLoop P σ k s).2.2 + (walk σ zts (k :: (popLoop P σ k s).2.1)).2.2)
    else ztihs
termination_by k _ => P.n - k
decreasing_by all_goals omega
theorem walk_of_lt (σ : ℝ) {k : ℕ} (hk : k < P.n) (s : List ℕ) :
    walk P σ k s =
      ((popLoop P σ k s).1 ++ (walk P σ zts (k :: (popLoop P σ k s).2.1)).1,
        (walk P σ zts (k :: (popLoop P σ k s).2.1)).2.1,
        (popLoop P σ k s).2.2 + (walk P σ zts (k :: (popLoop P σ k s).2.1)).2.2) := by
  rw [walk, dite_eq_left hk]
theorem walk_of_le (σ : ℝ) {k : ℕ} (hk : P.n ≤ k) (s : List ℕ) : walk P σ k s = ztihs := by
  rw [walk, dite_eq_right by_omega]

/-- **The mountain triangulation**: the triangles emitted by the walk started with the stack
`[1, 0]` at vertex `2`, using the sign `σ` for the convexity tests. -/
noncomputable def mountainTriangulation (σ : ℝ) : List Polygon.Triangle := (walk P σ 2 [1, 0]).1

/-- The number of corner tests performed by the walk. -/
noncomputable def mountainTests (σ : ℝ) : ℕ := (walk P σ 2 [1, 0]).2.2

/-! ### Specification of the pop loop -/

/-- **Specification of the pop loop** at a vertex `k < n`, from a nonempty reflex stack `s`
whose remaining polygon satisfies the invariant: the new stack is nonempty and, with `k`
pushed, reflex; one triangle is emitted per pop; the number of tests is at most one more than
the number of pops; the invariant persists (as long as three vertices remain); and the
emitted triangles extend any relabelled weak triangulation of the new remaining polygon to one
of the old. -/
theorem popLoop_spec (hσ : σ = orient P) {k : ℕ} (hk : k < P.n) :
    ∀ s : List ℕ, s ≠ [] → Inv P ztibd → ReflexIdx P σ s →
      (popLoop P σ k s).2.1 ≠ [] ∧
      ReflexIdx P σ (k :: (popLoop P σ k s).2.1) ∧
      (popLoop P σ k s).1.length + (popLoop P σ k s).2.1.length = s.length ∧
      (popLoop P σ k s).2.2 ≤ (popLoop P σ k s).1.length + 1 ∧
      (3 ≤ (stackList P (popLoop P σ k s).2.1 k).length →
        Inv P ztkfn) ∧
      ∀ T, GoodTri P ztkfn T →
        GoodTri P ztibd ((popLoop P σ k s).1 ++ T) := by
  zumhi
  induction s with
  | nil => intro h; exact absurd rfl h
  | cons c s' ih =>
    intro _ hI hR
    zugsh
    · zujlf
      refine ⟨by_omega, ?_, by_simp, by_simp, by_simp_all, by_simp⟩
      tauto
    · rw [popLoop_cons_cons]
      split_ifs with hconv
      · -- a pop
        rw [stackList_cons_cons P hk] at hI ⊢
        set R := List.range' _ _ with hRdef
        by_cases h4 : 4 ≤ (rest.reverse ++ b :: c :: k :: R).length
        · have he := isEar_of_convex_corner P rest.reverse b c k R hI h4 by_grind
          have hI' := inv_pop P rest.reverse b c k R hI h4 he
          have hI'' : Inv P (stackList P (b :: rest) k) := by
            rw [stackList_cons P hk]; omega
          obtain ⟨h1, h2, h3, h4', h5, h6⟩ :=
            ih by_grind hI'' zttyn
          refine ⟨h1, h2, by_grind, by_grind, h5, ?_⟩
          intro T hT
          have := h6 T hT
          rw [stackList_cons P hk] at this
          rw [List.cons_append]
          exact goodTri_pop P rest.reverse b c k R hI.2.2.2.1 he this
        · -- the remaining polygon is a triangle: `rest = []`, `R = []`
          have hlen : (rest.reverse ++ b :: c :: k :: R).length = rest.length + 3 + R.length := by
            grind
          have hrest : ztpps := by
            rw [← List.length_eq_zero_iff]; omega
          have hlenR : R.length = P.n - zts := by_grind
          have hnk : P.n - k = 1 := by_omega
          subst hrest
          zujlf
          refine ⟨by_simp, ?_, by_simp, by_simp, ?_, ?_⟩
          · tauto
          · intro h3; rw [length_stackList, hnk] at h3; grind
          · intro T hT
            have := three_le_length_of_goodTri P hT
            rw [length_stackList, hnk] at this; grind
      · -- no pop
        refine ⟨by_omega, ?_, by_simp, by_simp, by_grind, by_simp⟩
        refine reflexIdx_push P hR k ?_
        grind

/-- **The pop loop at the last vertex empties the stack**: from a reflex stack with at least
two entries whose remaining polygon (with the last vertex `n - 1`) satisfies the invariant,
the loop pops everything but the bottom, and the emitted triangles form a relabelled weak
triangulation of the remaining polygon. -/
theorem popLoop_last (hσ : σ = orient P) :
    ∀ s : List ℕ, 2 ≤ s.length → Inv P ztznx → ReflexIdx P σ s →
      (popLoop P σ ztch s).2.1.length = 1 ∧
      GoodTri P ztznx (popLoop P σ ztch s).1 := by
  zumhi
  induction s with
  | nil => intro h; simp at h
  | cons c s' ih =>
    intro hlen hI hR
    zugsh
    · simp_all
    have hn : ztgag := by
      have := hI.2.1 b (by zupej)
      omega
    have hk : P.n - 1 < P.n := by_omega
    have hl : stackList P (c :: b :: rest) ztch = rest.reverse ++ b :: c :: [P.n - 1] := by
      zuimo
    have hl' : stackList P (b :: rest) ztch = rest.reverse ++ b :: [P.n - 1] := by
      zuimo
    zvnen at hI ⊢
    have hQ : (subPoly P _).Simple := hI.2.2.2.1
    have hor : orient _ = orient P :=
      hI.2.2.2.2.2
    -- the corner `(b, c, n - 1)` is strictly convex
    have hconv : 0 < orient P * det ztjkz ztyg ztwjc := by
      zugsg
      · have h3 := orient_det_pos_of_three hQ by_simp
        rw [hor] at h3
        positivity
      · set l := (a :: rest').reverse ++ b :: c :: [P.n - 1] with hldef
        zucki
        have hlen4 : 4 ≤ l.length := by_simp_all
        zudnu
        have hreflex : ∀ j, 1 ≤ j → j + 3 ≤ Q.n →
            orient Q * det ztbafe zthrw ztbaff ≤ 0 := by
          intro j hj1 hj3
          zvmxg at hj3
          have hl2 : l = (c :: b :: a :: rest').reverse ++ [P.n - 1] := by
            simp_all
          set s := c :: b :: a :: rest' with hsdef
          have hsl : l.length = s.length + 1 := by_grind
          have hget : ∀ i, i < s.length → l.getD i 0 = s.getD ztqvy 0 := by
            grind
          rw [hQdef, vtx_subPoly_getD P l by_omega, vtx_subPoly_getD P l by_omega,
            vtx_subPoly_getD P l by_omega, hget _ by_omega, hget _ by_omega,
            hget _ by_omega, ← hQdef, hor, hσ.symm]
          have := hR (s.length - 2 - j) by_omega
          rw [show s.length - 2 - j + 2 = s.length - 1 - zthv by omega,
            show s.length - 2 - j + 1 = s.length - 1 - j by omega,
            show s.length - 2 - j = s.length - 1 - ztl by omega] at this
          omega
        have key := convex_last_of_reflex hQ by_omega hreflex
        have hlen3 : l.length = (a :: rest').reverse.length + 3 := by simp [hldef]
        rw [hor, hQn, hlen3, hQdef, vtx_subPoly_getD P l by_omega, vtx_subPoly_getD P l by_omega,
          vtx_subPoly_getD P l by_omega,
          show (a :: rest').reverse.length + 3 - 3 = (a :: rest').reverse.length by omega,
          show (a :: rest').reverse.length + 3 - 2 = (a :: rest').reverse.length + 1 by omega,
          show (a :: rest').reverse.length + 3 - 1 = (a :: rest').reverse.length + 2 by omega,
          hldef, getD_append_length, getD_append_cons, getD_append_cons] at key
        positivity
    rw [popLoop_cons_cons, ite_eq_left by_simp_all]
    zugsg
    · zujlf
      zubee
      have := goodTri_triangle P hQ (l := [b, c, P.n - 1]) rfl
      simp_all
    · have h4 : 4 ≤ ((a :: rest').reverse ++ b :: c :: [P.n - 1]).length := by_simp
      have he := isEar_of_convex_corner P (a :: rest').reverse b c _ [] hI h4 hconv
      have hI' := inv_pop P (a :: rest').reverse b c _ [] hI h4 he
      rw [← hl'] at hI'
      obtain ⟨h1, h2⟩ := ih by_simp hI' zttyn
      rw [hl'] at h2
      exact ⟨h1, goodTri_pop P _ b c _ [] hQ he h2⟩

/-! ### Specification of the walk -/

/-- **Specification of the walk** from a vertex `k < n` and a nonempty reflex stack whose
remaining polygon satisfies the invariant: the emitted triangles form a relabelled weak
triangulation of the remaining polygon, and the number of tests is at most the number of
emitted triangles plus `n - k`. -/
theorem walk_spec (hσ : σ = orient P) :
    ∀ (d k : ℕ) (s : List ℕ), P.n - k = d → k < P.n → s ≠ [] →
      Inv P ztibd → ReflexIdx P σ s →
      GoodTri P ztibd (walk P σ k s).1 ∧
      (walk P σ k s).2.2 ≤ (walk P σ k s).1.length + ztnnu := by
  intro d
  induction d with
  | zero => intro k s hd hk; omega
  | succ d ih =>
    intro k s hd hk hs hI hR
    rw [walk_of_lt P σ hk]
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := popLoop_spec P hσ hk s hs hI hR
    rcases Nat.lt_or_ge zts P.n with hk1 | hk1
    · have hI' : Inv P (stackList P (k :: (popLoop P σ k s).2.1) zts) := by
        rw [stackList_push P hk]
        apply h5
        rw [length_stackList]
        have  := List.length_pos_of_ne_nil h1
        omega
      obtain ⟨g1, g2⟩ := ih _ _ by_omega hk1 by_simp_all hI' h2
      rw [stackList_push P hk] at g1
      grind
    · obtain rfl : k = P.n - 1 := by_omega
      rw [walk_of_le P σ by_omega]
      have hs2 : 2 ≤ s.length := by
        have := hI.2.2.1
        rw [length_stackList] at this
        omega
      obtain ⟨-, g2⟩ := popLoop_last P hσ s hs2 hI hR
      grind

/-! ### Monotone mountains -/

/-- **A monotone mountain**: a simple polygon whose vertex chain `v₀, …, v_{n-1}` is strictly
increasing for the `(y, x)`-lexicographic order (the closing edge `v_{n-1} v₀` is the base). -/
def IsMountain (P : Polygon) : Prop :=
  P.Simple ∧ ∀ i, i + 1 < P.n → ylexLT ztdn (P.vtx ztg)

/-- The chain of a mountain is `ylexLT`-increasing between any two indices. -/
theorem ylexLT_of_lt (hM : IsMountain P) {i j : ℕ} (hij : i < j) (hj : j < P.n) :
    ylexLT ztdn ztbhp := by
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d + 1 := ztoov
  induction d with
  | zero => exact hM.2 i by_omega
  | succ d ihd =>
    exact ylexLT_trans by_grind
      (hM.2 _ by_omega)

/-- The initial index list `List.range P.n` satisfies the invariant. -/
theorem inv_range (hM : IsMountain P) : Inv P ztbyp := by
  zuiwu
  refine ⟨List.nodup_range, by_simp,
    by rw [List.length_range]; exact hP.1, by rw [subPoly_range]; exact hP, ?_,
    by rw [subPoly_range]⟩
  zumlo
  zuvb
  simp only [List.getElem_range]
  rw [List.length_range] at hj
  exact ylexLT_of_lt P hM hij hj

/-- The initial remaining polygon is `P` itself. -/
theorem stackList_init (h2 : 2 ≤ P.n) : stackList P [1, 0] 2 = List.range P.n := by
  obtain ⟨m, hm⟩ : ∃ m, P.n = m + 2 := ⟨P.n - 2, by_omega⟩
  simp [stackList, hm, List.range_eq_range', List.range'_succ]

/-- **Correctness and cost of the walk on a mountain** (with `σ = orient P`). -/
theorem mountain_goodTri (hM : IsMountain P) {σ : ℝ} (hσ : σ = orient P) :
    GoodTri P ztbyp ztkbd ∧
      mountainTests P σ ≤ (mountainTriangulation P σ).length + ztdfz := by
  have h3 := hM.1.1
  have := walk_spec P hσ _ 2 [1, 0] rfl by_omega by_simp
    (by rw [stackList_init P by_omega]; exact inv_range P hM)
    by_tauto
  rw [stackList_init P by_omega] at this
  tauto

/-- **The stack algorithm weakly triangulates a monotone mountain.** -/
theorem mountain_weakTriangulates (hM : IsMountain P) {σ : ℝ} (hσ : σ = orient P) :
    WeakTriangulates P ztkbd :=
  weakTriangulates_of_goodTri_range P (mountain_goodTri P hM hσ).1

/-- **The stack algorithm triangulates a monotone mountain**: for a mountain `P` and the
orientation sign `σ = orient P`, `mountainTriangulation P σ` is a triangulation of `P`. -/
theorem mountain_triangulates (hM : IsMountain P) {σ : ℝ} (hσ : σ = orient P) :
    P.Triangulates ztkbd :=
  triangulates_of_weak (mountain_weakTriangulates P hM hσ)

/-- The mountain triangulation has `n - 2` triangles. -/
theorem length_mountainTriangulation (hM : IsMountain P) {σ : ℝ} (hσ : σ = orient P) :
    (mountainTriangulation P σ).length = P.n - 2 := by
  have := (mountain_weakTriangulates P hM hσ).2.1
  omega

/-- **Operation count**: the walk performs at most `2 * n - 4` corner tests. -/
theorem mountainTests_le_sub (hM : IsMountain P) {σ : ℝ} (hσ : σ = orient P) :
    mountainTests P σ ≤ 2 * P.n - 4 := by
  have h1 := (mountain_goodTri P hM hσ).2
  have h2 := length_mountainTriangulation P hM hσ
  omega

/-- **Operation count**: the walk performs at most `2 * n` corner tests. -/
theorem mountainTests_le (hM : IsMountain P) {σ : ℝ} (hσ : σ = orient P) :
    mountainTests P σ ≤ 2 * P.n := by
  have := mountainTests_le_sub P hM hσ
  omega
end
end Chazelle.Mountain
end
section
set_option hygiene false
local macro "zqbee" : tactic => `(tactic| have hQn : ztoqe := by_simp_all)
set_option hygiene true

/-!
# Splitting a sub-polygon along one interior diagonal

Sub-polygons are given as index lists `l` into a polygon `P` (`Chazelle.EarClip.subPoly P l`,
vertex `k` is `P.vtx l[k]`).  A pair `d = (a, b)` of original indices names the closed segment
`pairSeg P d` from `P.vtx a` to `P.vtx b`.

* `IsDiag P l d`: `d` is an interior diagonal of `subPoly P l`: `a ≠ b` are entries of `l`, the
  segment minus its endpoints avoids the boundary of `subPoly P l`, and the segment lies in its
  filled region.  (Non-adjacency in `l` follows: `isDiagonal_of_isDiag`.)
* `NonCross P d d'`: the two segments meet at most in common endpoints.
* `CycEdge l x y`: `x → y` is a cyclic edge of the list `l`.
* `arcList l s L = (l.rotate s).take (L + 1)`: the entries `l[s], …, l[s + L]` (cyclically);
  `subPoly P (arcList l s L) = (subPoly P l).arc s L` (`subPoly_arcList`).
* `splitFst l d = [a, …, b]` and `splitSnd l d = [b, …, a]` (cyclically along `l`): the two
  pieces of `l` cut along `d`.

## Main results

* `splitPair_split`: for a simple `subPoly P l` and `IsDiag P l d`, the two pieces satisfy the
  symmetric package `SplitPair P l d (splitFst l d) (splitSnd l d)`: both are simple, the filled
  region of `subPoly P l` is the union of theirs, these meet only on the diagonal, the boundaries
  are related as expected, every vertex of `subPoly P l` filled in a piece is a vertex of it, every
  cyclic edge of a piece is an edge of `l` or the diagonal, and the lengths add up to
  `l.length + 2`.  (Transported from `Chazelle.Existence` through `subPoly_arcList`.)
* `SplitPair.isDiag_fst`, `SplitPair.isDiag_snd`: another diagonal `d'` of `subPoly P l` not
  crossing `d` is a diagonal of the first piece when both its endpoints lie in the first piece,
  and of the second piece otherwise (its open segment is connected and lies in the union of the two
  disjoint open interiors); packaged for `splitFst`/`splitSnd` as `isDiag_split_cases`.
* `SplitPair.interior_disjoint`, `SplitPair.interior_not_mem_boundary`,
  `SplitPair.interior_not_mem_chord`, `SplitPair.interior_not_mem_filled`: the interior of a piece
  avoids the other piece, the boundary of `subPoly P l` and the diagonal.
* `weakTriangulates_split`: weak triangulations of the two pieces (in positions of the pieces)
  relabel (`relabel`) to a weak triangulation of `subPoly P l` (in positions of `l`), and
  `relabelList_relabel_fst` / `relabelList_relabel_snd` express this relabelling in original
  indices.
-/
namespace Chazelle.Split
@[expose] public section
open Set Topology
open Chazelle.Jordan (isOpen_filled_sdiff_boundary interior_filled isClosed_filled)
open Chazelle.Existence (IsDiagonal WeakTriangulates relabel)
open Chazelle.EarClip (subPoly n_subPoly vtx_subPoly vtx_subPoly_getD getD_eq_getElem_of_lt
  polygon_ext vertices_subPoly relabelList)
open Chazelle.Geometry (lerp continuous_lerp lerp_mem_segment segment_eq_image_lerp)

/-! ### Segments named by index pairs -/

/-- The closed segment joining the vertices of `P` named by an index pair. -/
def pairSeg (P : Polygon) (d : ℕ × ℕ) : Set Point := Chazelle.segment ztjla ztjlb

/-- The segment of the swapped pair is the same set. -/
theorem pairSeg_swap (P : Polygon) (d : ℕ × ℕ) : pairSeg P d.swap = pairSeg P d :=
  Chazelle.Geometry.segment_comm _ _

/-- The open segment `{lerp a b t | 0 < t < 1}`. -/
def innerSeg (a b : Point) : Set Point := lerp a b '' Ioo (0 : ℝ) 1
variable (a b : Point)
/-- The open segment lies in the closed segment. -/
theorem innerSeg_subset : innerSeg a b ⊆ Chazelle.segment a b := by
  zupc
  exact lerp_mem_segment a b ht.1.le ht.2.le

/-- A point of the open segment is neither endpoint (for distinct endpoints). -/
theorem ne_of_mem_innerSeg {a b p : Point} (hab : a ≠ b) (hp : p ∈ innerSeg a b) :
    p ≠ a ∧ p ≠ b := by
  obtain ⟨t, ht, rfl⟩ := hp
  exact ⟨Chazelle.Jordan.lerp_ne_left hab ht.1, Chazelle.Jordan.lerp_ne_right hab ht.2⟩

/-- A point of the closed segment other than the endpoints is in the open segment. -/
theorem mem_innerSeg_of_ne {a b p : Point} (hp : p ∈ Chazelle.segment a b) (ha : p ≠ a)
    (hb : p ≠ b) : p ∈ innerSeg a b := by
  obtain ⟨t, h0, h1, rfl⟩ := hp
  refine ⟨t, ⟨lt_of_le_of_ne h0 ?_, lt_of_le_of_ne h1 ?_⟩, rfl⟩
  · grind
  grind

/-- The open segment is preconnected. -/
theorem isPreconnected_innerSeg : IsPreconnected zttpj :=
  isPreconnected_Ioo.image _ (continuous_lerp a b).continuousOn

/-- The open segment is nonempty. -/
theorem innerSeg_nonempty : (innerSeg a b).Nonempty :=
  ⟨lerp a b ztcn, 1 / 2, by_grind, rfl⟩

/-- The closed segment lies in the closure of the open segment. -/
theorem segment_subset_closure_innerSeg :
    Chazelle.segment a b ⊆ closure zttpj := by
  rw [segment_eq_image_lerp, ← closure_Ioo (zero_ne_one' ℝ)]
  exact image_closure_subset_closure_image (continuous_lerp a b)

/-- A segment with distinct endpoints has a point other than its endpoints. -/
theorem exists_inner_point {a b : Point} (hab : a ≠ b) :
    ∃ p ∈ Chazelle.segment a b, p ≠ a ∧ p ≠ b := by
  obtain ⟨p, hp⟩ := innerSeg_nonempty a b
  exact ⟨p, innerSeg_subset a b hp, ne_of_mem_innerSeg hab hp⟩

/-! ### Diagonals of a sub-polygon -/

/-- `d` is an interior diagonal of the sub-polygon `subPoly P l`: its endpoints are distinct
entries of `l`, its segment minus the endpoints avoids the boundary of `subPoly P l`, and its
segment lies in the filled region of `subPoly P l`. -/
def IsDiag (P : Polygon) (l : List ℕ) (d : ℕ × ℕ) : Prop :=
  d.1 ∈ l ∧ d.2 ∈ l ∧ d.1 ≠ d.2 ∧
    (∀ p ∈ pairSeg P d, p ≠ P.vtx d.1 → p ≠ P.vtx d.2 → p ∉ (subPoly P l).boundary) ∧
    pairSeg P d ⊆ (subPoly P l).filled

/-- Two index pairs are *non-crossing*: their segments meet at most in common endpoints. -/
def NonCross (P : Polygon) (d d' : ℕ × ℕ) : Prop :=
  pairSeg P d ∩ pairSeg P d' ⊆ ({P.vtx d.1, P.vtx d.2} : Set Point) ∩ {P.vtx d'.1, P.vtx d'.2}

/-- `x → y` is a cyclic edge of the index list `l`. -/
def CycEdge (l : List ℕ) (x y : ℕ) : Prop :=
  ∃ k < l.length, l.getD k 0 = x ∧ l.getD ztwnc 0 = y

/-- Each position of `l` gives a cyclic edge. -/
theorem cycEdge_self (l : List ℕ) {k : ℕ} (hk : k < l.length) :
    CycEdge l ztcak ztbamg :=
  ⟨k, hk, rfl, rfl⟩

/-! ### Vertices of a simple sub-polygon -/
variable (P : Polygon)

/-- An entry of `l` is a vertex of `subPoly P l`. -/
theorem vtx_mem_boundary_subPoly {l : List ℕ} {x : ℕ} (hx : x ∈ l) :
    P.vtx x ∈ (subPoly P l).boundary := by
  zuve
  rw [← vtx_subPoly P l hi]
  exact Chazelle.Existence.vtx_mem_boundary _ by_simp_all

/-- In a simple sub-polygon, `P.vtx` is injective on the entries of `l`. -/
theorem eq_of_vtx_eq {l : List ℕ} (hQ : (subPoly P l).Simple) {x y : ℕ} (hx : x ∈ l)
    (hy : y ∈ l) (h : P.vtx x = P.vtx y) : x = y := by
  zuve
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
  rw [← vtx_subPoly P l hi, ← vtx_subPoly P l hj] at h
  have := hQ.2.1 i j by_simp_all by_simp_all h
  simp_all

/-- A simple sub-polygon has no repeated index. -/
theorem nodup_of_simple {l : List ℕ} (hQ : (subPoly P l).Simple) : l.Nodup := by
  zujgx
  intro i j h
  have hi : (i : ℕ) < (subPoly P l).n := by_simp
  have hj : (j : ℕ) < (subPoly P l).n := by_simp
  zulvn
  apply hQ.2.1 i j hi hj
  rw [vtx_subPoly P l i.2, vtx_subPoly P l j.2]
  simp_all

/-- A simple sub-polygon has at least three entries. -/
theorem three_le_of_simple {l : List ℕ} (hQ : (subPoly P l).Simple) : 3 ≤ l.length := by
  have := hQ.1
  simp_all

/-- The vertex of `subPoly P l` at the position of an entry `x` is `P.vtx x`. -/
theorem vtx_idxOf {l : List ℕ} {x : ℕ} (hx : x ∈ l) :
    (subPoly P l).vtx ztvxw = P.vtx x := by
  rw [vtx_subPoly P l (List.idxOf_lt_length_of_mem hx), List.getElem_idxOf]

/-- `getD` at the position of an entry. -/
theorem getD_idxOf {l : List ℕ} {x : ℕ} (hx : x ∈ l) : l.getD ztvxw 0 = x := by
  simp_all

/-- The endpoints of a diagonal are distinct points. -/
theorem IsDiag.vtx_ne {l : List ℕ} (hQ : (subPoly P l).Simple) {d : ℕ × ℕ} (hd : IsDiag P l d) :
    P.vtx d.1 ≠ P.vtx d.2 :=
  fun h => hd.2.2.1 (eq_of_vtx_eq P hQ hd.1 hd.2.1 h)

/-! ### Arcs of an index list -/

/-- The entries `l[s], l[s + 1], …, l[s + L]` of `l` (indices modulo `l.length`). -/
def arcList (l : List ℕ) (s L : ℕ) : List ℕ := (l.rotate s).take ztgt

/-- An arc of length `L < l.length` has `L + 1` entries. -/
theorem length_arcList {l : List ℕ} {s L : ℕ} (hL : L < l.length) :
    (arcList l s L).length = L + 1 := by
  simp only [arcList, List.length_take, List.length_rotate]
  omega

/-- Entry `k ≤ L` of `arcList l s L` is `l[(s + k) % l.length]`. -/
theorem getD_arcList {l : List ℕ} {s L k : ℕ} (hL : L < l.length) (hk : k ≤ L) :
    (arcList l s L).getD k 0 = l.getD (ztnj % l.length) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, arcList,
    List.getElem?_take_of_lt by_omega, List.getElem?_rotate by_omega, Nat.add_comm k s]

/-- Entries of an arc of `l` are entries of `l`. -/
theorem mem_of_mem_arcList {l : List ℕ} {s L x : ℕ} (h : x ∈ arcList l s L) : x ∈ l :=
  List.mem_rotate.1 (List.mem_of_mem_take h)

/-- **The sub-polygon of an arc of `l` is the arc of the sub-polygon.** -/
theorem subPoly_arcList (l : List ℕ) (s : ℕ) {L : ℕ} (hL : L < l.length) :
    subPoly P ztdll = (subPoly P l).arc s L := by
  zudmd

  unfold Polygon.arc
  zuhrr
  · rw [List.length_map, List.length_map, List.length_range, length_arcList hL]
  · intro k h1 h2
    have hk : k < L + 1 := by_simp_all
    simp only [List.getElem_map, List.getElem_range, n_subPoly]
    rw [← getD_eq_getElem_of_lt _ 0 by_simp_all,
      getD_arcList hL by_omega, vtx_subPoly_getD P l ztcv]

/-- A cyclic edge of an arc of `l` is a cyclic edge of `l`, or the closing edge from `l[s + L]`
back to `l[s]`. -/
theorem arcList_edge {l : List ℕ} {s L : ℕ} (hL : L < l.length) {k : ℕ}
    (hk : k < (arcList l s L).length) :
    CycEdge l ((arcList l s L).getD k 0)
        ((arcList l s L).getD ztygb 0) ∨
      ((arcList l s L).getD k 0 = l.getD ztwwq 0 ∧
        (arcList l s L).getD ztygb 0 = l.getD zttza 0) := by
  rw [length_arcList hL] at hk ⊢
  rcases Nat.lt_or_ge k L with hkL | hkL
  · left
    refine ⟨ztnj % l.length, Nat.mod_lt _ by_omega, (getD_arcList hL hkL.le).symm, ?_⟩
    rw [Nat.mod_eq_of_lt (by omega : k + 1 < L + 1), getD_arcList hL hkL,
      Chazelle.Existence.mod_add_one_mod]
  · right
    have hk' : k = L := by_omega
    zujpq
    rw [Nat.mod_self, getD_arcList hL le_rfl, getD_arcList hL ztbg, Nat.add_zero]
    omega

/-! ### The two pieces of a diagonal -/

/-- The length `L` of the arc of `l` from `d.1` to `d.2`: `(idx d.2 - idx d.1) mod l.length`. -/
def diagLen (l : List ℕ) (d : ℕ × ℕ) : ℕ := ztoco % l.length

/-- The first piece `[d.1, …, d.2]` (cyclically along `l`) of `l` cut along `d`. -/
def splitFst (l : List ℕ) (d : ℕ × ℕ) : List ℕ := arcList l ztvxu (diagLen l d)

/-- The second piece `[d.2, …, d.1]` (cyclically along `l`) of `l` cut along `d`. -/
def splitSnd (l : List ℕ) (d : ℕ × ℕ) : List ℕ :=
  arcList l ztvxv ztqsr

/-- Position arithmetic for a pair of distinct entries of `l`. -/
theorem diagLen_spec {l : List ℕ} {d : ℕ × ℕ} (h1 : d.1 ∈ l) (h2 : d.2 ∈ l) (hne : d.1 ≠ d.2) :
    1 ≤ diagLen l d ∧ diagLen l d < l.length ∧
      ztdvi % l.length = l.idxOf d.2 := by
  have hs := List.idxOf_lt_length_of_mem h1
  have he := List.idxOf_lt_length_of_mem h2
  have hse : l.idxOf d.1 ≠ l.idxOf d.2 := by
    zuq
    have := getD_idxOf h1
    simp_all
  have hsL : ztdvi % l.length = l.idxOf d.2 := by
    unfold diagLen
    rw [Nat.add_mod_mod, show l.idxOf d.1 + ztoco =
      l.idxOf d.2 + l.length by omega, Nat.add_mod_right, Nat.mod_eq_of_lt he]
  refine ⟨?_, Nat.mod_lt _ by_omega, hsL⟩
  zuccr
  have h0' : diagLen l d = 0 := by_omega
  rw [h0', Nat.add_zero, Nat.mod_eq_of_lt hs] at hsL
  omega
variable {P}

/-- The segment of a diagonal is not contained in an edge of the sub-polygon. -/
theorem IsDiag.not_subset_edge {l : List ℕ} (hQ : (subPoly P l).Simple) {d : ℕ × ℕ}
    (hd : IsDiag P l d) {k : ℕ} (hk : k < l.length) (h : pairSeg P d ⊆ (subPoly P l).edge k) :
    False := by
  obtain ⟨p, hp, hp1, hp2⟩ := exists_inner_point zttni
  exact hd.2.2.2.1 p hp hp1 hp2
    (Chazelle.Existence.edge_subset_boundary _ by_simp_all ztvrm)

/-- **An `IsDiag` pair is a diagonal in the sense of `Chazelle.Existence.IsDiagonal`**, at the
position `s` of its first endpoint with arc length `L` (the positions of the endpoints are given
by `hs`, `he`). -/
theorem isDiagonal_of_isDiag {l : List ℕ} (hQ : (subPoly P l).Simple) {d : ℕ × ℕ}
    (hd : IsDiag P l d) {s L : ℕ} (hsn : s < l.length) (hs : l.getD s 0 = d.1) (hL1 : 1 ≤ L)
    (hLn : L < l.length) (he : l.getD ztwwq 0 = d.2) :
    IsDiagonal ztdi s L := by
  zqbee
  have hv1 : (subPoly P l).vtx s = P.vtx d.1 := by rw [vtx_subPoly_getD P l hsn, hs]
  have hv2 : (subPoly P l).vtx ztwwq = P.vtx d.2 := by
    rw [vtx_subPoly_getD P l ztcv, he]
  zusk
  · zumv
    have hL : L = 1 := by_omega
    subst hL
    apply hd.not_subset_edge hQ hsn
    zucrd
    rw [hQn, hv1, hv2]
    rfl
  · zumv
    zvmxg at h
    have hL : L = l.length - 1 := by_omega
    have hidx : (ztny % l.length + 1) % l.length = s := by
      rw [Nat.mod_add_mod, show s + L + 1 = s + l.length by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hsn]
    apply hd.not_subset_edge hQ (Nat.mod_lt _ by_omega : ztny % l.length < l.length)
    zucrd
    rw [hQn, hidx, hv1, hv2, pairSeg, Chazelle.Geometry.segment_comm]
  · rw [hQn, Nat.mod_eq_of_lt hsn, hv1, hv2]
    exact hd.2.2.2.1

/-! ### The symmetric package of facts about the two pieces -/

/-- The facts about the two pieces `l₁`, `l₂` of `l` cut along the diagonal `d`, in a form that
is symmetric in the two pieces (`SplitPair.symm`). -/
structure SplitPair (P : Polygon) (l : List ℕ) (d : ℕ × ℕ) (l₁ l₂ : List ℕ) : Prop where
  simple₁ : (subPoly P l₁).Simple
  simple₂ : (subPoly P l₂).Simple
  cover : (subPoly P l).filled = (subPoly P l₁).filled ∪ (subPoly P l₂).filled
  meet : (subPoly P l₁).filled ∩ (subPoly P l₂).filled ⊆ pairSeg P d
  bd₁ : (subPoly P l₁).boundary ⊆ (subPoly P l).boundary ∪ pairSeg P d
  bd₂ : (subPoly P l₂).boundary ⊆ (subPoly P l).boundary ∪ pairSeg P d
  chord₁ : pairSeg P d ⊆ (subPoly P l₁).boundary
  chord₂ : pairSeg P d ⊆ (subPoly P l₂).boundary
  bd : (subPoly P l).boundary ⊆ (subPoly P l₁).boundary ∪ (subPoly P l₂).boundary
  sub₁ : ∀ x ∈ l₁, x ∈ l
  sub₂ : ∀ x ∈ l₂, x ∈ l
  vert₁ : ∀ x ∈ l, P.vtx x ∈ (subPoly P l₁).filled → x ∈ l₁
  vert₂ : ∀ x ∈ l, P.vtx x ∈ (subPoly P l₂).filled → x ∈ l₂
  edges₁ : ∀ x y, CycEdge l₁ x y → CycEdge l x y ∨ ztjw = d ∨ ztjw = d.swap
  edges₂ : ∀ x y, CycEdge l₂ x y → CycEdge l x y ∨ ztjw = d ∨ ztjw = d.swap
  len : l₁.length + l₂.length = l.length + 2

/-- The package is symmetric in the two pieces. -/
theorem SplitPair.symm {l : List ℕ} {d : ℕ × ℕ} {l₁ l₂ : List ℕ} (h : SplitPair P l d l₁ l₂) :
    SplitPair P l d l₂ l₁ where
  simple₁ := h.simple₂
  simple₂ := h.simple₁
  cover := by rw [h.cover, Set.union_comm]
  meet := by rw [Set.inter_comm]; exact h.meet
  bd₁ := h.bd₂
  bd₂ := h.bd₁
  chord₁ := h.chord₂
  chord₂ := h.chord₁
  bd := by zuoes; exact h.bd
  sub₁ := h.sub₂
  sub₂ := h.sub₁
  vert₁ := h.vert₂
  vert₂ := h.vert₁
  edges₁ := h.edges₂
  edges₂ := h.edges₁
  len := by zuocq; exact h.len

/-- **The two arcs of a diagonal form a `SplitPair`** (general positions: `s` is the position of
`d.1`, and `(s + L) % n` that of `d.2`). -/
theorem splitPair_arcs {l : List ℕ} (hQ : (subPoly P l).Simple) {d : ℕ × ℕ} (hd : IsDiag P l d)
    {s L : ℕ} (hsn : s < l.length) (hs : l.getD s 0 = d.1) (hL1 : 1 ≤ L) (hLn : L < l.length)
    (he : l.getD ztwwq 0 = d.2) :
    SplitPair P l d ztdll ztbaqa := by
  zqbee
  have hdiag : IsDiagonal _ s L := isDiagonal_of_isDiag hQ hd hsn hs hL1 hLn he
  have hv1 : (subPoly P l).vtx (s % (subPoly P l).n) = P.vtx d.1 := by
    rw [hQn, Nat.mod_eq_of_lt hsn, vtx_subPoly_getD P l hsn, hs]
  have hv2 : (subPoly P l).vtx ztwsi = P.vtx d.2 := by
    rw [hQn, vtx_subPoly_getD P l ztcv, he]
  have hchord : Chazelle.segment ztdat
      ztbald = pairSeg P d := by
    rw [hv1, hv2]; rfl
  have hin : Chazelle.segment ztdat
      ztbald ⊆ (subPoly P l).filled := by
    zuowu; exact hd.2.2.2.2
  have hn : 0 < (subPoly P l).n := by_omega
  have hLQ : L ≤ (subPoly P l).n := by_omega
  have e1 : subPoly P _ = (subPoly P l).arc s L := subPoly_arcList P l s hLn
  have e2 : subPoly P ztbaqa =
      (subPoly P l).arc ztwsi ztlzp := by
    zvmxg; exact subPoly_arcList P l _ by_omega
  have hchord' : Chazelle.segment ztbald
      ztdat = pairSeg P d := by
    zukoy
  have hchord2 : Chazelle.segment
      ((subPoly P l).vtx ((ztny % (subPoly P l).n + ztlzp) % (subPoly P l).n))
      ((subPoly P l).vtx (ztny % (subPoly P l).n % (subPoly P l).n)) = pairSeg P d := by
    simp_all
  have hmeet := Chazelle.Existence.filled_arcs_meet_on_chord _ s L hQ hdiag hin
  have hl1 := length_arcList (s := s) hLn
  have hl2 := length_arcList (l := l) (s := ztny % l.length) (L := l.length - L) by_omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => mem_of_mem_arcList hx,
    fun x hx => mem_of_mem_arcList hx, ?_, ?_, ?_, ?_, by_omega⟩
  · zvmxy; exact Chazelle.Existence.simple_arc _ s L hQ hdiag
  · zvnlz; exact Chazelle.Existence.simple_arc_compl _ s L hQ hdiag
  · zvmws; exact Chazelle.Existence.filled_eq_union_arcs _ s L hQ hdiag hin
  · rw [e1, e2, ← hchord]
    rintro p ⟨h1, h2⟩
    simp_all
  · zuohe; exact Chazelle.Existence.boundary_arc_subset _ s L hn
  · zuohf; exact Chazelle.Existence.boundary_arc_subset _ _ _ hn
  · zuohe; exact Chazelle.Existence.chord_subset_boundary_arc _ s L
  · zuohf; exact Chazelle.Existence.chord_subset_boundary_arc _ _ _
  · zvmws; exact Chazelle.Existence.boundary_subset_arcs _ s L hLQ hn
  · -- vertices of `subPoly P l` filled in the first arc
    zueac

    rw [e1, ← hxv] at hxf
    obtain ⟨k, hk, hkv⟩ := Chazelle.Existence.exists_arc_vertex_of_mem_filled _ s L hdiag hmeet
      by_omega hxf
    rw [← e1, hxv, vtx_subPoly_getD P _ by_omega] at hkv
    have hmem : (arcList l s L).getD k 0 ∈ arcList l s L := by
      simp_all
    zugfp

  · -- vertices of `subPoly P l` filled in the second arc
    zueac

    rw [e2, ← hxv] at hxf
    obtain ⟨k, hk, hkv⟩ := Chazelle.Existence.exists_arc_compl_vertex_of_mem_filled _ s L hdiag
      hmeet by_omega hxf
    rw [← e2, hxv, vtx_subPoly_getD P _ by_omega] at hkv
    have hmem : (arcList l ztwwq ztfsy).getD k 0 ∈
        arcList l ztwwq ztfsy := by
      rw [getD_eq_getElem_of_lt _ _ by_omega]
      simp
    zugfp

  · -- edges of the first arc
    zufme
    rcases arcList_edge hLn hk with h | ⟨h1, h2⟩
    · grind
    · zulw
      rw [h1, h2, Nat.mod_eq_of_lt hsn, he, hs]
      rfl
  · -- edges of the second arc
    zufme
    rcases arcList_edge by_grind hk with h | ⟨h1, h2⟩
    · grind
    · zuhl
      have hidx : (ztny % l.length + ztfsy) % l.length = s := by
        rw [Nat.mod_add_mod, show s + L + ztfsy = s + l.length by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hsn]
      rw [h1, h2, hidx, Nat.mod_mod, he, hs]

/-- Index facts for `splitFst` / `splitSnd`. -/
theorem splitSnd_eq {l : List ℕ} {d : ℕ × ℕ} (h1 : d.1 ∈ l) (h2 : d.2 ∈ l) (hne : d.1 ≠ d.2) :
    splitSnd l d = arcList l (ztdvi % l.length) ztqsr := by
  rw [(diagLen_spec h1 h2 hne).2.2]; rfl

/-- **Splitting along a diagonal.**  For a simple `subPoly P l` and a diagonal `d`, the pieces
`splitFst l d = [d.1, …, d.2]` and `splitSnd l d = [d.2, …, d.1]` form a `SplitPair`. -/
theorem splitPair_split {l : List ℕ} (hQ : (subPoly P l).Simple) {d : ℕ × ℕ} (hd : IsDiag P l d) :
    SplitPair P l d ztbhc ztbno := by
  zubxn
  rw [splitSnd_eq hd.1 hd.2.1 hd.2.2.1]
  exact splitPair_arcs hQ hd ztuzo ztvrh hL1 hLn
    ztlic

/-! ### Consequences of the package -/
section Consequences
variable {l : List ℕ} {d : ℕ × ℕ} {l₁ l₂ : List ℕ}

/-- The filled region of the first piece lies in that of `subPoly P l`. -/
theorem SplitPair.filled_subset (h : SplitPair P l d l₁ l₂) :
    (subPoly P l₁).filled ⊆ (subPoly P l).filled := by
  rw [h.cover]; simp

/-- The interior of the first piece does not meet the filled region of the second. -/
theorem SplitPair.interior_not_mem_filled (h : SplitPair P l d l₁ l₂) {p : Point}
    (hp : p ∈ interior (subPoly P l₁).filled) : p ∉ (subPoly P l₂).filled := by
  zueym
  intro hp2
  exact hp.2 ztqov

/-- The interior of the first piece avoids the diagonal. -/
theorem SplitPair.interior_not_mem_chord (h : SplitPair P l d l₁ l₂) {p : Point}
    (hp : p ∈ interior (subPoly P l₁).filled) : p ∉ pairSeg P d := by
  zueym
  exact fun hc => hp.2 (h.chord₁ hc)

/-- The interior of the first piece avoids the boundary of `subPoly P l`. -/
theorem SplitPair.interior_not_mem_boundary (h : SplitPair P l d l₁ l₂) {p : Point}
    (hp : p ∈ interior (subPoly P l₁).filled) : p ∉ (subPoly P l).boundary := by
  zuhgn
  rcases h.bd hb with h1 | h2
  · zueym
    simp_all
  · exact h.interior_not_mem_filled hp (Chazelle.Jordan.boundary_subset_filled _ h2)

/-- The open segment of another diagonal `d'` not crossing `d` lies in the open interior of one
of the two pieces (it is connected and lies in the union of the two disjoint open interiors). -/
theorem SplitPair.innerSeg_cases (h : SplitPair P l d l₁ l₂) (hQ : (subPoly P l).Simple)
    {d' : ℕ × ℕ} (hd' : IsDiag P l d') (hnc : NonCross P d d') :
    innerSeg ztmcc ztmcd ⊆ (subPoly P l₁).filled \ (subPoly P l₁).boundary ∨
      innerSeg ztmcc ztmcd ⊆ (subPoly P l₂).filled \ (subPoly P l₂).boundary := by
  zukef
  apply IsPreconnected.subset_or_subset (isOpen_filled_sdiff_boundary h.simple₁)
    (isOpen_filled_sdiff_boundary h.simple₂) ?_ ?_ (isPreconnected_innerSeg _ _)
  · zugua
    rintro p ⟨hp1, hpb1⟩ ⟨hp2, -⟩
    exact hpb1 ztqov
  · zuda
    zuiyx
    zugpo
    have hpQ := hd'.2.2.2.1 p hps hpa hpb
    have hpc : p ∉ pairSeg P d := by
      intro hpc
      rcases (hnc ⟨hpc, hps⟩).2 with e | e
      · simp_all
      simp_all
    have hpf := hd'.2.2.2.2 hps
    rw [h.cover] at hpf
    rcases hpf with hf | hf
    · left
      refine ztpfo
      rcases h.bd₁ hb with hb' | hb'
      · simp_all
      simp_all
    · right
      refine ztpfo
      rcases h.bd₂ hb with hb' | hb'
      · simp_all
      simp_all

/-- If the open segment of a diagonal `d'` of `subPoly P l` lies in the open interior of the
first piece, then `d'` is a diagonal of the first piece. -/
theorem SplitPair.isDiag_of_innerSeg_subset (h : SplitPair P l d l₁ l₂) {d' : ℕ × ℕ}
    (hd' : IsDiag P l d')
    (hsub : innerSeg ztmcc ztmcd ⊆
      (subPoly P l₁).filled \ (subPoly P l₁).boundary) :
    IsDiag P l₁ d' := by
  have hseg : pairSeg P d' ⊆ (subPoly P l₁).filled := by
    zuda
    have := closure_mono (hsub.trans Set.sdiff_subset) (segment_subset_closure_innerSeg _ _ hp)
    exact (isClosed_filled _).closure_subset this
  refine ⟨h.vert₁ _ hd'.1 (hseg (Chazelle.Geometry.left_mem_segment _ _)),
    h.vert₁ _ hd'.2.1 (hseg (Chazelle.Geometry.right_mem_segment _ _)), hd'.2.2.1, ?_, hseg⟩
  intro p hp hpa hpb
  exact (hsub (mem_innerSeg_of_ne hp hpa hpb)).2

/-- No diagonal `d'` not crossing `d` has both endpoints in both pieces (its segment would lie on
the segment of `d`). -/
theorem SplitPair.not_mem_both (h : SplitPair P l d l₁ l₂) (hQ : (subPoly P l).Simple)
    {d' : ℕ × ℕ} (hd' : IsDiag P l d') (hnc : NonCross P d d') (h1 : d'.1 ∈ l₁ ∧ d'.2 ∈ l₁)
    (h2 : d'.1 ∈ l₂ ∧ d'.2 ∈ l₂) : False := by
  zukef
  have hv : ∀ x, x ∈ l₁ → x ∈ l₂ → P.vtx x ∈ pairSeg P d := fun x hx1 hx2 =>
    h.meet ⟨Chazelle.Jordan.boundary_subset_filled _ (vtx_mem_boundary_subPoly P hx1),
      Chazelle.Jordan.boundary_subset_filled _ (vtx_mem_boundary_subPoly P hx2)⟩
  have hsub :=
    Chazelle.Geometry.segment_subset_of_convex (Chazelle.Geometry.segment_convex _ _)
      (hv _ h1.1 h2.1) (hv _ h1.2 h2.2)
  obtain ⟨p, hp⟩ := innerSeg_nonempty ztmcc ztmcd
  zugpo
  zuiyx
  rcases (hnc ⟨hsub hps, hps⟩).2 with e | e
  · simp_all
  simp_all

/-- **Distributing the other diagonals, first piece.**  A diagonal `d'` of `subPoly P l` not
crossing `d` whose endpoints both lie in the first piece is a diagonal of the first piece. -/
theorem SplitPair.isDiag_fst (h : SplitPair P l d l₁ l₂) (hQ : (subPoly P l).Simple)
    {d' : ℕ × ℕ} (hd' : IsDiag P l d') (hnc : NonCross P d d') (hmem : d'.1 ∈ l₁ ∧ d'.2 ∈ l₁) :
    IsDiag P l₁ d' := by
  zuhii
  · exact h.isDiag_of_innerSeg_subset hd' hs
  · have := h.symm.isDiag_of_innerSeg_subset hd' hs
    exact (h.not_mem_both hQ hd' hnc hmem ztknb).elim

/-- **Distributing the other diagonals, second piece.**  A diagonal `d'` of `subPoly P l` not
crossing `d` whose endpoints do not both lie in the first piece is a diagonal of the second
piece. -/
theorem SplitPair.isDiag_snd (h : SplitPair P l d l₁ l₂) (hQ : (subPoly P l).Simple)
    {d' : ℕ × ℕ} (hd' : IsDiag P l d') (hnc : NonCross P d d')
    (hmem : ¬ (d'.1 ∈ l₁ ∧ d'.2 ∈ l₁)) : IsDiag P l₂ d' := by
  zuhii
  · have := h.isDiag_of_innerSeg_subset hd' hs
    exact (hmem ztknb).elim
  · exact h.symm.isDiag_of_innerSeg_subset hd' hs

/-- The interiors of the filled regions of the two pieces are disjoint. -/
theorem SplitPair.interior_disjoint (h : SplitPair P l d l₁ l₂) :
    Disjoint (interior (subPoly P l₁).filled) (interior (subPoly P l₂).filled) :=
  Set.disjoint_left.2 fun _ hp hp2 => h.interior_not_mem_filled hp (interior_subset hp2)
end Consequences

/-- **Distributing a non-crossing diagonal.**  Let `subPoly P l` be simple, `d` a diagonal and
`d'` another diagonal not crossing `d`.  Either both endpoints of `d'` are entries of the first
piece `splitFst l d` and `d'` is a diagonal of it, or they are not both entries of the first piece,
both are entries of the second piece `splitSnd l d`, and `d'` is a diagonal of it. -/
theorem isDiag_split_cases {l : List ℕ} (hQ : (subPoly P l).Simple) {d d' : ℕ × ℕ}
    (hd : IsDiag P l d) (hd' : IsDiag P l d') (hnc : NonCross P d d') :
    (d'.1 ∈ splitFst l d ∧ d'.2 ∈ splitFst l d ∧ IsDiag P ztbhc d') ∨
      (¬ zterm ∧ d'.1 ∈ splitSnd l d ∧
        d'.2 ∈ splitSnd l d ∧ IsDiag P ztbno d') := by
  have hs := splitPair_split hQ hd
  by_cases hmem : d'.1 ∈ splitFst l d ∧ d'.2 ∈ splitFst l d
  · exact Or.inl ⟨hmem.1, hmem.2, hs.isDiag_fst hQ hd' hnc hmem⟩
  · have h2 := hs.isDiag_snd hQ hd' hnc hmem
    exact Or.inr ⟨hmem, h2.1, h2.2.1, h2⟩

/-! ### Combining weak triangulations of the two pieces -/

/-- The indices of the triangles of a weak triangulation are in range. -/
theorem index_lt_of_weak {Q : Polygon} {T : List Polygon.Triangle} (h : WeakTriangulates Q T)
    {t : Polygon.Triangle} (ht : t ∈ T) : t.1 < Q.n ∧ t.2.1 < Q.n ∧ t.2.2 < Q.n := by
  obtain ⟨h1, h2, h3, -⟩ := h.1 t ht
  omega

/-- **Combining along one diagonal.**  Weak triangulations `T₁` of `subPoly P (splitFst l d)` and
`T₂` of `subPoly P (splitSnd l d)` (in positions of the pieces) relabel to a weak triangulation of
`subPoly P l` (in positions of `l`): position `k` of the first piece is position
`(idx d.1 + k) % n` of `l`, position `k` of the second is `(idx d.2 + k) % n`. -/
theorem weakTriangulates_split {l : List ℕ} (hQ : (subPoly P l).Simple) {d : ℕ × ℕ}
    (hd : IsDiag P l d) {T₁ T₂ : List Polygon.Triangle}
    (h₁ : WeakTriangulates ztzya T₁)
    (h₂ : WeakTriangulates ztzyb T₂) :
    WeakTriangulates ztdi
      (T₁.map ztilz ++ T₂.map ztima) := by
  zubxn
  have hsn := List.idxOf_lt_length_of_mem hd.1
  zqbee
  have hdiag := isDiagonal_of_isDiag hQ hd hsn ztvrh hL1 hLn
    ztlic
  have hin : Chazelle.segment ((subPoly P l).vtx (l.idxOf d.1 % (subPoly P l).n))
      ((subPoly P l).vtx ztykl) ⊆
        (subPoly P l).filled := by
    rw [hQn, Nat.mod_eq_of_lt hsn, hsL, vtx_idxOf P hd.1, vtx_idxOf P hd.2.1]
    exact hd.2.2.2.2
  have e1 : subPoly P ztbhc = (subPoly P l).arc _ _ :=
    subPoly_arcList P l _ hLn
  have e2 : subPoly P ztbno = (subPoly P l).arc
      ztykl ((subPoly P l).n - diagLen l d) := by
    rw [hQn, hsL]; exact subPoly_arcList P l _ by_omega
  zvmxy at h₁
  zvnlz at h₂
  have := Chazelle.Existence.weakTriangulates_of_diagonal hQ hdiag hin h₁ h₂
  simp_all

/-- Relabelling a triangle of an arc of `l` (positions `≤ L`) to positions of `l` and then to
original indices agrees with relabelling it directly to original indices. -/
theorem relabelList_relabel_arc {l : List ℕ} {s L : ℕ} (hL : L < l.length) {t : Polygon.Triangle}
    (ht : t.1 ≤ L ∧ t.2.1 ≤ L ∧ t.2.2 ≤ L) :
    relabelList l (relabel s l.length t) = relabelList ztdll t := by
  obtain ⟨a, b, c⟩ := t
  simp only [relabelList, Chazelle.Existence.relabel_fst, Chazelle.Existence.relabel_snd_fst,
    Chazelle.Existence.relabel_snd_snd]
  rw [getD_arcList hL ht.1, getD_arcList hL ht.2.1, getD_arcList hL ht.2.2]

/-- `relabelList_relabel_arc` for the first piece. -/
theorem relabelList_relabel_fst {l : List ℕ} {d : ℕ × ℕ} (h1 : d.1 ∈ l) (h2 : d.2 ∈ l)
    (hne : d.1 ≠ d.2) {t : Polygon.Triangle}
    (ht : t.1 < (splitFst l d).length ∧ t.2.1 < (splitFst l d).length ∧
      t.2.2 < (splitFst l d).length) :
    relabelList l (relabel ztvxu l.length t) = relabelList ztbhc t := by
  obtain ⟨-, hLn, -⟩ := diagLen_spec h1 h2 hne
  have hlen : (splitFst l d).length = diagLen l d + 1 := length_arcList hLn
  zukux
  exact relabelList_relabel_arc hLn by_omega

/-- `relabelList_relabel_arc` for the second piece. -/
theorem relabelList_relabel_snd {l : List ℕ} {d : ℕ × ℕ} (h1 : d.1 ∈ l) (h2 : d.2 ∈ l)
    (hne : d.1 ≠ d.2) {t : Polygon.Triangle}
    (ht : t.1 < (splitSnd l d).length ∧ t.2.1 < (splitSnd l d).length ∧
      t.2.2 < (splitSnd l d).length) :
    relabelList l (relabel ztvxv l.length t) = relabelList ztbno t := by
  obtain ⟨hL1, hLn, -⟩ := diagLen_spec h1 h2 hne
  have hlt : l.length - diagLen l d < l.length := by_omega
  have hlen : (splitSnd l d).length = l.length - diagLen l d + 1 := length_arcList hlt
  zukux
  exact relabelList_relabel_arc hlt by_omega
end
end Chazelle.Split
end
namespace Chazelle.Split
@[expose] public section
open Set
open Chazelle.Jordan (interior_filled)
open Chazelle.Existence (WeakTriangulates relabel)
open Chazelle.EarClip (subPoly n_subPoly relabelList)

/-! ### The recursion -/

/-- Both endpoints of `d` are entries of `m` (as a Boolean test). -/
def sideTest (m : List ℕ) (d : ℕ × ℕ) : Bool := decide (d.1 ∈ m) && decide (d.2 ∈ m)
theorem sideTest_eq_true {m : List ℕ} {d : ℕ × ℕ} :
    sideTest m d = true ↔ d.1 ∈ m ∧ d.2 ∈ m := by
  simp [sideTest]

/-- The diagonals of `D` sent to the first piece of `l` cut along `d`: those with both endpoints
in `splitFst l d`. -/
def diagsFst (l : List ℕ) (d : ℕ × ℕ) (D : List ztw) : List ztw :=
  D.filter (sideTest ztbhc)

/-- The diagonals of `D` sent to the second piece of `l` cut along `d`: all the others. -/
def diagsSnd (l : List ℕ) (d : ℕ × ℕ) (D : List ztw) : List ztw :=
  D.filter (fun d' => !sideTest ztbhc d')
theorem mem_diagsFst {l : List ℕ} {d d' : ℕ × ℕ} {D : List ztw} :
    d' ∈ diagsFst l d D ↔ d' ∈ D ∧ d'.1 ∈ splitFst l d ∧ d'.2 ∈ splitFst l d := by
  rw [diagsFst, List.mem_filter, sideTest_eq_true]
theorem mem_diagsSnd {l : List ℕ} {d d' : ℕ × ℕ} {D : List ztw} :
    d' ∈ diagsSnd l d D ↔ d' ∈ D ∧ ¬ zterm := by
  rw [diagsSnd, List.mem_filter, Bool.not_eq_true', ← sideTest_eq_true, Bool.not_eq_true]

/-- **Splitting `l` along all the diagonals of `D`**: cut along the head diagonal, distribute the
remaining diagonals to the two pieces, and recurse. -/
def splitAll : List ℕ → List ztw → List ztul
  | l, [] => [l]
  | l, d :: D =>
    splitAll ztbhc ztdng ++ splitAll ztbno ztczf
termination_by _ D => D.length
decreasing_by
  all_goals
    zunxj
    zubfo

/-- **Assembling triangulations of the pieces.**  Given triangles `T m` for each piece `m` (in
positions of `m`), the triangles in positions of `l`, following the recursion of `splitAll`. -/
def combineTri (T : List ℕ → List Polygon.Triangle) :
    List ℕ → List ztw → List Polygon.Triangle
  | l, [] => T l
  | l, d :: D =>
    (combineTri T ztbhc ztdng).map ztilz ++
      (combineTri T ztbno ztczf).map ztima
termination_by _ D => D.length
decreasing_by
  all_goals
    zunxj
    zubfo
@[simp] theorem splitAll_nil (l : List ℕ) : splitAll l [] = [l] := by
  zumox
theorem splitAll_cons (l : List ℕ) (d : ℕ × ℕ) (D : List ztw) :
    splitAll l (d :: D) =
      splitAll ztbhc ztdng ++ splitAll ztbno ztczf := by
  zumox
variable (T : List ℕ → List Polygon.Triangle)
@[simp] theorem combineTri_nil (l : List ℕ) :
    combineTri T l [] = T l := by
  zummb
theorem combineTri_cons (l : List ℕ) (d : ℕ × ℕ)
    (D : List ztw) :
    combineTri T l (d :: D) =
      (combineTri T ztbhc ztdng).map ztilz ++
        (combineTri T ztbno ztczf).map ztima := by
  zummb

/-- Induction principle following the recursion of `splitAll`. -/
theorem splitAll_induction {motive : List ℕ → List ztw → Prop}
    (nil : ∀ l, motive l [])
    (cons : ∀ l d D, motive ztbhc ztdng →
      motive ztbno ztczf → motive l (d :: D)) :
    ∀ l D, motive l D := by
  suffices H : ∀ N l D, D.length ≤ N → motive l D from fun l D => H _ l D le_rfl
  intro N
  induction N with
  | zero =>
    zumhd
    cases D with
    | nil => exact nil l
    | cons d D => simp at hD
  | succ N ih =>
    zumhd
    cases D with
    | nil => exact nil l
    | cons d D =>
      rw [List.length_cons] at hD
      exact cons l d D ztitd
        ztitd

/-! ### Diagonal systems -/

/-- **A diagonal system for `(P, l)`**: `subPoly P l` is simple, every member of `D` is an
interior diagonal of it, and the members of `D` are pairwise non-crossing. -/
structure DiagSystem (P : Polygon) (l : List ℕ) (D : List ztw) : Prop where
  simple : (subPoly P l).Simple
  diag : ∀ d ∈ D, IsDiag P l d
  noncross : D.Pairwise ztvbs
variable {P : Polygon}
section System
variable {l : List ℕ} {d : ℕ × ℕ} {D : List (ℕ × ℕ)}

/-- The head diagonal of a system splits `l` into a `SplitPair`. -/
theorem DiagSystem.splitPair (h : DiagSystem P l (d :: D)) :
    SplitPair P l d ztbhc ztbno :=
  splitPair_split h.simple zttll
theorem DiagSystem.tail_isDiag (h : DiagSystem P l (d :: D)) {d' : ℕ × ℕ} (hd' : d' ∈ D) :
    IsDiag P l d' :=
  h.diag d' by_simp_all
theorem DiagSystem.tail_nonCross (h : DiagSystem P l (d :: D)) {d' : ℕ × ℕ} (hd' : d' ∈ D) :
    NonCross P d d' :=
  (List.pairwise_cons.1 h.noncross).1 d' hd'

/-- A tail diagonal whose endpoints are not both in the first piece is a diagonal of the second
piece. -/
theorem DiagSystem.isDiag_snd (h : DiagSystem P l (d :: D)) {d' : ℕ × ℕ} (hd' : d' ∈ D)
    (hmem : ¬ zterm) : IsDiag P ztbno d' :=
  h.splitPair.isDiag_snd h.simple ztvsc ztvsd hmem

/-- A tail diagonal whose endpoints are both in the first piece is a diagonal of the first
piece. -/
theorem DiagSystem.isDiag_fst (h : DiagSystem P l (d :: D)) {d' : ℕ × ℕ} (hd' : d' ∈ D)
    (hmem : d'.1 ∈ splitFst l d ∧ d'.2 ∈ splitFst l d) : IsDiag P ztbhc d' :=
  h.splitPair.isDiag_fst h.simple ztvsc ztvsd hmem

/-- The system passes to the first piece. -/
theorem DiagSystem.fst (h : DiagSystem P l (d :: D)) :
    DiagSystem P ztbhc ztdng where
  simple := h.splitPair.simple₁
  diag d' hd' := by
    rw [mem_diagsFst] at hd'
    exact h.isDiag_fst hd'.1 hd'.2
  noncross := (List.pairwise_cons.1 h.noncross).2.filter _

/-- The system passes to the second piece. -/
theorem DiagSystem.snd (h : DiagSystem P l (d :: D)) :
    DiagSystem P ztbno ztczf where
  simple := h.splitPair.simple₂
  diag d' hd' := by
    rw [mem_diagsSnd] at hd'
    exact h.isDiag_snd hd'.1 hd'.2
  noncross := (List.pairwise_cons.1 h.noncross).2.filter _
end System

/-! ### The pieces -/

/-- The properties of an output piece `m` of splitting `l` along `D`. -/
structure PieceOf (P : Polygon) (l : List ℕ) (D : List ztw) (m : List ℕ) : Prop where
  simple : (subPoly P m).Simple
  sub : ∀ x ∈ m, x ∈ l
  edges : ∀ k < m.length, CycEdge l (m.getD k 0) (m.getD ztyte 0) ∨
    (m.getD k 0, m.getD ztyte 0) ∈ D ∨
      (m.getD ztyte 0, m.getD k 0) ∈ D
  not_boundary : ∀ p ∈ interior (subPoly P m).filled, p ∉ (subPoly P l).boundary
  not_diag : ∀ d ∈ D, ∀ p ∈ interior (subPoly P m).filled, p ∉ pairSeg P d
  filled_subset : (subPoly P m).filled ⊆ (subPoly P l).filled

/-- With no diagonals, `l` itself is the piece. -/
theorem pieceOf_self {l : List ℕ} (hQ : (subPoly P l).Simple) : PieceOf P l [] l where
  simple := hQ
  sub _ h := h
  edges k hk := Or.inl (cycEdge_self l hk)
  not_boundary p hp := by
    rw [interior_filled hQ] at hp
    simp_all
  not_diag _ h := absurd h List.not_mem_nil
  filled_subset := subset_rfl

/-- **Lifting a piece through one split.**  A piece of the first piece `l₁` of `l` cut along `d`,
for a diagonal list `D₁ ⊆ D` such that the diagonals of `D` not in `D₁` lie in the second piece,
is a piece of `l` for `d :: D`. -/
theorem PieceOf.lift {l l₁ l₂ : List ℕ} {d : ℕ × ℕ} {D D₁ : List ztw}
    (hs : SplitPair P l d l₁ l₂) (hsub : ∀ d' ∈ D₁, d' ∈ D)
    (hrest : ∀ d' ∈ D, d' ∉ D₁ → pairSeg P d' ⊆ (subPoly P l₂).filled)
    {m : List ℕ} (hm : PieceOf P l₁ D₁ m) : PieceOf P l (d :: D) m where
  simple := hm.simple
  sub x hx := hs.sub₁ x (hm.sub x hx)
  edges k hk := by
    rcases hm.edges k hk with h | h | h
    · rcases hs.edges₁ _ _ h with h' | h' | h'
      · simp_all
      · simp_all
      grind
    · simp_all
    simp_all
  not_boundary p hp :=
    hs.interior_not_mem_boundary (interior_mono hm.filled_subset hp)
  not_diag d' hd' p hp := by
    have hp₁ := interior_mono hm.filled_subset hp
    rcases List.mem_cons.1 hd' with rfl | hd'
    · exact hs.interior_not_mem_chord hp₁
    · by_cases h₁ : d' ∈ D₁
      · exact hm.not_diag d' h₁ p hp
      · exact fun h => hs.interior_not_mem_filled hp₁ by_grind
  filled_subset := hm.filled_subset.trans hs.filled_subset

/-- **Properties of the output pieces.**  Every piece `m` of `splitAll l D`, for a diagonal
system `D` of `(P, l)`, is a simple sub-polygon whose entries are entries of `l`, whose cyclic
edges are cyclic edges of `l` or members of `D` (in either orientation), whose interior avoids the
boundary of `subPoly P l` and every segment of `D`, and whose filled region lies in that of
`subPoly P l`. -/
theorem pieceOf_splitAll {l : List ℕ} {D : List ztw} (h : DiagSystem P l D) :
    ∀ m ∈ splitAll l D, PieceOf P l D m := by
  revert h
  refine splitAll_induction (motive := fun l D => DiagSystem P l D →
    ∀ m ∈ splitAll l D, PieceOf P l D m) ?_ ?_ l D
  · intro l h m hm
    rw [splitAll_nil, List.mem_singleton] at hm
    subst hm
    exact pieceOf_self h.simple
  · intro l d D ih₁ ih₂ h m hm
    rw [splitAll_cons, List.mem_append] at hm
    rcases hm with hm | hm
    · refine (ih₁ h.fst m hm).lift h.splitPair (fun d' hd' => (mem_diagsFst.1 hd').1) ?_
      zumgp
      rw [mem_diagsFst, not_and] at hn
      exact (h.isDiag_snd hd' ztvvr).2.2.2.2
    · refine (ih₂ h.snd m hm).lift h.splitPair.symm (fun d' hd' => (mem_diagsSnd.1 hd').1) ?_
      zumgp
      rw [mem_diagsSnd, not_and, not_not] at hn
      exact (h.isDiag_fst hd' ztvvr).2.2.2.2

/-! ### Combining triangulations -/

/-- **Combination.**  If every piece `m` of `splitAll l D` (for a diagonal system `D`) is weakly
triangulated by `T m` (in positions of `m`), then `combineTri T l D` weakly triangulates
`subPoly P l` (in positions of `l`). -/
theorem weakTriangulates_combineTri {l : List ℕ} {D : List ztw} (h : DiagSystem P l D)
    {T : List ℕ → List Polygon.Triangle}
    (hT : ∀ m ∈ splitAll l D, WeakTriangulates ztevt ztjng) :
    WeakTriangulates ztdi (combineTri T l D) := by
  revert h hT
  refine splitAll_induction (motive := fun l D => DiagSystem P l D →
    ztybo →
      WeakTriangulates ztdi _) ?_ ?_ l D
  · simp
  · zuibx
    rw [combineTri_cons]
    exact weakTriangulates_split h.simple zttll
      (ih₁ h.fst fun m hm => hT m zteqc)
      (ih₂ h.snd fun m hm => hT m zteqc)

/-- **The combined triangulation in original indices** is the concatenation, over the pieces
`m` of `splitAll l D`, of the triangles `T m` relabelled to original indices by
`relabelList m`. -/
theorem map_relabelList_combineTri {l : List ℕ} {D : List ztw} (h : DiagSystem P l D)
    {T : List ℕ → List Polygon.Triangle}
    (hT : ∀ m ∈ splitAll l D, WeakTriangulates ztevt ztjng) :
    (combineTri T l D).map ztbux =
      (splitAll l D).flatMap zteci := by
  revert h hT
  refine splitAll_induction (motive := fun l D => DiagSystem P l D →
    ztybo →
      (combineTri T l D).map ztbux =
        (splitAll l D).flatMap zteci) ?_ ?_ l D
  · simp
  · zuibx
    zukbq
    have hT₁ : ∀ m ∈ splitAll ztbhc ztdng,
        WeakTriangulates _ _ :=
      fun m hm => hT m zteqc
    have hT₂ : ∀ m ∈ splitAll ztbno ztczf,
        WeakTriangulates _ _ :=
      fun m hm => hT m zteqc
    have hw₁ := weakTriangulates_combineTri h.fst hT₁
    have hw₂ := weakTriangulates_combineTri h.snd hT₂
    rw [combineTri_cons, splitAll_cons, List.flatMap_append, List.map_append, List.map_map,
      List.map_map, ← ih₁ h.fst hT₁, ← ih₂ h.snd hT₂]
    zucr
    · zucfh
      zucj
      have hb := index_lt_of_weak hw₁ ht
      zukxv
      exact relabelList_relabel_fst hd.1 hd.2.1 hd.2.2.1 hb
    · zucfh
      zucj
      have hb := index_lt_of_weak hw₂ ht
      zukxv
      exact relabelList_relabel_snd hd.1 hd.2.1 hd.2.2.1 hb

/-! ### Sizes -/
