module

public import Chazelle.Mountain.Stack
public import Chazelle.Visibility.Ray

/-!
# The orientation of a mountain from its lowest corner

For a monotone mountain the orientation sign `orient P` (the side of the edges on which the
interior lies) is the sign of the determinant of the corner at the lowest vertex `v₀`:

  `0 < orient P * det v_{n-1} v₀ v₁`   (`mountain_orient_det`).

This is the value a machine can compute in constant time before running the stack walk;
`mountain_triangulates_of_sign` restates the correctness theorem for the sign
`σ = ±1` with `0 < σ * det v_{n-1} v₀ v₁`.

The proof transposes the coordinates (`Chazelle.Visibility.transpose`): the `(y, x)`-smallest
vertex of `P` is the `(x, y)`-smallest vertex of the transpose, whose open convex sector is
interior (`Chazelle.Existence.sector_subset_interior`); transposing back, the sector at `v₀` on
the side of `det v_{n-1} v₀ v₁` is interior, and `orient_eq_of_eventually` identifies the
orientation.
-/

namespace Chazelle.Mountain

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Jordan
open Chazelle.Existence
open Chazelle.Visibility (transpose transpose_n transpose_vtx transpose_simple
  mem_transpose_filled_iff)
open Chazelle.Programs (lexLE)
open Chazelle.Geometry (lerp det_cyclic point_ext)

/-- Swapping the coordinates negates the determinant. -/
theorem det_swap_swap_swap (a b c : Point) : det a.swap b.swap c.swap = -det a b c := by
  unfold det; simp only [Prod.fst_swap, Prod.snd_swap]; ring

/-- Balls of the sup metric are symmetric under swapping the coordinates. -/
theorem swap_mem_ball_swap_iff {y v : Point} {r : ℝ} : y.swap ∈ ball v.swap r ↔ y ∈ ball v r := by
  rw [mem_ball_iff_abs, mem_ball_iff_abs]
  simp only [Prod.fst_swap, Prod.snd_swap]
  exact and_comm

variable (P : Polygon)

/-- The lowest vertex of a mountain is `ylexLE`-smallest. -/
theorem ylexLE_zero (hM : IsMountain P) {i : ℕ} (hi : i < P.n) : ylexLE (P.vtx 0) (P.vtx i) := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · exact ylexLE_refl _
  · exact ylexLE_of_ylexLT (ylexLT_of_lt P hM hpos hi)

/-- **The open sector at the lowest vertex of a mountain is interior**, on the side of
`det v_{n-1} v₀ v₁`: for `σ = ±1` with `0 < σ * det v_{n-1} v₀ v₁` there is `r > 0` such that
every point of the ball of radius `r` around `v₀` with `0 < σ * det v_{n-1} v₀ x` and
`0 < σ * det v₀ v₁ x` lies in `P.filled \ P.boundary`. -/
theorem sector_lowest_subset_interior (hM : IsMountain P) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hpos : 0 < σ * det (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1)) :
    ∃ r > 0, ∀ y ∈ ball (P.vtx 0) r,
      0 < σ * det (P.vtx (P.n - 1)) (P.vtx 0) y → 0 < σ * det (P.vtx 0) (P.vtx 1) y →
        y ∈ P.filled \ P.boundary := by
  have hP := hM.1
  set T := transpose P with hTdef
  have hT : T.Simple := transpose_simple hP
  have hTn : T.n = P.n := transpose_n P
  have hmin : ∀ i, i < T.n → lexLE (T.vtx 0) (T.vtx i) := by
    intro i hi
    rw [hTn] at hi
    rw [hTdef, transpose_vtx, transpose_vtx]
    rcases ylexLE_zero P hM hi with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2⟩
  have hσ' : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> norm_num
  have hposT : 0 < (-σ) * det (T.vtx (T.n - 1)) (T.vtx 0) (T.vtx 1) := by
    rw [hTn, hTdef, transpose_vtx, transpose_vtx, transpose_vtx, det_swap_swap_swap]
    linarith
  obtain ⟨r, hr, hsec⟩ := sector_subset_interior hT hmin hσ' hposT
  refine ⟨r, hr, fun y hy h1 h2 => ?_⟩
  have := hsec y.swap (by rwa [hTdef, transpose_vtx, swap_mem_ball_swap_iff])
    (by rw [hTn, hTdef, transpose_vtx, transpose_vtx, det_swap_swap_swap]; linarith)
    (by rw [hTdef, transpose_vtx, transpose_vtx, det_swap_swap_swap]; linarith)
  rwa [Set.mem_sdiff, mem_transpose_filled_iff, Chazelle.Visibility.mem_transpose_boundary_iff,
    Prod.swap_swap] at this

/-- **The orientation of a mountain is the sign of its lowest corner**:
`0 < orient P * det v_{n-1} v₀ v₁`. -/
theorem mountain_orient_det (hM : IsMountain P) :
    0 < orient P * det (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) := by
  have hP := hM.1
  have hn := simple_three_le hP
  have hdet : det (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) ≠ 0 := by
    have := det_ne_zero_of_lexMin (transpose_simple hP) (by
      intro i hi
      rw [transpose_n] at hi
      rw [transpose_vtx, transpose_vtx]
      rcases ylexLE_zero P hM hi with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, h2⟩)
    rw [transpose_n, transpose_vtx, transpose_vtx, transpose_vtx, det_swap_swap_swap] at this
    intro h; apply this; rw [h, neg_zero]
  obtain ⟨σ, hσ, hpos⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      0 < σ * det (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1) := by
    rcases lt_or_gt_of_ne hdet with h | h
    · exact ⟨-1, Or.inr rfl, by linarith⟩
    · exact ⟨1, Or.inl rfl, by linarith⟩
  obtain ⟨r, hr, hsec⟩ := sector_lowest_subset_interior P hM hσ hpos
  set u := P.vtx (P.n - 1) with hu
  set v := P.vtx 0 with hv
  set w := P.vtx 1
  have huv : u ≠ v := simple_vtx_ne hP (by omega) (by omega) (by omega)
  have hsq := sqLen_pos huv
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  -- a point of the edge `u v` close to `v`, in the ball and on the `σ` side of `v w`
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
  rwa [hor]

/-- **Correctness with the computable sign.**  For a mountain `P` and any `σ = ±1` with
`0 < σ * det v_{n-1} v₀ v₁`, the stack walk with sign `σ` triangulates `P` and performs at most
`2 * n` corner tests. -/
theorem mountain_triangulates_of_sign (hM : IsMountain P) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hpos : 0 < σ * det (P.vtx (P.n - 1)) (P.vtx 0) (P.vtx 1)) :
    P.Triangulates (mountainTriangulation P σ) ∧ mountainTests P σ ≤ 2 * P.n := by
  have hor : σ = orient P := by
    have h := mountain_orient_det P hM
    rcases sign_eq_or_eq_neg hσ (orient_eq P) with h' | h'
    · exact h'
    · rw [h', neg_mul] at hpos; linarith
  exact ⟨mountain_triangulates P hM hor, mountainTests_le P hM hor⟩

end

end Chazelle.Mountain
