module

public import Chazelle.Core.ShootCutShWt
public import Chazelle.RewriteTactics

/-!
# WP-G, part 54: the geometry of the origin of the ray

The ray-shooter reads the origin `z` of the ray as a point record (abscissa, height, symbolic
point) and derives from it how to query the Lemma 3.6 structures of the kind-1 pieces.

* `walk_x_bounds`: every walk vertex of a chain model lies in the box horizontally;
* `innerPt_bounds`: an inner point lies strictly inside the height range of the box and inside
  its abscissa range;
* `walk_above`: a position of the walk strictly inside the box that is neither a vertex nor an
  inner point of a tour edge (a position inside the slit) lies above the top of the chain.
-/

namespace Chazelle.Core

@[expose] public section

open Chazelle.Geometry (lerp lerp_fst lerp_snd)

namespace ShootCut

variable (C : Chain)

/-- **All walk abscissae lie in `[-R, R]`.** -/
theorem walk_x_bounds {q : ℕ} (hq : q < 2 * C.m + 7) :
    -C.radius ≤ ((chainModel C).W.vtx q).1 ∧ ((chainModel C).W.vtx q).1 ≤ C.radius := by
  have hR := C.radius_pos
  have ht := abs_lt.1 (abs_top_lt C)
  rcases (show q ≤ 5 ∨ 6 ≤ q by omega) with h | h
  · show -C.radius ≤ ((C.sideWalk C.sideBeta).vtx q).1 ∧
      ((C.sideWalk C.sideBeta).vtx q).1 ≤ C.radius
    interval_cases q
    · rw [C.sideWalk_vtx_zero]; unfold Chazelle.Chain.slitTop
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · rw [C.sideWalk_vtx_one]; exact ⟨le_rfl, by linarith⟩
    · rw [C.sideWalk_vtx_two]; exact ⟨le_rfl, by linarith⟩
    · rw [C.sideWalk_vtx_three]; exact ⟨by linarith, le_rfl⟩
    · rw [C.sideWalk_vtx_four]; exact ⟨by linarith, le_rfl⟩
    · rw [C.sideWalk_vtx_five]; unfold Chazelle.Chain.slitTop
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · obtain ⟨i, rfl⟩ : ∃ i, q = i + 6 := ⟨q - 6, by omega⟩
    show -C.radius ≤ ((C.sideWalk C.sideBeta).vtx (i + 6)).1 ∧
      ((C.sideWalk C.sideBeta).vtx (i + 6)).1 ≤ C.radius
    rw [C.sideWalk_vtx_tour _ (by omega)]
    have hb := C.set_subset_box (C.vertex_mem_set (C.sideIdx_le C.sideBeta i))
    have := abs_lt.1 hb.1
    unfold Chazelle.Chain.sideTour
    constructor <;> linarith [this.1, this.2]

/-- **An inner point of a chain model** lies strictly inside the height range of the box and
inside its abscissa range. -/
theorem innerPt_bounds {z : Point} (h : (chainModel C).InnerPt z) :
    |z.2| < C.radius ∧ |z.1| ≤ C.radius := by
  obtain ⟨⟨p, q, hp, hq, h1, h2⟩, ⟨p', q', hp', hq', h3, h4⟩⟩ := h
  have hn  := chainModel_n C
  rw [hn] at hp hq hp' hq'
  have a := walk_y_bounds C hp
  have b := walk_y_bounds C hq
  have a' := walk_x_bounds C hp'
  have b' := walk_x_bounds C hq'
  exact ⟨abs_lt.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩

/-- **A position inside the slit**: a position of the walk strictly inside the box that is
neither on a tour edge (edges `6 … 2m + 5`) nor a vertex lies above the top of the chain. -/
theorem walk_above {Q : Polygon} {N e hc : ℕ} (hp : ProperPos (chainModel C) Q N ⟨e, hc⟩)
    (hen : e < 2 * C.m + 7)
    (hx : |((chainModel C).pos Q ⟨e, hc⟩).1| < C.radius)
    (hy : |((chainModel C).pos Q ⟨e, hc⟩).2| < C.radius)
    (hno : ¬ (6 ≤ e ∧ (e < 2 * C.m + 6 ∨ (chainModel C).param Q ⟨e, hc⟩ = 0))) :
    C.top.2 < ((chainModel C).pos Q ⟨e, hc⟩).2 := by
  have hn  := chainModel_n C
  have hR := C.radius_pos
  have htop := C.top_snd_lt_radius
  have t0 := hp.1
  have t1 := hp.2.1
  have hpos : (chainModel C).pos Q ⟨e, hc⟩ = lerp ((chainModel C).W.vtx e)
      ((chainModel C).W.vtx ((e + 1) % (2 * C.m + 7))) ((chainModel C).param Q ⟨e, hc⟩) := by
    rwr [← hn]
  rw [hpos] at hx hy ⊢
  obtain ⟨t, htd⟩ : ∃ t, (chainModel C).param Q ⟨e, hc⟩ = t := ⟨_, rfl⟩
  rw [htd] at hx hy t0 t1 hno ⊢
  simp only [lerp_fst, lerp_snd] at hx hy ⊢
  rw [abs_lt] at hx hy
  have V : ∀ q, (chainModel C).W.vtx q = (C.sideWalk C.sideBeta).vtx q := fun _ => rfl
  have V6  := SweepPrim.walk_vtx_six C
  rcases (show e ≤ 5 ∨ 6 ≤ e by omega) with h5 | h6
  · rw [Nat.mod_eq_of_lt (by omega)] at hx hy ⊢
    interval_cases e
    · simp only [V, C.sideWalk_vtx_zero, C.sideWalk_vtx_one, Chazelle.Chain.slitTop] at hy
      linarith [hy.2]
    · simp only [V, C.sideWalk_vtx_one, C.sideWalk_vtx_two] at hx
      linarith [hx.1]
    · simp only [V, C.sideWalk_vtx_two, C.sideWalk_vtx_three] at hy
      linarith [hy.1]
    · simp only [V, C.sideWalk_vtx_three, C.sideWalk_vtx_four] at hx
      linarith [hx.2]
    · simp only [V, C.sideWalk_vtx_four, C.sideWalk_vtx_five, Chazelle.Chain.slitTop] at hy
      linarith [hy.2]
    · rw [show (5 : ℕ) + 1 = 6 from rfl, V6, V, C.sideWalk_vtx_five]
      unfold Chazelle.Chain.slitTop
      dsimp only
      nlinarith [mul_pos (show (0 : ℝ) < 1 - t by linarith) (show 0 < C.radius - C.top.2 by linarith)]
  · have he : e = 2 * C.m + 6 := by
      by_contra hc'
      exact hno ⟨h6, Or.inl (by omega)⟩
    have ht0 : t ≠ 0 := fun h => hno ⟨h6, Or.inr h⟩
    have tp  := lt_of_le_of_ne t0 (Ne.symm ht0)
    subst he
    rw [show 2 * C.m + 6 + 1 = 2 * C.m + 7 by omega, Nat.mod_self, SweepPrim.walk_vtx_last, V,
      C.sideWalk_vtx_zero]
    unfold Chazelle.Chain.slitTop
    dsimp only
    nlinarith [mul_pos tp (show 0 < C.radius - C.top.2 by linarith)]

end ShootCut

end

end Chazelle.Core
