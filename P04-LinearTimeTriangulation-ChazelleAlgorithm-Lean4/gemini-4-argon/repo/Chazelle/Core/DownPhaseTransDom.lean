module

public import Chazelle.Core.DownPhaseTourB
public import Chazelle.Core.DownPhaseFrontier

/-!
# WP-M (T, part 2): the top chain and the interior of `Q`

For a simple polygon `Q` and its top chain `C` (`C.P = Q`, `C.s = 0`, `C.m + 1 = Q.n`, so the
chain is `Q` without its last edge `e_{n-1} = [v_{n-1}, v_0]`):
* chain vertex `k` is `Q.vtx k` and chain edge `k` is `Q.edge k` (`vertex_eq`, `chainEdge_eq'`);
* the filled polygon lies below the top vertex (`filled_below_top`);
* the interior of `Q` lies in the domain of `C` (`interior_sub_dom`);
* the boundary of `Q` meets the domain of `C` only in the open part of `e_{n-1}`
  (`boundary_dom`).
-/

namespace Chazelle.Core

namespace Trans

@[expose] public section

open Set
open Chazelle.Chain (sidePt)
open Chazelle.Geometry (lerp)
open Chazelle.Jordan (coordBound)

/-- **The top chain** of `Q`. -/
structure Top (Q : Polygon) (C : Chain) : Prop where
  hP : C.P = Q
  hs : C.s = 0
  hm : C.m + 1 = Q.n

variable {Q : Polygon} {C : Chain}

theorem Top.n_pos (T : Top Q C) : 0 < Q.n := by have := T.hm; omega

theorem Top.edgeIdx (T : Top Q C) {k : ℕ} (hk : k < Q.n) : C.edgeIdx k = k := by
  unfold Chain.edgeIdx; rw [T.hs, zero_add, T.hP, Nat.mod_eq_of_lt hk]

/-- Chain vertex `k` is vertex `k` of `Q`. -/
theorem Top.vertex_eq (T : Top Q C) {k : ℕ} (hk : k < Q.n) : C.vertex k = Q.vtx k := by
  unfold Chain.vertex; rw [T.edgeIdx hk, T.hP]

/-- Chain edge `k` is edge `k` of `Q`. -/
theorem Top.chainEdge_eq' (T : Top Q C) {k : ℕ} (hk : k < C.m) : C.chainEdge k = Q.edge k := by
  unfold Chain.chainEdge; rw [T.edgeIdx (by have := T.hm; omega), T.hP]

/-- Every vertex of `Q` is at most as high as the top vertex. -/
theorem Top.vtx_le_top (T : Top Q C) {k : ℕ} (hk : k < Q.n) : (Q.vtx k).2 ≤ C.top.2 := by
  rw [← T.vertex_eq hk]; exact C.vertex_snd_le_top (by have := T.hm; omega)

/-- Every boundary point of `Q` is at most as high as the top vertex. -/
theorem Top.boundary_le_top (T : Top Q C) {z : Point} (hz : z ∈ Q.boundary) : z.2 ≤ C.top.2 := by
  obtain ⟨i, hi, t, ht0, ht1, rfl⟩ := hz
  have h1 := T.vtx_le_top hi
  have h2 := T.vtx_le_top (Nat.mod_lt (i + 1) T.n_pos)
  simp only
  nlinarith

/-- **The filled polygon lies below the top vertex** (a point above it sees the far exterior along
an upward ray). -/
theorem Top.filled_below_top (hQ : Q.Simple) (T : Top Q C) {z : Point} (hz : z ∈ Q.filled) :
    z.2 ≤ C.top.2 := by
  by_contra hlt
  push Not at hlt
  set L : ℝ := coordBound Q + |z.2| + 1 with hL
  have hL0 : 0 ≤ L := by rw [hL]; have := abs_nonneg z.2; have := C.coordBound_nonneg; rw [T.hP] at this; linarith
  set f : ℝ → Point := fun t => (z.1, z.2 + t) with hf
  have hpre : IsPreconnected (f '' Icc 0 L) :=
    isPreconnected_Icc.image _ (by fun_prop : Continuous f).continuousOn
  have hsub : f '' Icc 0 L ⊆ Q.boundaryᶜ := by
    rintro _ ⟨t, ht, rfl⟩ hb
    have := T.boundary_le_top hb
    simp only [hf] at this
    linarith [ht.1]
  have hw : f L ∉ Q.filled := Chazelle.Jordan.far_not_mem_filled Q (Or.inr (Or.inr (Or.inl (by
    simp only [hf, hL]; linarith [le_abs_self z.2, neg_abs_le z.2]))))
  have hzT : z ∈ f '' Icc 0 L := ⟨0, ⟨le_rfl, hL0⟩, by simp [hf]⟩
  exact FactsInterior.subset_exterior hQ hpre hsub ⟨L, ⟨hL0, le_rfl⟩, rfl⟩ hw hzT hz

/-- The chain lies on the boundary of `Q`. -/
theorem Top.set_sub (T : Top Q C) : C.set ⊆ Q.boundary := by
  rintro z ⟨k, hk, hz⟩
  rw [T.chainEdge_eq' hk] at hz
  exact ⟨k, by have := T.hm; omega, hz⟩

/-- **The interior of `Q` lies in the domain of its top chain.** -/
theorem Top.interior_sub_dom (hQ : Q.Simple) (T : Top Q C) :
    Q.filled \ Q.boundary ⊆ C.dom := by
  rintro z ⟨hzf, hzb⟩
  refine C.mem_dom_iff.2 ⟨?_, fun hs => hzb (T.set_sub hs), fun hs => ?_⟩
  · have hsq := Chazelle.Jordan.filled_subset_square Q hzf
    have := C.coordBound_lt_radius
    rw [T.hP] at this
    exact ⟨lt_of_le_of_lt hsq.1 this, lt_of_le_of_lt hsq.2 this⟩
  · obtain ⟨h1, h2, -⟩ := C.mem_slit_iff.1 hs
    have h3 := T.filled_below_top hQ hzf
    have hzt : z = C.top := Prod.ext h1 (le_antisymm h3 h2)
    exact hzb (T.set_sub (hzt ▸ C.top_mem_set))

/-- The last edge of `Q`. -/
theorem Top.last_edge (T : Top Q C) : Q.edge C.m = Chazelle.segment (Q.vtx C.m) (Q.vtx 0) := by
  unfold Polygon.edge
  rw [show (C.m + 1) % Q.n = 0 by rw [T.hm, Nat.mod_self]]

/-- **The boundary of `Q` meets the domain of `C` only in the open part of `e_{n-1}`.** -/
theorem Top.boundary_dom (T : Top Q C) {z : Point} (hz : z ∈ Q.boundary) (hzD : z ∈ C.dom) :
    ∃ s ∈ Ioo (0 : ℝ) 1, z = lerp (Q.vtx C.m) (Q.vtx 0) s := by
  have hzs := C.not_mem_set_of_mem_dom hzD
  obtain ⟨i, hi, hzi⟩ := hz
  have him : i = C.m := by
    by_contra h
    exact hzs ⟨i, by have := T.hm; omega, by rwa [T.chainEdge_eq' (by have := T.hm; omega)]⟩
  subst him
  rw [T.last_edge] at hzi
  obtain ⟨s, hs0, hs1, rfl⟩ := Chazelle.Geometry.mem_segment_iff_lerp.1 hzi
  have hm0 : C.vertex C.m = Q.vtx C.m := T.vertex_eq (by have := T.hm; omega)
  have h00 : C.vertex 0 = Q.vtx 0 := T.vertex_eq T.n_pos
  refine ⟨s, ⟨?_, ?_⟩, rfl⟩
  · rcases hs0.lt_or_eq with h | h
    · exact h
    · exfalso; subst h; rw [Chazelle.Geometry.lerp_zero, ← hm0] at hzs
      exact hzs (C.vertex_mem_set le_rfl)
  · rcases hs1.lt_or_eq with h | h
    · exact h
    · exfalso; subst h; rw [Chazelle.Geometry.lerp_one, ← h00] at hzs
      exact hzs (C.vertex_mem_set (Nat.zero_le _))

end

end Trans

end Chazelle.Core
