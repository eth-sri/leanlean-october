module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseBoxMap
public import Chazelle.Chain.Sides
public import Mathlib.Data.List.GetD

/-!
# WP-M (B3′, part 2): twin chains

Two chains `C`, `C'` (in possibly different host polygons) are **twins** if they have the same
number of edges and the same vertices.  Their chain models differ only by the box radius; the
box stretch `phi C C' = stretchPt B k` with `B = min R R' - 1/2` and `k = slope B R R'` fixes the
chain (whose coordinates are at most `min R R' - 1`) and maps

* the box of `C` onto the box of `C'`, the slit of `C` onto the slit of `C'`, the domain of `C`
  onto the domain of `C'` (`phi_mem_dom_iff`, as a preimage statement);
* every vertex of the walk of `C` to the vertex of the walk of `C'` with the same index
  (`phi_walk_vtx`): the box corners and the slit top move, the tour of the double boundary is
  fixed (`sideIdx_eq`: the tour is the same, also when `sideBeta` differs, which only happens when
  the top vertex is an end of the chain).
-/

namespace Chazelle.Core

namespace BoxT

@[expose] public section

open Set Chazelle.Chain

/-- Twin chains: the same number of edges and the same vertices. -/
structure Twin (C C' : Chain) : Prop where
  m_eq : C.m = C'.m
  vtx_eq : ∀ k, k ≤ C.m → C.vertex k = C'.vertex k

section
variable (C C' : Chain)
include C C'
/-- The fixed band `[-B, B]` of the stretch. -/
noncomputable def bnd : ℝ := min C.radius C'.radius - 1 / 2

/-- The slope of the stretch. -/
noncomputable def kk : ℝ := slope (bnd C C') C.radius C'.radius

/-- **The box stretch of twin chains.** -/
noncomputable def phi : Point → Point := stretchPt (bnd C C') (kk C C')


end

variable {C C' : Chain}

theorem one_le_radius (C : Chain) : 1 ≤ C.radius := by
  unfold Chain.radius; linarith [C.coordBound_nonneg]

theorem bnd_nonneg : 0 ≤ bnd C C' := by
  unfold bnd; have := one_le_radius C; have := one_le_radius C'
  grind

theorem bnd_lt : bnd C C' < C.radius := by
  core_grind

theorem bnd_lt' : bnd C C' < C'.radius := by
  core_grind

theorem kk_pos : 0 < kk C C' := slope_pos bnd_lt bnd_lt'

namespace Twin

variable (h : Twin C C')
include h

theorem set_eq : C.set = C'.set := by
  have hm := h.m_eq
  ext p
  simp only [Chain.set, mem_ofPred_eq]
  constructor
  · rintro ⟨k, hk, hp⟩
    refine ⟨k, h.m_eq ▸ hk, ?_⟩
    rw [Chain.chainEdge_eq] at hp ⊢
    rwa [← h.vtx_eq k (by omega), ← h.vtx_eq (k + 1) (by omega)]
  · rintro ⟨k, hk, hp⟩
    refine ⟨k, h.m_eq ▸ hk, ?_⟩
    rw [Chain.chainEdge_eq] at hp ⊢
    rwa [h.vtx_eq k (by omega), h.vtx_eq (k + 1) (by omega)]

/-- Points of the chain are well inside the fixed band. -/
theorem abs_le_of_mem {p : Point} (hp : p ∈ C.set) :
    |p.1| ≤ bnd C C' - 1 / 2 ∧ |p.2| ≤ bnd C C' - 1 / 2 := by
  have h1 := C.abs_le_coordBound_of_mem_set hp
  have h2 := C'.abs_le_coordBound_of_mem_set (h.set_eq ▸ hp)
  core_grind [Chain.radius]

theorem topIdx_eq : C.topIdx = C'.topIdx := by
  have hm := h.m_eq
  apply le_antisymm
  · refine C.topIdx_min (hm ▸ C'.topIdx_le) fun i hi => ?_
    rw [h.vtx_eq i hi, h.vtx_eq _ (hm ▸ C'.topIdx_le)]
    exact C'.topIdx_spec.2 i (hm ▸ hi)
  · refine C'.topIdx_min (hm ▸ C.topIdx_le) fun i hi => ?_
    rw [← h.vtx_eq i (hm ▸ hi), ← h.vtx_eq _ C.topIdx_le]
    exact C.topIdx_spec.2 i (hm ▸ hi)

theorem top_eq : C.top = C'.top := by
  unfold Chain.top; rw [← h.topIdx_eq]; exact h.vtx_eq _ C.topIdx_le

theorem phi_fix {p : Point} (hp : p ∈ C.set) : phi C C' p = p := by
  have := h.abs_le_of_mem hp
  exact stretchPt_of_le bnd_nonneg (by linarith) (by linarith)

omit h in
theorem stretch_fix (_h : Twin C C') {x : ℝ} (hx : |x| ≤ bnd C C') : stretch (bnd C C')
    (kk C C') x = x :=
  stretch_of_abs_le bnd_nonneg hx

theorem top_abs : |C.top.1| ≤ bnd C C' - 1 / 2 ∧ |C.top.2| ≤ bnd C C' - 1 / 2 :=
  h.abs_le_of_mem C.top_mem_set

omit h in
theorem stretch_radius_eq (_h : Twin C C') : stretch (bnd C C') (kk C C') C.radius = C'.radius :=
  stretch_radius bnd_nonneg bnd_lt

theorem stretch_neg_radius_eq : stretch (bnd C C') (kk C C') (-C.radius) = -C'.radius := by
  rw [stretch_neg bnd_nonneg, h.stretch_radius_eq]

theorem phi_slitTop : phi C C' C.slitTop = C'.slitTop := by
  unfold phi stretchPt Chain.slitTop
  rw [h.stretch_fix (by linarith [h.top_abs.1]), h.stretch_radius_eq, h.top_eq]

omit h in
theorem stretch_inj (_h : Twin C C') {x y : ℝ} (hxy : stretch (bnd C C')
    (kk C C') x = stretch (bnd C C') (kk C C') y) :
    x = y := (stretch_strictMono bnd_nonneg kk_pos).injective hxy

omit h in
theorem stretch_le_iff (_h : Twin C C') {x y : ℝ} :
    stretch (bnd C C') (kk C C') x ≤ stretch (bnd C C') (kk C C') y ↔ x ≤ y :=
  (stretch_strictMono bnd_nonneg kk_pos).le_iff_le

/-- A point whose stretch lies on the chain is fixed. -/
theorem eq_of_phi_mem {p : Point} (hp : phi C C' p ∈ C.set) : phi C C' p = p := by
  have hb := h.abs_le_of_mem hp
  simp only [phi, stretchPt] at hb
  have e1 := stretch_inv (B := bnd C C') (k := kk C C') (bnd_nonneg (C := C) (C' := C'))
    (kk_pos (C := C) (C' := C')) p.1
  have e2 := stretch_inv (B := bnd C C') (k := kk C C') (bnd_nonneg (C := C) (C' := C'))
    (kk_pos (C := C) (C' := C')) p.2
  rw [stretch_of_abs_le bnd_nonneg (by linarith)] at e1
  rw [stretch_of_abs_le bnd_nonneg (by linarith)] at e2
  exact Prod.ext e1 e2

theorem phi_mem_set_iff (p : Point) : phi C C' p ∈ C'.set ↔ p ∈ C.set := by
  constructor
  · intro hp
    rw [← h.set_eq] at hp
    rwa [h.eq_of_phi_mem hp] at hp
  · intro hp; rw [h.phi_fix hp, ← h.set_eq]; exact hp

theorem phi_mem_slit_iff (p : Point) : phi C C' p ∈ C'.slit ↔ p ∈ C.slit := by
  rw [Chain.mem_slit_iff, Chain.mem_slit_iff, ← h.top_eq]
  have ht1 := h.stretch_fix (x := C.top.1) (by linarith [h.top_abs.1])
  have ht2 := h.stretch_fix (x := C.top.2) (by linarith [h.top_abs.2])
  simp only [phi, stretchPt]
  grind [Chazelle.Core.BoxT.Twin.stretch_inj, Chazelle.Core.BoxT.Twin.stretch_le_iff, Chazelle.Core.BoxT.Twin.stretch_radius_eq]

omit h in
theorem phi_mem_box_iff (_h : Twin C C')
    (p : Point) : phi C C' p ∈ box C'.radius ↔ p ∈ box C.radius :=
  stretchPt_mem_box_iff bnd_nonneg bnd_lt bnd_lt' p

/-- **The stretch maps the domain of `C` onto the domain of `C'`.** -/
theorem phi_mem_dom_iff (p : Point) : phi C C' p ∈ C'.dom ↔ p ∈ C.dom := by
  simp only [Chain.dom, Chain.obstacle, mem_sdiff, mem_union, h.phi_mem_box_iff,
    h.phi_mem_set_iff, h.phi_mem_slit_iff]

/-! ## The walks -/

theorem sideIdx_eq (i : ℕ) : C.sideIdx C.sideBeta i = C'.sideIdx C'.sideBeta i := by
  have hm := h.m_eq
  have hT := h.topIdx_eq
  have hTle := C.topIdx_le
  unfold Chain.sideIdx Chain.sideS
  rw [← hm, ← hT]
  -- the tour does not depend on the turn when the top is an end of the chain
  by_cases hend : C.topIdx = 0 ∨ C.topIdx = C.m
  · have hm0 : 0 < 2 * C.m := by have := C.one_le; omega
    rcases hend with h0 | h0
    · rw [h0]
      cases C.sideBeta <;> cases C'.sideBeta <;> simp [Nat.add_mod_left]
    · rw [h0]
      cases C.sideBeta <;> cases C'.sideBeta <;> simp [show 2 * C.m - C.m = C.m by omega]
  · push Not at hend
    have hbeta : C.sideBeta = C'.sideBeta := by
      unfold Chain.sideBeta
      rw [← h.top_eq, ← hT, ← h.vtx_eq _ (by omega), ← h.vtx_eq _ (by omega)]
      congr 1
      apply propext
      -- the slit direction is `(0, R - top.2)` resp. `(0, R' - top.2)`: same direction
      have hR := C.top_snd_lt_radius
      have hR' := C'.top_snd_lt_radius
      rw [h.top_eq] at hR ⊢
      unfold Chain.slitTop
      rw [← h.top_eq]
      set A := C.vertex (C.topIdx - 1) - C.top
      set Bv := C.vertex (C.topIdx + 1) - C.top
      have e1 : ((C.top.1, C.radius) : Point) - C.top = (0, C.radius - C.top.2) := by
        ext <;> simp
      have e2 : ((C.top.1, C'.radius) : Point) - C.top = (0, C'.radius - C.top.2) := by
        ext <;> simp
      rw [e1, e2]
      have hc1 : 0 < C.radius - C.top.2 := by linarith [C.top_snd_lt_radius]
      have hc2 : 0 < C'.radius - C.top.2 := by rw [h.top_eq]; linarith
      unfold sideCcw sideCross sideDot
      simp only
      constructor <;> intro hh <;>
        rcases hh with ⟨a, b, c⟩ | ⟨a, b⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
      all_goals first
        | (left; refine ⟨a, ?_, ?_⟩ <;> nlinarith)
        | (right; left; refine ⟨a, ?_⟩; rcases b with b | b
           · left; nlinarith
           · right; nlinarith)
        | (right; right; left; refine ⟨a, b, ?_⟩; nlinarith)
        | (right; right; right; refine ⟨a, b, ?_⟩; rcases c with c | c
           · left; intro hc; apply c; nlinarith
           · right; nlinarith)
    rw [hbeta]

omit h in
theorem sideIdx_le (_h : Twin C C') (i : ℕ) : C.sideIdx C.sideBeta i ≤ C.m := by
  unfold Chain.sideIdx
  exact sideE_le (Nat.mod_lt _ (by have := C.one_le; omega)).le

theorem walk_n : (C'.sideWalk C'.sideBeta).n = (C.sideWalk C.sideBeta).n := by
  rw [Chain.sideWalk_n, Chain.sideWalk_n, h.m_eq]

/-- **The walk vertices correspond under the stretch.** -/
theorem phi_walk_vtx (i : ℕ) :
    (C'.sideWalk C'.sideBeta).vtx i = phi C C' ((C.sideWalk C.sideBeta).vtx i) := by
  have hm := h.m_eq
  have hR := h.stretch_radius_eq
  have hRn := h.stretch_neg_radius_eq
  rcases Nat.lt_or_ge i 6 with hi | hi
  · interval_cases i
    · rw [Chain.sideWalk_vtx_zero, Chain.sideWalk_vtx_zero, h.phi_slitTop]
    · simp_all [Chain.sideWalk_vtx_one, phi, stretchPt] 
    · simp_all [Chain.sideWalk_vtx_two, phi, stretchPt] 
    · simp_all [Chain.sideWalk_vtx_three, phi, stretchPt] 
    · simp_all [Chain.sideWalk_vtx_four, phi, stretchPt] 
    · rw [Chain.sideWalk_vtx_five, Chain.sideWalk_vtx_five, h.phi_slitTop]
  · rcases Nat.lt_or_ge (i - 6) (2 * C.m + 1) with hi' | hi'
    · have e : i = (i - 6) + 6 := by omega
      rw [e, C.sideWalk_vtx_tour _ (by omega), C'.sideWalk_vtx_tour _ (by omega)]
      unfold Chain.sideTour
      rw [← h.sideIdx_eq, ← h.vtx_eq _ (h.sideIdx_le _),
        h.phi_fix (C.vertex_mem_set (h.sideIdx_le _))]
    · -- beyond the walk: the default vertex `(0, 0)`, fixed by the stretch
      have hn : (C.sideWalk C.sideBeta).n ≤ i := by grind [Chain.sideWalk_n]
      have hn' : (C'.sideWalk C'.sideBeta).n ≤ i := by grind [Chain.sideWalk_n]
      unfold Polygon.vtx
      rw [List.getD_eq_default _ _ hn, List.getD_eq_default _ _ hn']
      exact (stretchPt_of_le bnd_nonneg (by simp [bnd_nonneg]) (by simp [bnd_nonneg])).symm

end Twin

end

end BoxT

end Chazelle.Core
