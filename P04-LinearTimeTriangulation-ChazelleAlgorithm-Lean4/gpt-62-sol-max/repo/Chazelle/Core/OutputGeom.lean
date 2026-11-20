module

public import Chazelle.Core.SpecPhases
public import Chazelle.Core.FactsInterior
public import Chazelle.Core.Setup

/-!
# WP-N, part 1: the top and bottom sides of a trapezoid (distinct heights)

For a simple polygon `Q` with pairwise distinct vertex heights and trapezoid data `D` of a region
`U = D.region` of its horizontal visibility map, with left and right side edges `i`, `j`, heights
`y₁ < y₂` and top and bottom vertices `vt = D.top`, `vb = D.bot`:

* the only boundary point of the open top side `(Lt, Rt) × {y₂}` (with `Lt = edgeX Q i y₂`,
  `Rt = edgeX Q j y₂`) is the vertex `vt` (`top_bdry`); every other point of it is interior, in
  the closure of `U`, and on a chord (`top_chord_pt`);
* a chord meeting the closure of `U` in an interior point does so on the open top or bottom side
  (`touch_cases`);
* a chord through the open top side has its left end at `Lt` or at `vt`, its right end at `vt`
  or at `Rt` (`top_chord_ends`);
* if the open top side is empty, `vt` is the upper end of both side edges (`top_empty`);
* if `vt` is not at the left corner, some chord through the top side ends at the left corner
  (`exists_top_chord_left`), and symmetrically on the right;

and the same for the bottom side.
-/

namespace Chazelle.Core

namespace OutGeom

open Set Filter Topology
open Chazelle.Visibility
open Chazelle.Mountain (TrapData topVtx botVtx sideVtxSet)
open Chazelle.Jordan (simple_vtx_inj simple_openEdge_not_mem_other simple_openEdge_ne_vtx
  exists_openEdge_of_mem_boundary simple_endpoint_of_mem_two succIdx_lt simple_vtx_succ_ne)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext point_ext_iff continuous_lerp)

@[expose] public section

variable {Q : Polygon} (hQ : Q.Simple) (hdh : DistinctHeights Q) (D : TrapData Q)

/-! ## Vertices at the side heights -/

include hdh in
/-- The top vertex is the only vertex at the top height. -/
theorem vtx_eq_top (hQ : Q.Simple) {k : ℕ} (hk : k < Q.n) (hy : (Q.vtx k).2 = D.y₂) :
    k = D.top := by
  by_contra hne
  exact hdh k D.top hk (D.top_lt hQ) hne (hy.trans (D.top_snd hQ).symm)

include hdh in
/-- The bottom vertex is the only vertex at the bottom height. -/
theorem vtx_eq_bot (hQ : Q.Simple) {k : ℕ} (hk : k < Q.n) (hy : (Q.vtx k).2 = D.y₁) :
    k = D.bot := by
  by_contra hne
  exact hdh k D.bot hk (D.bot_lt hQ) hne (hy.trans (D.bot_snd hQ).symm)

include hQ in
/-- The top vertex lies on the closed top side. -/
theorem top_x_mem : edgeX Q D.i D.y₂ ≤ (Q.vtx D.top).1 ∧ (Q.vtx D.top).1 ≤ edgeX Q D.j D.y₂ := by
  have h := D.isTrap.topVtx_mem hQ D.free
  exact ⟨h.2.2.1, h.2.2.2⟩

include hQ in
/-- The bottom vertex lies on the closed bottom side. -/
theorem bot_x_mem : edgeX Q D.i D.y₁ ≤ (Q.vtx D.bot).1 ∧ (Q.vtx D.bot).1 ≤ edgeX Q D.j D.y₁ := by
  have h := D.isTrap.botVtx_mem hQ D.free
  exact ⟨h.2.2.1, h.2.2.2⟩

/-! ## Boundary points of the open sides -/

include hQ in
/-- A boundary point `z` of height `y₀` near which the points on the `ε`-side of the line are in
the region is a vertex (a non-vertex boundary point lies inside a non-horizontal edge, whose
points on the `ε`-side would be boundary points of the region). -/
theorem side_bdry_vtx {z : Point} {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (hz : z ∈ Q.boundary)
    (hdh : DistinctHeights Q)
    (hnear : ∀ᶠ p' in 𝓝 z, 0 < ε * (p'.2 - z.2) → p' ∈ D.region) :
    ∃ m, m < Q.n ∧ Q.vtx m = z := by
  by_contra hv
  push Not at hv
  obtain ⟨e, he, t, ht, hzt⟩ := exists_openEdge_of_mem_boundary Q hz (fun m hm h => hv m hm h.symm)
  set a := Q.vtx e with ha
  set b := Q.vtx ((e + 1) % Q.n) with hb
  have hn3 := hQ.1
  have hab := hdh e _ he (succIdx_lt Q he) (Chazelle.Jordan.succIdx_ne Q hn3 he).symm
  -- move along the edge towards the `ε` side
  set d : ℝ := ε * (b.2 - a.2) with hd
  have hd0 : d ≠ 0 := by
    rw [hd]
    exact mul_ne_zero (by rcases hε with rfl | rfl <;> norm_num) (sub_ne_zero.2 hab.symm)
  set g : ℝ → Point := fun s => lerp a b (t + s * d) with hg
  have hgc : Continuous g := (continuous_lerp a b).comp (by fun_prop)
  have hg0 : g 0 = z := by simp [hg, hzt]
  have htend : Tendsto g (𝓝[>] 0) (𝓝 z) := by
    rw [← hg0]; exact (hgc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hev1 := htend.eventually hnear
  have htend' : Tendsto (fun s : ℝ => t + s * d) (𝓝[>] 0) (𝓝 t) := by
    have hc : Continuous (fun s : ℝ => t + s * d) := by fun_prop
    have := hc.tendsto 0
    simp only [zero_mul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev2 := htend'.eventually (isOpen_Ioo.mem_nhds ht)
  obtain ⟨s, ⟨h1, h2⟩, hs⟩ := ((hev1.and hev2).and self_mem_nhdsWithin).exists
  have hs0 := hs
  have hy : (g s).2 - z.2 = s * d * (b.2 - a.2) := by
    simp only [hg, lerp_snd]; rw [hzt, lerp_snd]; ring
  have hpos : 0 < ε * ((g s).2 - z.2) := by
    rw [hy]
    have : ε * (s * d * (b.2 - a.2)) = s * (d * d) := by rw [hd]; ring
    rw [this]
    exact mul_pos hs0 (mul_self_pos.2 hd0)
  have hreg := h1 hpos
  have hmem : g s ∈ Q.boundary := ⟨e, he, Chazelle.Geometry.lerp_mem_segment _ _ h2.1.le h2.2.le⟩
  exact (D.region_subset_interior hQ hreg).2 hmem

include hQ hdh in
/-- **The only boundary point of the open top side is the top vertex.** -/
theorem top_bdry {x : ℝ} (hx1 : edgeX Q D.i D.y₂ < x) (hx2 : x < edgeX Q D.j D.y₂)
    (hb : ((x, D.y₂) : Point) ∈ Q.boundary) : ((x, D.y₂) : Point) = Q.vtx D.top := by
  obtain ⟨m, hm, hmz⟩ := side_bdry_vtx hQ D (Or.inr rfl) hb hdh (D.isTrap.near_top hx1 hx2)
  have := vtx_eq_top hdh D hQ hm (by rw [hmz])
  rw [← hmz, this]

include hQ hdh in
/-- **The only boundary point of the open bottom side is the bottom vertex.** -/
theorem bot_bdry {x : ℝ} (hx1 : edgeX Q D.i D.y₁ < x) (hx2 : x < edgeX Q D.j D.y₁)
    (hb : ((x, D.y₁) : Point) ∈ Q.boundary) : ((x, D.y₁) : Point) = Q.vtx D.bot := by
  obtain ⟨m, hm, hmz⟩ := side_bdry_vtx hQ D (Or.inl rfl) hb hdh (D.isTrap.near_bot hx1 hx2)
  have := vtx_eq_bot hdh D hQ hm (by rw [hmz])
  rw [← hmz, this]

/-- The geometric facts about a horizontal wall, used for either height. -/
private structure Wall (Q : Polygon) (U : Set Point) (l r y : ℝ) (v : Point) : Prop where
  coords : l ≤ v.1 ∧ v.1 ≤ r
  left_mem : (l, y) ∈ Q.boundary
  right_mem : (r, y) ∈ Q.boundary
  vertex : ∀ {x}, l < x → x < r → (x, y) ∈ Q.boundary → (x, y) = v
  near : ∀ {x}, l < x → x < r → (x, y) ∈ closure U
  side : ∀ {x}, l < x → x < r → (x, y) ∈ Q.boundary ∨ ∃ c ∈ chords Q, (x, y) ∈ c
  filled : closure U ⊆ Q.filled

private theorem Wall.chord_pt {U : Set Point} {l r y x : ℝ} {v : Point}
    (w : Wall Q U l r y v) (hl : l < x) (hr : x < r) (hne : (x, y) ≠ v) :
    ∃ c ∈ chords Q, (x, y) ∈ c ∧ (x, y) ∈ Q.filled \ Q.boundary ∧ (x, y) ∈ closure U := by
  have hc := w.near hl hr
  have hn : (x, y) ∉ Q.boundary := fun hb => hne (w.vertex hl hr hb)
  obtain ⟨c, hch, hx⟩ := (w.side hl hr).resolve_left hn
  exact ⟨c, hch, hx, ⟨w.filled hc, hn⟩, hc⟩

private theorem Wall.chord_ends {U : Set Point} {l r y a b : ℝ} {v z : Point}
    (w : Wall Q U l r y v) (hch : IsHChord Q y a b) (hz : z ∈ hseg y a b)
    (hzD : z ∈ Q.filled \ Q.boundary) (hl : l < z.1) (hr : z.1 < r) :
    l ≤ a ∧ (a = l ∨ a = v.1) ∧ b ≤ r ∧ (b = r ∨ b = v.1) := by
  obtain ⟨hy, ha, hb⟩ := hz
  have ha' : a < z.1 := ha.lt_of_ne fun h => hzD.2 ((show z = (a, y) from point_ext h.symm hy).symm ▸ hch.left_mem)
  have hb' : z.1 < b := hb.lt_of_ne fun h => hzD.2 ((show z = (b, y) from point_ext h hy).symm ▸ hch.right_mem)
  have hla : l ≤ a := le_of_not_gt fun h => (hch.open_int _ h (hl.trans hb')).2 w.left_mem
  have hbr : b ≤ r := le_of_not_gt fun h => (hch.open_int _ (ha'.trans hr) h).2 w.right_mem
  refine ⟨hla, ?_, hbr, ?_⟩
  · rcases hla.lt_or_eq with h | h
    · exact Or.inr (congrArg Prod.fst (w.vertex h (ha'.trans hr) hch.left_mem))
    · exact Or.inl h.symm
  · rcases hbr.lt_or_eq with h | h
    · exact Or.inr (congrArg Prod.fst (w.vertex (hl.trans hb') h hch.right_mem))
    · exact Or.inl h

include hQ hdh in
private theorem topWall : Wall Q D.region (edgeX Q D.i D.y₂) (edgeX Q D.j D.y₂)
    D.y₂ (Q.vtx D.top) := by
  have hy := (D.isTrap.bot_lt.trans D.isTrap.lt_top).le
  exact ⟨top_x_mem hQ D, ⟨D.i, D.isTrap.hi, D.isTrap.mem_edgeL hy le_rfl rfl⟩,
    ⟨D.j, D.isTrap.hj, D.isTrap.mem_edgeR hy le_rfl rfl⟩, fun {x} => top_bdry hQ hdh D (x := x),
    fun {x} => D.isTrap.top_mem_closure (x := x), fun {x} hl hr => D.isTrap.top_side hQ D.free hl hr,
    D.isTrap.closure_subset_filled hQ D.free⟩

include hQ hdh in
private theorem botWall : Wall Q D.region (edgeX Q D.i D.y₁) (edgeX Q D.j D.y₁)
    D.y₁ (Q.vtx D.bot) := by
  have hy := (D.isTrap.bot_lt.trans D.isTrap.lt_top).le
  exact ⟨bot_x_mem hQ D, ⟨D.i, D.isTrap.hi, D.isTrap.mem_edgeL le_rfl hy rfl⟩,
    ⟨D.j, D.isTrap.hj, D.isTrap.mem_edgeR le_rfl hy rfl⟩, fun {x} => bot_bdry hQ hdh D (x := x),
    fun {x} => D.isTrap.bot_mem_closure (x := x), fun {x} hl hr => D.isTrap.bot_side hQ D.free hl hr,
    D.isTrap.closure_subset_filled hQ D.free⟩

include hQ in
/-- **A chord touches the region on its open top or bottom side.** -/
theorem touch_cases {c : Set Point} (hc : c ∈ chords Q) {z : Point} (hzc : z ∈ c)
    (hzD : z ∈ Q.filled \ Q.boundary) (hzU : z ∈ closure D.region) :
    (z.2 = D.y₂ ∧ edgeX Q D.i D.y₂ < z.1 ∧ z.1 < edgeX Q D.j D.y₂) ∨
      (z.2 = D.y₁ ∧ edgeX Q D.i D.y₁ < z.1 ∧ z.1 < edgeX Q D.j D.y₁) := by
  obtain ⟨h1, h2, h3, h4⟩ := closure_trapSet_subset Q D.i D.j D.y₁ D.y₂ hzU
  have hnotU := fun h =>
    (D.region_subset_freeRegion hQ h).2 ⟨c, hc, hzc⟩
  have hnotL := fun e =>
    hzD.2 ⟨D.i, D.isTrap.hi, D.isTrap.mem_edgeL h1 h2 e⟩
  have hnotR := fun e =>
    hzD.2 ⟨D.j, D.isTrap.hj, D.isTrap.mem_edgeR h1 h2 e⟩
  have h3' := lt_of_le_of_ne h3 (Ne.symm hnotL)
  have h4' := lt_of_le_of_ne h4 hnotR
  rcases h1.lt_or_eq with h1 | h1
  · rcases h2.lt_or_eq with h2 | h2
    · exact absurd ⟨h1, h2, h3', h4'⟩ hnotU
    simp_all
  · simp_all

include hQ hdh in
/-- **The ends of a chord through the open top side**: its left end is the left corner or the
top vertex, its right end the top vertex or the right corner. -/
theorem top_chord_ends {a b : ℝ} (hch : IsHChord Q D.y₂ a b) {z : Point}
    (hz : z ∈ hseg D.y₂ a b) (hzD : z ∈ Q.filled \ Q.boundary)
    (hz1 : edgeX Q D.i D.y₂ < z.1) (hz2 : z.1 < edgeX Q D.j D.y₂) :
    edgeX Q D.i D.y₂ ≤ a ∧ (a = edgeX Q D.i D.y₂ ∨ a = (Q.vtx D.top).1) ∧
      b ≤ edgeX Q D.j D.y₂ ∧ (b = edgeX Q D.j D.y₂ ∨ b = (Q.vtx D.top).1) :=
  (topWall hQ hdh D).chord_ends hch hz hzD hz1 hz2

include hQ hdh in
/-- **The ends of a chord through the open bottom side.** -/
theorem bot_chord_ends {a b : ℝ} (hch : IsHChord Q D.y₁ a b) {z : Point}
    (hz : z ∈ hseg D.y₁ a b) (hzD : z ∈ Q.filled \ Q.boundary)
    (hz1 : edgeX Q D.i D.y₁ < z.1) (hz2 : z.1 < edgeX Q D.j D.y₁) :
    edgeX Q D.i D.y₁ ≤ a ∧ (a = edgeX Q D.i D.y₁ ∨ a = (Q.vtx D.bot).1) ∧
      b ≤ edgeX Q D.j D.y₁ ∧ (b = edgeX Q D.j D.y₁ ∨ b = (Q.vtx D.bot).1) :=
  (botWall hQ hdh D).chord_ends hch hz hzD hz1 hz2

include hQ hdh in
/-- **An empty top side**: the top vertex is at both upper corners. -/
theorem top_empty (h : edgeX Q D.j D.y₂ ≤ edgeX Q D.i D.y₂) :
    Q.vtx D.top = ((edgeX Q D.i D.y₂, D.y₂) : Point) ∧
      Q.vtx D.top = ((edgeX Q D.j D.y₂, D.y₂) : Point) := by
  have hle := D.isTrap.edgeX_le_top hQ D.free
  have heq := le_antisymm hle h
  have hy12 := (D.isTrap.bot_lt.trans D.isTrap.lt_top).le
  have h1 : ((edgeX Q D.i D.y₂, D.y₂) : Point) ∈ Q.edge D.i := D.isTrap.mem_edgeL hy12 le_rfl rfl
  have h2 : ((edgeX Q D.i D.y₂, D.y₂) : Point) ∈ Q.edge D.j := D.isTrap.mem_edgeR hy12 le_rfl heq
  obtain ⟨m, hm, hmp⟩ := Final.exists_vtx_of_mem_two_edges hQ D.isTrap.hi D.isTrap.hj
    (D.isTrap.ne hQ D.free.1) h1 h2
  have hmt := vtx_eq_top hdh D hQ hm (by rw [hmp])
  simp_all

include hQ hdh in
/-- **An empty bottom side**: the bottom vertex is at both lower corners. -/
theorem bot_empty (h : edgeX Q D.j D.y₁ ≤ edgeX Q D.i D.y₁) :
    Q.vtx D.bot = ((edgeX Q D.i D.y₁, D.y₁) : Point) ∧
      Q.vtx D.bot = ((edgeX Q D.j D.y₁, D.y₁) : Point) := by
  have hle := D.isTrap.edgeX_le_bot hQ D.free
  have heq := le_antisymm hle h
  have hy12 := (D.isTrap.bot_lt.trans D.isTrap.lt_top).le
  have h1 : ((edgeX Q D.i D.y₁, D.y₁) : Point) ∈ Q.edge D.i := D.isTrap.mem_edgeL le_rfl hy12 rfl
  have h2 : ((edgeX Q D.i D.y₁, D.y₁) : Point) ∈ Q.edge D.j := D.isTrap.mem_edgeR le_rfl hy12 heq
  obtain ⟨m, hm, hmp⟩ := Final.exists_vtx_of_mem_two_edges hQ D.isTrap.hi D.isTrap.hj
    (D.isTrap.ne hQ D.free.1) h1 h2
  have hmt := vtx_eq_bot hdh D hQ hm (by rw [hmp])
  simp_all

/-- A chord of `Q` through a point of height `y`, as a horizontal chord at height `y`. -/
theorem chord_hseg (hQ : Q.Simple) {c : Set Point} (hc : c ∈ chords Q) {z : Point} (hz : z ∈ c) :
    ∃ a b, IsHChord Q z.2 a b ∧ c = hseg z.2 a b := by
  obtain ⟨v, σ, hv, hσ, hdir, rfl, hch⟩ := chords_spec hQ hc
  have hz' := hz
  rw [chordSet_eq_hseg] at hz'
  rw [hz'.1, chordSet_eq_hseg]
  exact ⟨_, _, hch, rfl⟩

include hQ in
private theorem Wall.left_chord {U : Set Point} {l r y : ℝ} {v : Point}
    (w : Wall Q U l r y v) (hne : v.1 ≠ l) :
    ∃ c ∈ chords Q, ∃ b, IsHChord Q y l b ∧ c = hseg y l b ∧
      ∃ z ∈ c, z ∈ Q.filled \ Q.boundary ∧ z ∈ closure U := by
  have hl := w.coords.1.lt_of_ne hne.symm
  let x := (l + v.1) / 2
  have h1 : l < x := by dsimp [x]; linarith
  have h2 : x < v.1 := by dsimp [x]; linarith
  have hr := h2.trans_le w.coords.2
  obtain ⟨c, hc, hx, hD, hU⟩ := w.chord_pt h1 hr fun h => h2.ne (congrArg Prod.fst h)
  obtain ⟨a, b, hch, rfl⟩ := chord_hseg hQ hc hx
  have ha : a = l := (w.chord_ends hch hx hD h1 hr).2.1.resolve_right
    (fun he => h2.not_ge (he ▸ hx.2.1))
  subst a
  exact ⟨_, hc, b, hch, rfl, _, hx, hD, hU⟩

include hQ in
private theorem Wall.right_chord {U : Set Point} {l r y : ℝ} {v : Point}
    (w : Wall Q U l r y v) (hne : v.1 ≠ r) :
    ∃ c ∈ chords Q, ∃ a, IsHChord Q y a r ∧ c = hseg y a r ∧
      ∃ z ∈ c, z ∈ Q.filled \ Q.boundary ∧ z ∈ closure U := by
  have hr := w.coords.2.lt_of_ne hne
  let x := (v.1 + r) / 2
  have h1 : v.1 < x := by dsimp [x]; linarith
  have h2 : x < r := by dsimp [x]; linarith
  have hl := w.coords.1.trans_lt h1
  obtain ⟨c, hc, hx, hD, hU⟩ := w.chord_pt hl h2 fun h => h1.ne' (congrArg Prod.fst h)
  obtain ⟨a, b, hch, rfl⟩ := chord_hseg hQ hc hx
  have hb : b = r := (w.chord_ends hch hx hD hl h2).2.2.2.resolve_right
    (fun he => h1.not_ge (he ▸ hx.2.2))
  subst b
  exact ⟨_, hc, a, hch, rfl, _, hx, hD, hU⟩

include hQ hdh in
/-- **Left top corner**: if the top vertex is not at the left upper corner, some chord through
the open top side ends at that corner. -/
theorem exists_top_chord_left (hne : (Q.vtx D.top).1 ≠ edgeX Q D.i D.y₂) :
    ∃ c ∈ chords Q, ∃ b, IsHChord Q D.y₂ (edgeX Q D.i D.y₂) b ∧
      c = hseg D.y₂ (edgeX Q D.i D.y₂) b ∧
      ∃ z ∈ c, z ∈ Q.filled \ Q.boundary ∧ z ∈ closure D.region :=
  (topWall hQ hdh D).left_chord hQ hne

include hQ hdh in
/-- **Right top corner**: if the top vertex is not at the right upper corner, some chord through
the open top side ends at that corner. -/
theorem exists_top_chord_right (hne : (Q.vtx D.top).1 ≠ edgeX Q D.j D.y₂) :
    ∃ c ∈ chords Q, ∃ a, IsHChord Q D.y₂ a (edgeX Q D.j D.y₂) ∧
      c = hseg D.y₂ a (edgeX Q D.j D.y₂) ∧
      ∃ z ∈ c, z ∈ Q.filled \ Q.boundary ∧ z ∈ closure D.region :=
  (topWall hQ hdh D).right_chord hQ hne

include hQ hdh in
/-- **Left bottom corner.** -/
theorem exists_bot_chord_left (hne : (Q.vtx D.bot).1 ≠ edgeX Q D.i D.y₁) :
    ∃ c ∈ chords Q, ∃ b, IsHChord Q D.y₁ (edgeX Q D.i D.y₁) b ∧
      c = hseg D.y₁ (edgeX Q D.i D.y₁) b ∧
      ∃ z ∈ c, z ∈ Q.filled \ Q.boundary ∧ z ∈ closure D.region :=
  (botWall hQ hdh D).left_chord hQ hne

include hQ hdh in
/-- **Right bottom corner.** -/
theorem exists_bot_chord_right (hne : (Q.vtx D.bot).1 ≠ edgeX Q D.j D.y₁) :
    ∃ c ∈ chords Q, ∃ a, IsHChord Q D.y₁ a (edgeX Q D.j D.y₁) ∧
      c = hseg D.y₁ a (edgeX Q D.j D.y₁) ∧
      ∃ z ∈ c, z ∈ Q.filled \ Q.boundary ∧ z ∈ closure D.region :=
  (botWall hQ hdh D).right_chord hQ hne

/-! ## Vertices at the corners are ends of the side edges -/

/-- A vertex on an edge, above the lower end of the edge, is its upper end. -/
theorem endpoint_upper (hQ : Q.Simple) {e v : ℕ} (he : e < Q.n) (hv : v < Q.n)
    (hmem : Q.vtx v ∈ Q.edge e) (hbot : edgeBot Q e < (Q.vtx v).2) :
    (v = e ∧ (Q.vtx ((e + 1) % Q.n)).2 < (Q.vtx v).2) ∨
      (v = (e + 1) % Q.n ∧ (Q.vtx e).2 < (Q.vtx v).2) := by
  unfold edgeBot at hbot
  rcases Chazelle.Existence.eq_endpoint_of_vtx_mem_edge hQ hv he hmem with h | h
  · left
    refine ⟨simple_vtx_inj hQ hv he h, ?_⟩
    simp_all
  · right
    refine ⟨simple_vtx_inj hQ hv (succIdx_lt Q he) h, ?_⟩
    simp_all

/-- A vertex on an edge, below the upper end of the edge, is its lower end. -/
theorem endpoint_lower (hQ : Q.Simple) {e v : ℕ} (he : e < Q.n) (hv : v < Q.n)
    (hmem : Q.vtx v ∈ Q.edge e) (htop : (Q.vtx v).2 < edgeTop Q e) :
    (v = e ∧ (Q.vtx v).2 < (Q.vtx ((e + 1) % Q.n)).2) ∨
      (v = (e + 1) % Q.n ∧ (Q.vtx v).2 < (Q.vtx e).2) := by
  unfold edgeTop at htop
  rcases Chazelle.Existence.eq_endpoint_of_vtx_mem_edge hQ hv he hmem with h | h
  · left
    refine ⟨simple_vtx_inj hQ hv he h, ?_⟩
    simp_all
  · right
    refine ⟨simple_vtx_inj hQ hv (succIdx_lt Q he) h, ?_⟩
    simp_all

include hQ in
/-- The top vertex at the left upper corner is an end of the left edge, above the other end. -/
theorem top_left_upper (h : Q.vtx D.top = ((edgeX Q D.i D.y₂, D.y₂) : Point)) :
    (D.top = D.i ∧ (Q.vtx ((D.i + 1) % Q.n)).2 < (Q.vtx D.top).2) ∨
      (D.top = (D.i + 1) % Q.n ∧ (Q.vtx D.i).2 < (Q.vtx D.top).2) := by
  have hy12 := (D.isTrap.bot_lt.trans D.isTrap.lt_top).le
  refine endpoint_upper hQ D.isTrap.hi (D.top_lt hQ) ?_ ?_
  · rw [h]; exact D.isTrap.mem_edgeL hy12 le_rfl rfl
  · rw [D.top_snd hQ]; exact lt_of_le_of_lt D.isTrap.botL (D.isTrap.bot_lt.trans D.isTrap.lt_top)

include hQ in
/-- The top vertex at the right upper corner is an end of the right edge, above the other end. -/
theorem top_right_upper (h : Q.vtx D.top = ((edgeX Q D.j D.y₂, D.y₂) : Point)) :
    (D.top = D.j ∧ (Q.vtx ((D.j + 1) % Q.n)).2 < (Q.vtx D.top).2) ∨
      (D.top = (D.j + 1) % Q.n ∧ (Q.vtx D.j).2 < (Q.vtx D.top).2) := by
  have hy12 := (D.isTrap.bot_lt.trans D.isTrap.lt_top).le
  refine endpoint_upper hQ D.isTrap.hj (D.top_lt hQ) ?_ ?_
  · rw [h]; exact D.isTrap.mem_edgeR hy12 le_rfl rfl
  · rw [D.top_snd hQ]; exact lt_of_le_of_lt D.isTrap.botR (D.isTrap.bot_lt.trans D.isTrap.lt_top)

include hQ in
/-- The bottom vertex at the left lower corner is an end of the left edge, below the other end. -/
theorem bot_left_lower (h : Q.vtx D.bot = ((edgeX Q D.i D.y₁, D.y₁) : Point)) :
    (D.bot = D.i ∧ (Q.vtx D.bot).2 < (Q.vtx ((D.i + 1) % Q.n)).2) ∨
      (D.bot = (D.i + 1) % Q.n ∧ (Q.vtx D.bot).2 < (Q.vtx D.i).2) := by
  have hy12 := (D.isTrap.bot_lt.trans D.isTrap.lt_top).le
  refine endpoint_lower hQ D.isTrap.hi (D.bot_lt hQ) ?_ ?_
  · rw [h]; exact D.isTrap.mem_edgeL le_rfl hy12 rfl
  · rw [D.bot_snd hQ]; exact lt_of_lt_of_le (D.isTrap.bot_lt.trans D.isTrap.lt_top) D.isTrap.topL

include hQ in
/-- The bottom vertex at the right lower corner is an end of the right edge, below the other
end. -/
theorem bot_right_lower (h : Q.vtx D.bot = ((edgeX Q D.j D.y₁, D.y₁) : Point)) :
    (D.bot = D.j ∧ (Q.vtx D.bot).2 < (Q.vtx ((D.j + 1) % Q.n)).2) ∨
      (D.bot = (D.j + 1) % Q.n ∧ (Q.vtx D.bot).2 < (Q.vtx D.j).2) := by
  have hy12 := (D.isTrap.bot_lt.trans D.isTrap.lt_top).le
  refine endpoint_lower hQ D.isTrap.hj (D.bot_lt hQ) ?_ ?_
  · rw [h]; exact D.isTrap.mem_edgeR le_rfl hy12 rfl
  · rw [D.bot_snd hQ]; exact lt_of_lt_of_le (D.isTrap.bot_lt.trans D.isTrap.lt_top) D.isTrap.topR

end

end OutGeom

end Chazelle.Core
